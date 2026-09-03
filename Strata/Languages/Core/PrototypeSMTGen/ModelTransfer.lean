/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
import all Strata.Languages.Core.PrototypeSMTGen.Construct
import all Strata.DL.SMT.DenoteTyped

/-!
# Model transfer for the interpreted-function SMT encoder

This file promotes `Construct`'s SYNTACTIC correspondence to a SEMANTIC one. `Construct` proves
`EncInv (OblProgram.ctx P) (SMTProgram.ctx block)` — the emitted SMT context matches the source
obligation context structurally (which UFs, `define-fun`s, and assertions correspond). This file
uses that structural match to construct, from a source (Lambda) model `(opInterp, fvarVal)`, an SMT
model `(mkUFInterp, mkSMTEnv)` that agrees with it VALUE-FOR-VALUE on every corresponding symbol and
assertion. Hence the emitted query is satisfiable exactly when the obligation is falsifiable, so an
SMT-unsat verdict implies the obligation is valid (`oblProgram_valid_of_smtUnsat`).

Model construction and the structural invariant are combined in `smtModel_of_lambdaModel` and the
headline soundness theorems. The file is written in `Construct` vocabulary
(`P.Φ`/`P.Ψ`/`SMTProgram.ctx`/`EncInv`/`EncodedBySyn`).

Key definitions:
  * `mkUFInterp` / `mkSMTEnv` — construct the SMT model `(ufInterp, smtEnv)` from a Lambda model
    `(opInterp, fvarVal)`. `mkUFInterp` dispatches by UF signature over the (SMT-LIB-disjoint)
    source contexts `Φ`/`Ψ` (fvar → cast `fvarVal`; fn → cast `opInterp`; else inhabited default).
    `smtEnv` is immaterial for the closed obligation (every program variable encodes as a UF
    application through `ufInterp`, not `smtEnv`), so the default env suffices at this layer.
  * `mkUFInterp_fvarCorresponds` / `_fnCorresponds` — the two by-construction correspondences
    (`FVarEnvCorresponds` / `FnEnvCorresponds`) that model transfer and `toSMTTerm_sound` consume.
  * `SMTSatAt` / `SMTCtx.checkSat` — the meaning of a `check-sat`(-assuming) query: some
    preamble-respecting model satisfies the assertions plus the query's transient literals.
  * `SMTProgram.Unsat` — `¬ checkSat` of the whole program with no transient literals.
  * `SMTProgram.checkVerdicts` — the program's output: the ordered `List Prop` of per-check
    verdicts, one `SMTCtx.checkSat` per emitted check.
  * `OblProgram.Valid` / `OblProgram.Unsat` — the source-side conclusions, mirroring `LogConseq`
    (assumptions + distincts ⟹ obligation, and its dual ⟹ ¬obligation).

Key results:
  * `mkModel_sat_obligation`, `mkModel_sat_distinct`, `mkModel_sat_preamble` — the parametric crux:
    the constructed model satisfies the encoded obligation, each encoded `distinct` group, and the
    emitted `define-fun` preamble.
  * `smtModel_of_lambdaModel` — instantiates the crux at a well-formed `P` and its emitted `prog`.
  * `mkModel_checkSat_block` — the shared block-level witness through which every soundness
    direction funnels.
  * The headline soundness theorems, matching the three encoders of `Construct`:
      - `oblProgram_valid_of_smtUnsat` (`encode`, single-check): SMT-unsat ⟹ `Valid`;
      - `oblProgram_unsat_of_smtUnsat` (`encodeUnsat`, single-check): SMT-unsat ⟹ `Unsat`;
      - `oblProgram_valid_of_verdictUnsat` / `oblProgram_unsat_of_verdictUnsat` — the same two,
        stated over the reified program output (`checkVerdicts prog = [v]`, `¬v ⟹ …`);
      - `encodeIncremental_sound` (`encodeIncremental`, two `check-sat-assuming` over one pushed
        block): `checkVerdicts prog = [v₀, v₁]` with `¬v₀ ⟹ Unsat` and `¬v₁ ⟹ Valid`.

The model's definition-consistency conditions (`FnDefs.OpConsistent` / `VarDefs.Consistent`) are
carried as hypotheses throughout this file; the whole-program layer (`Core.lean`) discharges them —
`FnDefs.OpConsistent` from the model's `Factory.InterpConsistent`, and `VarDefs.Consistent` from the
operational pinning of `.det` variables.
-/

open Core Lambda Imperative Strata.SMT Std Core.Construct
open Strata.SMT.DenoteTyped

/-- The trivial sort interpretation (every uninterpreted sort → `Unit`). `SMTSatAt` quantifies over
    all sort interpretations; since the prototype fragment is base-sorts-only, `defaultσ` is the
    concrete sort interpretation supplied as the witness when constructing a satisfying model
    (`mkModel_checkSat_block`). -/
def defaultσ : SortInterp := fun _ _ => Unit

instance : SortInterp.AllInhabited defaultσ := ⟨fun _ _ => ⟨()⟩⟩

namespace Core.ModelTransfer

/-! ## The SMT variable environment (immaterial for the closed obligation) -/

/-- The SMT variable environment. The verified obligation is CLOSED (`Δ = []`): a program
    variable is a `.fvar`, which `toSMTTerm` encodes as a UF APPLICATION through `ufInterp`,
    not a `Term.var` read from `smtEnv`. So the obligation's denotation does not depend on
    `smtEnv` (quantifier bodies extend it locally), and the default inhabited env suffices at
    this layer. -/
noncomputable def mkSMTEnv : VarEnv defaultσ SmtArrayTheory := fun v => (default : TermType.denoteTyped defaultσ SmtArrayTheory v.ty)

/-! ## `mkUFInterp` — the constructed UF interpretation

Dispatch is on the UF signature `uf`, against the source contexts:
  * if some `(name, τ) ∈ Φ` resolves to `uf` (`lookupUF ufs name = some uf`), the UF is a free
    variable — return the cast of `fvarVal ⟨name,()⟩ (τ.substTyVars …)`;
  * else if some `(name, τ) ∈ Ψ` resolves to `uf`, it is a (declared/defined) function — return
    the cast of `opInterp name (τ.substTyVars …)`;
  * else an inhabited default (unreferenced under well-formedness).

The cast in each branch is exactly `FVarEnvCorresponds`/`FnEnvCorresponds`'s cast, so the
correspondences hold definitionally on the matched branch. Resolution is well-defined because the
source names are `Nodup`, so at most one `(name, τ)` resolves to a given `uf`.
-/

/-- A default UF denotation (each `SMTTyDenote` is inhabited); the value `mkUFInterp` returns
    for a signature that resolves to no source symbol. -/
noncomputable def UFDenote'.default : (args : List TermType) → (out : TermType) → UF.denoteTyped' defaultσ SmtArrayTheory args out
  | [], out => (TermType.denoteTyped.instInhabited (σ := defaultσ) (𝒜 := SmtArrayTheory) out).default
  | _ :: rest, out => fun _ => UFDenote'.default rest out

/-- The cast carrying an fvar/op value of arrow type `τ` to `uf`'s UF denotation, given the
    resolution equalities. Factored out so `mkUFInterp` and the correspondence lemmas share
    the SAME cast (`tyDenote_arrow_eq_UFDenote'` composed with the `τ = foldr arrow` fact). -/
private theorem uf_cast_eq {τ : LMonoTy} {uf : UF}
    (hargs : baseTysToTermTypes (collectArrowTy τ).1 = some uf.args)
    (hout : baseTyToTermType (collectArrowTy τ).2 = some uf.out) :
    Lambda.TyDenote simpTcInterp simpTyVarVal τ = UF.denoteTyped defaultσ SmtArrayTheory uf := by
  have h1 : τ = List.foldr LMonoTy.arrow (collectArrowTy τ).2 (collectArrowTy τ).1 := by
    have hf := collectArrowTy_foldr τ
    obtain ⟨argTys, rty, hcol⟩ : ∃ a r, collectArrowTy τ = (a, r) := ⟨_, _, rfl⟩
    rw [hcol] at hf ⊢; exact hf
  rw [h1]; exact tyDenote_arrow_eq_UFDenote' hargs hout

/-- The decidable predicate "source entry `x` RESOLVES to UF signature `uf`": its name looks up
    to `uf` in `ufs`, and its arrow type encodes to `uf`'s argument/return sorts. This is the
    dispatch key for `mkUFInterp`; being a genuine `Bool` predicate lets the encoder select a
    real entry by `List.find?`, keeping the correspondence proofs cast-proof-irrelevant. -/
def resolvesTo (ufs : UFCtx) (uf : UF) (x : String × LMonoTy) : Bool :=
  decide (lookupUF ufs x.1 = some uf ∧
    baseTysToTermTypes (collectArrowTy x.2).1 = some uf.args ∧
    baseTyToTermType (collectArrowTy x.2).2 = some uf.out)

/-- Decode `resolvesTo` into the three resolution facts. -/
theorem resolvesTo_iff {ufs : UFCtx} {uf : UF} {x : String × LMonoTy} :
    resolvesTo ufs uf x = true ↔
      lookupUF ufs x.1 = some uf ∧
      baseTysToTermTypes (collectArrowTy x.2).1 = some uf.args ∧
      baseTyToTermType (collectArrowTy x.2).2 = some uf.out := by
  simp only [resolvesTo, decide_eq_true_eq]

/-- **Construct `ufInterp`.** Dispatch by `List.find?` on the resolution predicate: the first
    `Φ`-entry resolving to `uf` gives the `fvarVal` cast; else the first such `Ψ`-entry gives the
    `opInterp` cast; else an inhabited default. The found entry `x` is a genuine `match`-bound
    local, with resolution facts from `List.find?_some`. -/
noncomputable def mkUFInterp
    (Φ : FVarCtx) (Ψ : FnCtx) (ufs : UFCtx)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) : UFInterp defaultσ SmtArrayTheory :=
  fun uf =>
    match hΦ : Φ.find? (resolvesTo ufs uf) with
    | some x =>
        have hx := resolvesTo_iff.mp (List.find?_some hΦ)
        cast (uf_cast_eq hx.2.1 hx.2.2) (fvarVal ⟨x.1, ()⟩ (x.2.substTyVars simpTyVarVal))
    | none =>
        match hΨ : Ψ.find? (resolvesTo ufs uf) with
        | some x =>
            have hx := resolvesTo_iff.mp (List.find?_some hΨ)
            cast (uf_cast_eq hx.2.1 hx.2.2) (opInterp x.1 (x.2.substTyVars simpTyVarVal))
        | none => UFDenote'.default uf.args uf.out

/-! ## Correspondence by construction -/

/-- Key-uniqueness: in a context with `Nodup` names, two entries sharing a name are equal.
    This is what identifies `mkUFInterp`'s `find?`-selected entry with the correspondence's
    `lookupUF`-resolved entry. -/
private theorem entry_unique {Γ : List (String × LMonoTy)} (hnd : (Γ.map (·.1)).Nodup)
    {a b : String × LMonoTy} (ha : a ∈ Γ) (hb : b ∈ Γ) (hkey : a.1 = b.1) : a = b := by
  induction Γ with
  | nil => simp at ha
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (hkey ▸ List.mem_map_of_mem (f := (·.1)) hb) hnd.1
    · exact absurd (hkey.symm ▸ List.mem_map_of_mem (f := (·.1)) ha) hnd.1
    · exact ih hnd.2 ha hb

/-- A `find?` that has a satisfying member succeeds. -/
private theorem find?_isSome_of_mem {α} {l : List α} {p : α → Bool} {a : α}
    (ha : a ∈ l) (hpa : p a = true) : (l.find? p).isSome := by
  rcases h : l.find? p with _ | b
  · exact absurd hpa (by have := List.find?_eq_none.mp h a ha; simp [this])
  · rfl

/-- **`mkUFInterp` reduces on the fvar branch.** When `(name, τ) ∈ Φ` resolves to `uf` (with
    `Φ`-names `Nodup`), `mkUFInterp` returns the cast of `fvarVal ⟨name,()⟩ …`. -/
private theorem mkUFInterp_fvar_eq
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (hnd : (Φ.map (·.1)).Nodup)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {name : String} {τ : LMonoTy} {uf : UF} (hmem : (name, τ) ∈ Φ)
    (hlk : lookupUF ufs name = some uf)
    (hargs : baseTysToTermTypes (collectArrowTy τ).1 = some uf.args)
    (hout : baseTyToTermType (collectArrowTy τ).2 = some uf.out)
    (hcast : Lambda.TyDenote simpTcInterp simpTyVarVal τ = UF.denoteTyped defaultσ SmtArrayTheory uf) :
    mkUFInterp Φ Ψ ufs opInterp fvarVal uf
      = cast hcast (fvarVal ⟨name, ()⟩ (τ.substTyVars simpTyVarVal)) := by
  -- `(name, τ)` satisfies the resolution predicate, so the `Φ`-`find?` succeeds
  have hres : resolvesTo ufs uf (name, τ) = true := resolvesTo_iff.mpr ⟨hlk, hargs, hout⟩
  have hsome := find?_isSome_of_mem hmem hres
  unfold mkUFInterp
  split
  · -- `some x'`: the selected entry resolves to `uf`, so `= (name, τ)` by nodup ⇒ cast-irrelevance
    rename_i x' hx'
    have hxres := resolvesTo_iff.mp (List.find?_some hx')
    have hxname : x'.1 = name := by
      have h1 := lookupUF_id hxres.1; have h2 := lookupUF_id hlk; rw [h1] at h2; exact h2
    have hxeq : x' = (name, τ) := entry_unique hnd (List.mem_of_find?_eq_some hx') hmem hxname
    subst hxeq; rfl
  · -- `none`: contradicts `find?`-succeeds
    rename_i hnone; rw [hnone] at hsome; simp at hsome

/-- **fvar correspondence, by construction.** For every `(name, τ) ∈ Φ` (with `Φ`-names
    `Nodup`), `mkUFInterp` agrees with `fvarVal` under the `FVarEnvCorresponds` cast. -/
theorem mkUFInterp_fvarCorresponds
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (huwf : FNameCtxWF Φ ufs)
    (hnd : (Φ.map (·.1)).Nodup)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) :
    FVarEnvCorresponds huwf fvarVal (mkUFInterp Φ Ψ ufs opInterp fvarVal) := by
  intro name τ hmem
  have hlk : lookupUF ufs name = some ((lookupUF ufs name).get (huwf.fvar_resolves name τ hmem)) :=
    (Option.some_get _).symm
  -- `FVarEnvCorresponds` reduces to `cast … (fvarVal …) = mkUFInterp … uf`; `mkUFInterp_fvar_eq`
  -- rewrites the RHS to the SAME cast (proof-irrelevant), closing by reflexivity.
  exact (mkUFInterp_fvar_eq hnd opInterp fvarVal hmem hlk
    (huwf.args_eq name τ _ hmem hlk) (huwf.out_eq name τ _ hmem hlk) _).symm

/-- **`mkUFInterp` reduces on the fn branch.** When `(name, τ) ∈ Ψ` resolves to `uf`, and no
    `Φ`-entry shares `name` (joint Φ/Ψ-name disjointness, which SMT-LIB requires), `mkUFInterp`
    falls through the `Φ`-`find?` to the `Ψ`-`find?` and returns the cast of `opInterp name …`. -/
private theorem mkUFInterp_fn_eq
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (hndΨ : (Ψ.map (·.1)).Nodup)
    (hdisj : ∀ x ∈ Φ, x.1 ∉ Ψ.map (·.1))
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {name : String} {τ : LMonoTy} {uf : UF} (hmem : (name, τ) ∈ Ψ)
    (hlk : lookupUF ufs name = some uf)
    (hargs : baseTysToTermTypes (collectArrowTy τ).1 = some uf.args)
    (hout : baseTyToTermType (collectArrowTy τ).2 = some uf.out)
    (hcast : Lambda.TyDenote simpTcInterp simpTyVarVal τ = UF.denoteTyped defaultσ SmtArrayTheory uf) :
    mkUFInterp Φ Ψ ufs opInterp fvarVal uf
      = cast hcast (opInterp name (τ.substTyVars simpTyVarVal)) := by
  -- the `Φ`-`find?` returns `none`: no `Φ`-entry resolves to `uf` (would name `uf.id = name ∈ Ψ`)
  have hΦnone : Φ.find? (resolvesTo ufs uf) = none := by
    rw [List.find?_eq_none]
    intro x hxΦ hxres
    have hxname : x.1 = name := by
      have h1 := lookupUF_id (resolvesTo_iff.mp hxres).1
      have h2 := lookupUF_id hlk; rw [h1] at h2; exact h2
    exact hdisj x hxΦ (hxname ▸ List.mem_map_of_mem (f := (·.1)) hmem)
  -- the `Ψ`-`find?` succeeds, witnessed by `(name, τ)`
  have hres : resolvesTo ufs uf (name, τ) = true := resolvesTo_iff.mpr ⟨hlk, hargs, hout⟩
  have hsome := find?_isSome_of_mem hmem hres
  unfold mkUFInterp
  split
  · -- outer `Φ`-`find? = some`: impossible, `Φ`-`find?` is `none`
    rename_i x' hx'; rw [hΦnone] at hx'; simp at hx'
  · -- `Φ`-`find? = none`; now split the `Ψ`-`find?`
    split
    · rename_i x' hx'
      have hxres := resolvesTo_iff.mp (List.find?_some hx')
      have hxname : x'.1 = name := by
        have h1 := lookupUF_id hxres.1; have h2 := lookupUF_id hlk; rw [h1] at h2; exact h2
      have hxeq : x' = (name, τ) := entry_unique hndΨ (List.mem_of_find?_eq_some hx') hmem hxname
      subst hxeq; rfl
    · rename_i hnone; rw [hnone] at hsome; simp at hsome

/-- **fn correspondence, by construction.** For every `(name, τ) ∈ Ψ` (with `Ψ`-names `Nodup`
    and Φ/Ψ names disjoint), `mkUFInterp` agrees with `opInterp` under the `FnEnvCorresponds`
    cast. -/
theorem mkUFInterp_fnCorresponds
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (hψwf : FNameCtxWF Ψ ufs)
    (hndΨ : (Ψ.map (·.1)).Nodup) (hdisj : ∀ x ∈ Φ, x.1 ∉ Ψ.map (·.1))
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) :
    FnEnvCorresponds hψwf opInterp (mkUFInterp Φ Ψ ufs opInterp fvarVal) := by
  intro name τ hmem
  have hlk : lookupUF ufs name = some ((lookupUF ufs name).get (hψwf.fvar_resolves name τ hmem)) :=
    (Option.some_get _).symm
  exact (mkUFInterp_fn_eq hndΨ hdisj opInterp fvarVal hmem hlk
    (hψwf.args_eq name τ _ hmem hlk) (hψwf.out_eq name τ _ hmem hlk) _).symm

/-! ## The crux

A Lambda model transfers to a corresponding SMT model that satisfies the encoded obligation, each
encoded `distinct` group, and the emitted `define-fun` preamble. Stated parametrically over
`(Φ, Ψ, ufs, fs)` with the correspondence hypotheses the two `mkUFInterp_*Corresponds` lemmas
discharge (name-nodup + Φ/Ψ disjointness), independent of the fact that the contexts came from a
program. Three building blocks:
  * `mkModel_sat_obligation` — the constructed `(mkUFInterp, smtEnv)` satisfies the encoded
    obligation term, via `toSMTTerm_sound` and the by-construction correspondences (at bool, the
    transfer cast is trivial). This is the pure model transfer.
  * `mkModel_sat_distinct` — the constructed model satisfies an encoded `distinct` group, lifting
    source pairwise-distinctness (`DistinctSat`) across `toSMTTerm_sound` and cast injectivity.
    Reused for the assumption-side assertions too.
  * `mkModel_sat_preamble` — the constructed model satisfies `IFs.UFConsistent fs` (the emitted
    `define-fun` contract), discharging each emitted `f` per-function via its `EncodedBySyn` witness
    and the bridges `UFConsistent_of_OpConsistent'` (op-side `fnDef`s) /
    `UFConsistent_of_VarConsistent'` (fvar-side `varDef`s). Definition-consistency
    (`FnDefs.OpConsistent`) is taken as a hypothesis here; the whole-program layer (`Core.lean`)
    discharges it from the model's `Factory.InterpConsistent`.
-/

/-- An SMT model `(ufInterp, smtEnv)` SATISFIES a bool-typed term `tm` (type-checking against
    `ufs`) when its denotation is `true` — the SMT analog of `Lambda.Interp.satisfies`. -/
def SMTSat {ufs : UFCtx} {σ : SortInterp} {𝒜 : ArrayTheory}
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜)
    (divByZero modByZero : Int → Int)
    (tm : Term) (htc : Term.typeCheck ⟨[], ufs, []⟩ tm = .ok .bool) : Prop :=
  Term.denoteTyped ufInterp smtEnv divByZero modByZero tm .bool htc = true

/-- **Source-side satisfaction of a distinctness group.** The group's elements, at their shared
    base type `τ`, denote (under `simpDenote`) to PAIRWISE-DISTINCT values. LExpr has no `distinct`
    operator, so this is stated directly over the elements' denotations (the SMT side's
    `Pairwise (·≠·)`). -/
noncomputable def DistinctSat {Φ : FVarCtx} {Ψ : FnCtx}
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (es : List Expression.Expr) (τ : LMonoTy)
    (hall : ∀ e ∈ es, LExpr.HasSimpType Φ Ψ [] e τ) : Prop :=
  (es.attach.map (fun x => simpDenote opInterp fvarVal .nil x.1 τ
    (HasSimpType_implies_HasTypeA (hall x.1 x.2)))).Pairwise (· ≠ ·)

/-- **Obligation-denotation transfer (equation form).** The constructed model's SMT denotation of
    the encoded term `tm` EQUALS the Lambda denotation of the closed bool source `e` — at `τ = bool`
    the transfer cast is the identity `Bool = Bool`. This is `toSMTTerm_sound` specialized to bool,
    with the correspondences discharged by construction. Both the positive (`mkModel_sat_obligation`)
    and refuting (contrapositive) directions read off this single equation. -/
theorem mkModel_denote_obligation
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx}
    (hndΦ : (Φ.map (·.1)).Nodup) (hndΨ : (Ψ.map (·.1)).Nodup)
    (hdisj : ∀ x ∈ Φ, x.1 ∉ Ψ.map (·.1))
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {e : Expression.Expr} (he : LExpr.HasSimpType Φ Ψ [] e (.tcons "bool" []))
    -- ── SMT (target) side ──
    {ufs : UFCtx} (hufwf : UFCtxWF ufs)
    {tm : Term} (htc : Term.typeCheck ⟨[], ufs, []⟩ tm = .ok .bool)
    -- ── correspondence (source ↔ target) ──
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs)
    (h_ok : toSMTTerm [] e = .ok tm) :
    (Term.denoteTyped (mkUFInterp Φ Ψ ufs opInterp fvarVal) mkSMTEnv divByZero modByZero tm .bool htc : Bool)
      = (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
          (HasSimpType_implies_HasTypeA he) : Bool) := by
  -- correspondences by construction
  have hfenv := mkUFInterp_fvarCorresponds (Ψ := Ψ) huwf hndΦ opInterp fvarVal
  have hopenv := mkUFInterp_fnCorresponds (Φ := Φ) hψwf hndΨ hdisj opInterp fvarVal
  -- empty bvar context corresponds vacuously
  have hbwf : BVarCtxWF [] [] := ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  have hbenv : BVarEnvCorresponds hbwf (.nil) mkSMTEnv := by
    intro i τ' hbase' hlook; exact absurd hlook (by simp)
  -- `toSMTTerm_sound` at `τ = bool`: `cast (…) (simpDenote … e) = Term.denoteTyped … tm`
  have hsound := toSMTTerm_sound he (HasSimpType_implies_HasTypeA he) .bool
    opInterp hop fvarVal .nil htc (mkUFInterp Φ Ψ ufs opInterp fvarVal) mkSMTEnv hufwf
    h_ok rfl huwf hψwf hbwf hfenv hopenv hbenv
  -- at bool the transfer cast is the identity
  rw [← hsound]; rfl

/-- **Obligation-satisfaction transfer** (positive direction): if the source obligation holds, the
    constructed model satisfies the encoded term. A corollary of `mkModel_denote_obligation`. -/
theorem mkModel_sat_obligation
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx}
    (hndΦ : (Φ.map (·.1)).Nodup) (hndΨ : (Ψ.map (·.1)).Nodup)
    (hdisj : ∀ x ∈ Φ, x.1 ∉ Ψ.map (·.1))
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {e : Expression.Expr} (he : LExpr.HasSimpType Φ Ψ [] e (.tcons "bool" []))
    (hsat : (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
              (HasSimpType_implies_HasTypeA he) : Bool) = true)
    -- ── SMT (target) side ──
    {ufs : UFCtx} (hufwf : UFCtxWF ufs)
    {tm : Term} (htc : Term.typeCheck ⟨[], ufs, []⟩ tm = .ok .bool)
    -- ── correspondence (source ↔ target) ──
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs)
    (h_ok : toSMTTerm [] e = .ok tm) :
    SMTSat (ufs := ufs) (mkUFInterp Φ Ψ ufs opInterp fvarVal) mkSMTEnv divByZero modByZero tm htc := by
  unfold SMTSat
  rw [mkModel_denote_obligation hndΦ hndΨ hdisj opInterp hop fvarVal he hufwf htc huwf hψwf h_ok,
      hsat]

/- ── Keystones for the distinct transfer ──
   The SMT `distinct` denotation reduces to `decide (Pairwise (·≠·) L) = true`, where `L` is the
   flattened list of the type-checked args' denotations. These two lemmas characterize `L`: its
   length is the arg count, and its `i`-th element is `Term.denoteTyped args[i]`. Both fall out of
   the DEFINITIONAL reduction `Term.denoteTypedArgs (t::ts) = .cons (denote t) (denote ts)` (an
   `rfl`) and the `hlistReplicateToList` cons — no `simp` needed on their internal `match`es. -/

/-- The flattened denoted-args list has length = arg count. -/
theorem hlist_len {α} {f : α → Type} {a : α} : ∀ (n : Nat) (hl : HList f (List.replicate n a)),
    (hlistReplicateToList n hl).length = n := by
  intro n; induction n with
  | zero => intro hl; rfl
  | succ m ih => intro hl; match hl with | .cons x xs => simp [hlistReplicateToList, ih]

/-- The tail of a `replicate`-shaped `typeCheckArgs` also type-checks (peels the head). -/
private theorem tcArgs_rest {ufs : UFCtx} {Γ : List TermVar} {t : Term} {ts : List Term}
    {ty : TermType}
    (htc : Term.typeCheckArgs ⟨[], ufs, Γ⟩ (t::ts) (ty :: List.replicate ts.length ty) = true) :
    Term.typeCheckArgs ⟨[], ufs, Γ⟩ ts (List.replicate ts.length ty) = true := by
  simp only [Term.typeCheckArgs] at htc
  split at htc
  · rename_i ty' he; simp only [Bool.and_eq_true] at htc; exact htc.2
  · exact absurd htc (by simp)

/-- The `i`-th element of the flattened denoted-args list IS `Term.denoteTyped args[i]` (bracket
    form; downstream consumers bridge to `.get` via `List.get_eq_getElem` as needed). -/
theorem hlist_getElem {ufs : UFCtx} {Γ : List TermVar} (ufInterp : UFInterp defaultσ SmtArrayTheory) (env : VarEnv defaultσ SmtArrayTheory)
    {divByZero modByZero : Int → Int}
    (ty : TermType) : ∀ (args : List Term)
    (htc : Term.typeCheckArgs ⟨[], ufs, Γ⟩ args (List.replicate args.length ty) = true)
    (i : Nat) (hi : i < args.length) (htci : Term.typeCheck ⟨[], ufs, Γ⟩ args[i] = .ok ty),
    (hlistReplicateToList args.length
      (Term.denoteTypedArgs ufInterp env divByZero modByZero args (List.replicate args.length ty) htc))[i]'(by rw [hlist_len]; exact hi)
    = Term.denoteTyped ufInterp env divByZero modByZero args[i] ty htci := by
  intro args
  induction args with
  | nil => intro htc i hi htci; simp at hi
  | cons t ts ih =>
    intro htc i hi htci
    match i, hi with
    | 0, _ => rfl
    | j+1, hj =>
      have hjlt : j < ts.length := by simpa using hj
      have htcj : Term.typeCheck ⟨[], ufs, Γ⟩ ts[j] = .ok ty := htci
      have htcrest := tcArgs_rest htc
      have hstep : (hlistReplicateToList (t::ts).length
          (Term.denoteTypedArgs ufInterp env divByZero modByZero (t::ts) (List.replicate (t::ts).length ty) htc))[j+1]'(by rw [hlist_len]; exact hj)
        = (hlistReplicateToList ts.length
            (Term.denoteTypedArgs ufInterp env divByZero modByZero ts (List.replicate ts.length ty) htcrest))[j]'(by rw [hlist_len]; exact hjlt) := rfl
      rw [hstep]; exact ih htcrest j hjlt htcj

/-- Encoding preserves length: `es.mapM toSMTTerm = .ok ts ⟹ ts.length = es.length`. -/
theorem mapM_toSMT_len : ∀ {es : List Expression.Expr} {ts : List Term}
    (_ : es.mapM (toSMTTerm []) = .ok ts), ts.length = es.length := by
  intro es
  induction es with
  | nil => intro ts h; simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | cons e es ih =>
    intro ts h
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases het : toSMTTerm [] e with
    | error _ => rw [het] at h; simp at h
    | ok t =>
      rw [het] at h; simp only at h
      cases hrest : es.mapM (toSMTTerm []) with
      | error _ => rw [hrest] at h; simp at h
      | ok ts' => rw [hrest] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp [ih hrest]

/-- Encoding aligns per index: `ts.get i = toSMTTerm (es.get i)`. -/
theorem mapM_toSMT_getElem : ∀ {es : List Expression.Expr} {ts : List Term}
    (_ : es.mapM (toSMTTerm []) = .ok ts) (i : Nat) (hi : i < es.length) (hit : i < ts.length),
    toSMTTerm [] (es.get ⟨i, hi⟩) = .ok (ts.get ⟨i, hit⟩) := by
  intro es
  induction es with
  | nil => intro ts h i hi hit; simp at hi
  | cons e es ih =>
    intro ts h i hi hit
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases het : toSMTTerm [] e with
    | error _ => rw [het] at h; simp at h
    | ok t =>
      rw [het] at h; simp only at h
      cases hrest : es.mapM (toSMTTerm []) with
      | error _ => rw [hrest] at h; simp at h
      | ok ts' =>
        rw [hrest] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        match i, hi, hit with
        | 0, _, _ => simpa using het
        | j+1, hj, hjt => simpa using ih hrest j (by simpa using hj) (by simpa using hjt)

/-- **Distinctness-satisfaction transfer.** A distinctness group `es` (elements at shared base
    type `τ`) whose source denotations are pairwise-distinct (`DistinctSat`) transfers to the SMT
    model satisfying the encoded `distinct (map toSMTTerm es)` term. The SMT `distinct` denotes as
    `decide (Pairwise (·≠·) [Term.denoteTyped t₁, …])`; each `Term.denoteTyped tᵢ = cast (simpDenote eᵢ)`
    by `toSMTTerm_sound`, and `cast` is injective, so source pairwise-distinctness lifts to the
    SMT side. -/
theorem mkModel_sat_distinct
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx}
    (hndΦ : (Φ.map (·.1)).Nodup) (hndΨ : (Ψ.map (·.1)).Nodup)
    (hdisj : ∀ x ∈ Φ, x.1 ∉ Ψ.map (·.1))
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {es : List Expression.Expr} {τ : LMonoTy} (hbase : LExpr.MonoTyIsBase τ)
    (hall : ∀ e ∈ es, LExpr.HasSimpType Φ Ψ [] e τ)
    (hsat : DistinctSat (Φ := Φ) (Ψ := Ψ) opInterp fvarVal es τ hall)
    -- ── SMT (target) side ──
    {ufs : UFCtx} (hufwf : UFCtxWF ufs)
    {ts : List Term} (htc : Term.typeCheck ⟨[], ufs, []⟩ (.app (.core .distinct) ts .bool) = .ok .bool)
    -- ── correspondence (source ↔ target) ──
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs)
    (h_ok : es.mapM (toSMTTerm []) = .ok ts) :
    SMTSat (ufs := ufs) (mkUFInterp Φ Ψ ufs opInterp fvarVal) mkSMTEnv divByZero modByZero
      (.app (.core .distinct) ts .bool) htc := by
  -- `τ` encodes to some SMT sort `smtτ`
  obtain ⟨smtτ, hτ⟩ := MonoTyIsBase_baseTyToTermType hbase
  -- lengths align; the constructed model's correspondences (by construction)
  have htlen : ts.length = es.length := mapM_toSMT_len h_ok
  have hfenv := mkUFInterp_fvarCorresponds (Ψ := Ψ) huwf hndΦ opInterp fvarVal
  have hopenv := mkUFInterp_fnCorresponds (Φ := Φ) hψwf hndΨ hdisj opInterp fvarVal
  have hbwf : BVarCtxWF [] [] := ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  have hbenv : BVarEnvCorresponds hbwf (.nil) mkSMTEnv := by
    intro i τ' hbase' hlook; exact absurd hlook (by simp)
  -- every `ts[i]` type-checks to `smtτ` at the block `ufs` (toSMTTerm_typeChecks per element)
  have htci : ∀ i (hit : i < ts.length),
      Term.typeCheck ⟨[], ufs, []⟩ ts[i] = .ok smtτ := by
    intro i hit
    have hie : i < es.length := htlen ▸ hit
    exact toSMTTerm_typeChecks (hall _ (es.get_mem ⟨i, hie⟩)) hufwf
      (mapM_toSMT_getElem h_ok i hie hit) hτ huwf hψwf hbwf
  -- each `ts[i]` denotes to `cast (simpDenote es[i])` (toSMTTerm_sound per element)
  have hsound : ∀ i (hit : i < ts.length) (hie : i < es.length),
      Term.denoteTyped (mkUFInterp Φ Ψ ufs opInterp fvarVal) mkSMTEnv divByZero modByZero ts[i] smtτ (htci i hit)
      = cast (tyDenote_eq_smtTyDenote hbase hτ)
          (simpDenote opInterp fvarVal .nil (es.get ⟨i, hie⟩) τ
            (HasSimpType_implies_HasTypeA (hall _ (es.get_mem ⟨i, hie⟩)))) := by
    intro i hit hie
    exact (toSMTTerm_sound (hall _ (es.get_mem ⟨i, hie⟩))
      (HasSimpType_implies_HasTypeA (hall _ (es.get_mem ⟨i, hie⟩))) hbase
      opInterp hop fvarVal .nil (htci i hit) (mkUFInterp Φ Ψ ufs opInterp fvarVal) mkSMTEnv hufwf
      (mapM_toSMT_getElem h_ok i hie hit) hτ huwf hψwf hbwf hfenv hopenv hbenv).symm
  -- `ts` must be `t1::t2::rest` (≥2 args), so the distinct denotation reduces
  obtain ⟨t1, t2, restts, htseq⟩ : ∃ a b r, ts = a :: b :: r := by
    match ts, htc with
    | [], htc => simp [Term.typeCheck] at htc
    | [_], htc => simp [Term.typeCheck] at htc
    | a :: b :: r, _ => exact ⟨a, b, r, rfl⟩
  subst htseq
  unfold SMTSat Term.denoteTyped
  rcases htdi : Term.typeCheck_distinct_inv htc with ⟨ty, ht1, hargs, heq⟩
  dsimp only
  rw [cast_eq]
  -- `ty` (the shared arg sort from `Term.typeCheck_distinct_inv`) is `smtτ` (the encoding of `τ`)
  have htyeq : ty = smtτ := by
    have h0 := htci 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [ht1] at h0; exact Except.ok.inj h0
  subst htyeq
  -- prove the `Pairwise` (·≠·) over the flattened denoted-args list (strip the classical `decide`)
  simp only [decide_eq_true_iff]
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [hlist_len] at hi hj
  -- the full-list arg type-check (head `ht1` + tail `hargs`); `Term.denoteTypedArgs` is proof-irrelevant
  have hfullargs : Term.typeCheckArgs ⟨[], ufs, []⟩ (t1::t2::restts)
      (List.replicate (t1::t2::restts).length ty) = true := by
    show Term.typeCheckArgs ⟨[], ufs, []⟩ (t1::t2::restts) (ty :: List.replicate (t2::restts).length ty) = true
    simp only [Term.typeCheckArgs, ht1, hargs, BEq.beq, decide_eq_true_eq, Bool.and_true]
  -- entry `k` of the flattened list is `Term.denoteTyped (t1::t2::restts)[k] = cast (simpDenote es[k])`
  rw [hlist_getElem (mkUFInterp Φ Ψ ufs opInterp fvarVal) mkSMTEnv ty (t1::t2::restts) hfullargs
        i hi (htci i hi),
      hlist_getElem (mkUFInterp Φ Ψ ufs opInterp fvarVal) mkSMTEnv ty (t1::t2::restts) hfullargs
        j hj (htci j hj)]
  -- both entries are now `Term.denoteTyped (t1::t2::restts)[·]`; apply `hsound` (same `[·]` LHS)
  rw [hsound i hi (htlen ▸ hi), hsound j hj (htlen ▸ hj)]
  -- `hsat`'s source pairwise-distinctness, read at indices `i,j` (via `getElem_map`/`_attach`)
  have hpw := hsat
  rw [DistinctSat, List.pairwise_iff_getElem] at hpw
  have hij' := hpw i j
    (by simp only [List.length_map, List.length_attach]; exact htlen ▸ hi)
    (by simp only [List.length_map, List.length_attach]; exact htlen ▸ hj) hij
  simp only [List.getElem_map, List.getElem_attach] at hij'
  -- the goal is `cast C vi ≠ cast C vj` with `vi ≠ vj` (`hij'`); cast is injective
  revert hij'
  generalize simpDenote opInterp fvarVal .nil (es.get ⟨i, htlen ▸ hi⟩) τ
      (HasSimpType_implies_HasTypeA (hall _ (es.get_mem ⟨i, htlen ▸ hi⟩))) = vi
  generalize simpDenote opInterp fvarVal .nil (es.get ⟨j, htlen ▸ hj⟩) τ
      (HasSimpType_implies_HasTypeA (hall _ (es.get_mem ⟨j, htlen ▸ hj⟩))) = vj
  intro hij' hcontra
  -- goal `cast C vi = cast C vj` with `C : TyDenote τ = TermType.denoteTyped defaultσ SmtArrayTheory ty`; make `C`'s RHS a
  -- variable so `subst` collapses the cast to the identity, then `hij'` closes.
  revert hcontra
  generalize tyDenote_eq_smtTyDenote (σ := defaultσ) hbase hτ = C
  generalize TermType.denoteTyped defaultσ SmtArrayTheory ty = B at C
  subst C
  simp only [cast_eq]
  exact hij'

/- ── Preamble join (per-`f`, mixed `fs`) ──
   `fs` mixes op-side (`fnDef`) and fvar-side (`varDef`) IFs, so the preamble is discharged
   per-`f` by case-splitting `EncInv.fsCorr`'s disjunction. Each branch reconstructs that IF's
   own `IF.UFConsistent` from: the source consistency (2) for its definition, and the model
   correspondence (1) at its signature. The delicate step is that the resolved UF `lookupUF …`
   equals the IF's own `toUF` (`resolved_uf_eq` op-side / `resolved_uf_eq_var` fvar-side), which
   turns the correspondence's RHS into the exact `hcorr` the per-function bridge wants. -/

/-- The UF resolved for a `fnDef`'s signature IS the emitted IF's `toUF`. -/
private theorem resolved_uf_eq {Ψ : FnCtx} {ufs : UFCtx} (hψwf : FNameCtxWF Ψ ufs)
    {d : FnDef} {f : IF} (hsyn : FnDef.EncodedBySyn d f) (hdmem : d.sig ∈ Ψ) :
    (lookupUF ufs d.name).get (hψwf.fvar_resolves d.name d.sig.2 hdmem)
      = ⟨d.name, f.args.map (·.ty), f.out⟩ := by
  have hlk : lookupUF ufs d.name =
      some ((lookupUF ufs d.name).get (hψwf.fvar_resolves d.name d.sig.2 hdmem)) :=
    (Option.some_get _).symm
  have hcol : collectArrowTy d.sig.2 = (d.argTys, d.retTy) := by
    simp only [FnDef.sig]; exact collectArrowTy_foldr_base (baseTyToTermType_isBase hsyn.rty)
  generalize huf : (lookupUF ufs d.name).get (hψwf.fvar_resolves d.name d.sig.2 hdmem) = uf at hlk ⊢
  have hid := lookupUF_id hlk
  have hargs := hψwf.args_eq d.name d.sig.2 uf hdmem hlk
  have hout := hψwf.out_eq d.name d.sig.2 uf hdmem hlk
  rw [hcol] at hargs hout; simp only at hargs hout
  have hfargs : baseTysToTermTypes d.argTys = some (f.args.map (·.ty)) := hsyn.bwf.baseTysToTermTypes_eq
  obtain ⟨id, args, out⟩ := uf
  simp only at hid hargs hout
  rw [hfargs] at hargs; rw [hsyn.rty] at hout
  simp only [UF.mk.injEq]
  exact ⟨hid, (Option.some.inj hargs).symm, (Option.some.inj hout).symm⟩

/-- The UF resolved for a `varDef`'s (nullary) declared type IS the emitted IF's `toUF`. -/
private theorem resolved_uf_eq_var {Φ : FVarCtx} {ufs : UFCtx} (huwf : FNameCtxWF Φ ufs)
    {v : VarDef} {f : IF} (hsyn : VarDef.EncodedBySyn v f) (hvmem : (v.name, v.ty) ∈ Φ) :
    (lookupUF ufs v.name).get (huwf.fvar_resolves v.name v.ty hvmem)
      = ⟨v.name, f.args.map (·.ty), f.out⟩ := by
  have hlk : lookupUF ufs v.name =
      some ((lookupUF ufs v.name).get (huwf.fvar_resolves v.name v.ty hvmem)) :=
    (Option.some_get _).symm
  -- `v.ty` is base ⇒ `collectArrowTy v.ty = ([], v.ty)`; and `f.args = []`
  have hcol : collectArrowTy v.ty = ([], v.ty) := by
    have hbase := baseTyToTermType_isBase hsyn.rty
    generalize v.ty = τ at *; cases hbase <;> rfl
  generalize huf : (lookupUF ufs v.name).get (huwf.fvar_resolves v.name v.ty hvmem) = uf at hlk ⊢
  have hid := lookupUF_id hlk
  have hargs := huwf.args_eq v.name v.ty uf hvmem hlk
  have hout := huwf.out_eq v.name v.ty uf hvmem hlk
  rw [hcol] at hargs hout; simp only [baseTysToTermTypes] at hargs hout
  obtain ⟨id, args, out⟩ := uf
  simp only at hid hargs hout
  rw [hsyn.rty] at hout
  simp only [UF.mk.injEq, hsyn.args_nil, List.map_nil]
  exact ⟨hid, (Option.some.inj hargs).symm, (Option.some.inj hout).symm⟩

/-- **Preamble-satisfaction transfer (mixed `fs`).** The constructed model satisfies the emitted
    `define-fun` preamble `IFs.UFConsistent fs`. For each `f ∈ fs`, `hfs` (the `EncInv.fsCorr`
    disjunction) says `f` encodes some `fnDef d ∈ defs` (op-side) OR some `varDef v ∈ varDefs`
    (fvar-side); the corresponding per-function bridge (`UFConsistent_of_OpConsistent'` /
    `UFConsistent_of_VarConsistent'`) discharges `IF.UFConsistent f`, its `hcorr` reconstructed
    from the by-construction correspondence at `f`'s signature (`resolved_uf_eq(_var)`).
    Consistency (2) is supplied per side (`FnDefs.OpConsistent` / `VarDefs.Consistent`). -/
theorem mkModel_sat_preamble
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} (defs : List FnDef) (varDefs : List VarDef)
    (hndΦ : (Φ.map (·.1)).Nodup) (hndΨ : (Ψ.map (·.1)).Nodup)
    (hdisj : ∀ x ∈ Φ, x.1 ∉ Ψ.map (·.1))
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    -- op-side: each `fnDef` is `WFIn` and its signature `d.sig ∈ Ψ`; consistency (2)
    (hdwf : ∀ d ∈ defs, d.WFIn Φ Ψ) (hdsig : ∀ d ∈ defs, d.sig ∈ Ψ)
    (hopcons : FnDefs.OpConsistent opInterp fvarVal defs (fun d hd => (hdwf d hd).hasTypeA))
    -- fvar-side: each `varDef` has base type, `(name,ty) ∈ Φ`, a body `WFIn` at the FULL
    -- context (its `Ψ` callees discharged by `hopenv`, generalized var bridge), and consistency (2)
    (hvΦ : ∀ v ∈ varDefs, (v.name, v.ty) ∈ Φ)
    (hvbase : ∀ v ∈ varDefs, LExpr.MonoTyIsBase v.ty)
    (hvbody : ∀ v ∈ varDefs, LExpr.HasSimpType Φ Ψ [] v.body v.ty)
    (hvcons : ∀ v (hv : v ∈ varDefs),
      v.Consistent opInterp fvarVal (HasSimpType_implies_HasTypeA (hvbody v hv)))
    -- ── SMT (target) side ──
    {ufs : UFCtx} (hufwf : UFCtxWF ufs)
    (fs : IFs)
    (htc : ∀ f ∈ fs, Term.typeCheck ⟨[], ufs, f.args⟩ f.body = .ok f.out)
    -- ── correspondence (source ↔ target) ──
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs)
    (hfs : ∀ f ∈ fs,
      (∃ d ∈ defs, FnDef.EncodedBySyn d f) ∨ (∃ v ∈ varDefs, VarDef.EncodedBySyn v f)) :
    IFs.UFConsistent fs htc (mkUFInterp Φ Ψ ufs opInterp fvarVal) divByZero modByZero := by
  have hfenv := mkUFInterp_fvarCorresponds (Ψ := Ψ) huwf hndΦ opInterp fvarVal
  have hopenv := mkUFInterp_fnCorresponds (Φ := Φ) hψwf hndΨ hdisj opInterp fvarVal
  intro f hf
  rcases hfs f hf with ⟨d, hd, hsyn⟩ | ⟨v, hv, hsyn⟩
  · -- op-side: `f = ⟨d.name, fargs, fout, fbody⟩`; reconstruct its own `corr` via `mkUFInterp_fn_eq`
    obtain ⟨fid, fargs, fout, fbody⟩ := f
    obtain ⟨hfid, hfbridge, hfrty, hfbwf⟩ := hsyn
    simp only at hfid hfbridge hfrty hfbwf; subst hfid
    -- `d.sig = (d.name, foldr arrow d.retTy d.argTys)` is in `Ψ`
    have hmem : (d.name, List.foldr LMonoTy.arrow d.retTy d.argTys) ∈ Ψ := by
      have := hdsig d hd; simpa only [FnDef.sig] using this
    have hcol : collectArrowTy (List.foldr LMonoTy.arrow d.retTy d.argTys) = (d.argTys, d.retTy) :=
      collectArrowTy_foldr_base (baseTyToTermType_isBase hfrty)
    have hueq := resolved_uf_eq (f := ⟨d.name, fargs, fout, fbody⟩) hψwf
      ⟨rfl, hfbridge, hfrty, hfbwf⟩ (by simpa only [FnDef.sig] using hdsig d hd)
    have hlk : lookupUF ufs d.name = some ⟨d.name, fargs.map (·.ty), fout⟩ := by
      rw [← hueq]; exact (Option.some_get (hψwf.fvar_resolves d.name _ hmem)).symm
    -- `mkUFInterp … f.toUF = cast … (opInterp d.name …)`; its `.symm` IS the `corr` we need
    have hcorr := (mkUFInterp_fn_eq (Φ := Φ) hndΨ hdisj opInterp fvarVal hmem hlk
      (by rw [hcol]; exact hfbwf.baseTysToTermTypes_eq)
      (by rw [hcol]; exact hfrty)
      (tyDenote_arrow_eq_UFDenote' hfbwf.baseTysToTermTypes_eq hfrty)).symm
    exact UFConsistent_of_OpConsistent' d (hdwf d hd) opInterp hop fvarVal (hopcons d hd)
      (htc _ hf) (mkUFInterp Φ Ψ ufs opInterp fvarVal) hufwf
      hfbridge hfrty huwf hψwf hfbwf hfenv hopenv hcorr
  · -- fvar-side: `f = ⟨v.name, [], fout, fbody⟩`; nullary bridge `UFConsistent_of_VarConsistent'`
    obtain ⟨fid, fargs, fout, fbody⟩ := f
    obtain ⟨hfid, hfargs, hfbridge, hfrty⟩ := hsyn
    simp only at hfid hfargs hfbridge hfrty; subst hfid; subst hfargs
    have hcol : collectArrowTy v.ty = ([], v.ty) := by
      have hb := hvbase v hv; generalize v.ty = τ at *; cases hb <;> rfl
    have hueq := resolved_uf_eq_var (f := ⟨v.name, [], fout, fbody⟩) huwf ⟨rfl, rfl, hfbridge, hfrty⟩
      (hvΦ v hv)
    have hlk : lookupUF ufs v.name = some ⟨v.name, [], fout⟩ := by
      simp only [List.map_nil] at hueq
      rw [← hueq]; exact (Option.some_get (huwf.fvar_resolves v.name _ (hvΦ v hv))).symm
    have hcorr := (mkUFInterp_fvar_eq (Ψ := Ψ) hndΦ opInterp fvarVal (hvΦ v hv) hlk
      (by rw [hcol]; rfl)
      (by rw [hcol]; exact hfrty)
      (tyDenote_eq_smtTyDenote (hvbase v hv) hfrty)).symm
    exact UFConsistent_of_VarConsistent' v (hvbase v hv) (hvbody v hv) opInterp hop fvarVal
      (hvcons v hv) (htc _ hf) (mkUFInterp Φ Ψ ufs opInterp fvarVal) hufwf
      hfbridge hfrty huwf hψwf hfenv hopenv hcorr

/-! ## The model transfer at an obligation program

`smtModel_of_lambdaModel` instantiates the crux building blocks at a well-formed `OblProgram P` and
its emitted `prog`: the correspondence/nodup/disjointness hypotheses come from `OblProgramWF` and
`encode_encInv`, and definition-consistency is taken as hypotheses (`hopcons`/`hvcons` — their
discharge from Core `Factory.InterpConsistent` is deferred). The preamble's `hfs` premise is
exactly `encode_encInv`'s `EncInv.fsCorr`.
-/

/-- **Model transfer at an obligation program.** For a well-formed `P` encoding to `prog =
    block ++ [assert (not goal), checkSat]`, a definition-consistent Lambda model `(opInterp,
    fvarVal)` that SATISFIES `P.obligation` yields the constructed SMT model `(mkUFInterp …,
    mkSMTEnv)` that (a) satisfies the encoded `goal` and (b) satisfies the emitted `define-fun`
    preamble `IFs.UFConsistent (SMTProgram.ctx block).fs` and (c) every emitted block assertion
    (assumptions + distincts). The two consistency (2) families are hypotheses (deferred Factory
    projection); everything else is derived from `OblProgramWF` + `encode_encInv`. -/
theorem smtModel_of_lambdaModel {P : OblProgram} (hwf : OblProgramWF P)
    {prog : SMTProgram} (henc : encode P = .ok prog)
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    -- op-consistency (2), per definition side (deferred Factory projection):
    (hopcons : FnDefs.OpConsistent opInterp fvarVal P.defs
      (fun d hd => ((hwf.defsWF) d hd).hasTypeA))
    (hvcons : VarDefs.Consistent opInterp fvarVal P.varDefs
      (fun v hv => (hwf.varDefsWF v hv).hasTypeA))
    -- the Lambda model satisfies the obligation:
    (hsat : (simpDenote opInterp fvarVal .nil P.obligation (.tcons "bool" [])
              (HasSimpType_implies_HasTypeA hwf.obligationWF) : Bool) = true)
    -- the Lambda model satisfies every source assumption …
    (hAssumeSat : ∀ e (he : e ∈ P.assumptions),
      (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA (hwf.assumptionsWF e he)) : Bool) = true)
    -- … and every distinctness group (elements pairwise-distinct at their shared base type):
    (hDistinctSat : ∀ es (hes : es ∈ P.distincts),
      DistinctSat (Φ := P.Φ) (Ψ := P.Ψ) opInterp fvarVal es
        (hwf.distinctsWF es hes).choose
        (fun e he => (hwf.distinctsWF es hes).choose_spec.2 e he)) :
    ∃ (block : SMTProgram) (goal : Term)
      (hgtc : Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, []⟩ goal = .ok .bool),
      prog = block ++ [.assert (.app (.core .not) [goal] .bool), .checkSat] ∧
      toSMTTerm [] P.obligation = .ok goal ∧
      -- (a) the encoded obligation is satisfied
      SMTSat (ufs := (SMTProgram.ctx block).ufs)
        (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal) mkSMTEnv divByZero modByZero goal hgtc ∧
      -- (b) the emitted `define-fun` preamble is satisfied
      (∀ (hbtc : ∀ f ∈ (SMTProgram.ctx block).fs,
          Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, f.args⟩ f.body = .ok f.out),
        IFs.UFConsistent (SMTProgram.ctx block).fs hbtc
          (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal) divByZero modByZero) ∧
      -- (c) every emitted assertion (assumptions + distincts) is satisfied
      ∀ t (_ht : t ∈ (SMTProgram.ctx block).assertions)
        (hatc : Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, []⟩ t = .ok .bool),
        SMTSat (ufs := (SMTProgram.ctx block).ufs)
          (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal) mkSMTEnv divByZero modByZero t hatc := by
  -- block/goal split + context correspondence
  obtain ⟨block, goal, hsplit, _, hgoalenc, hinv⟩ := encode_encInv hwf henc
  -- name hygiene from `OblProgramWF`
  have hnames := hwf.namesNodup
  have hndΦ : (P.Φ.map (·.1)).Nodup := (List.nodup_append.mp hnames).1
  have hndΨ : (P.Ψ.map (·.1)).Nodup := (List.nodup_append.mp hnames).2.1
  have hdisj : ∀ x ∈ P.Φ, x.1 ∉ P.Ψ.map (·.1) := by
    intro x hx hxΨ
    exact (List.nodup_append.mp hnames).2.2 x.1 (List.mem_map_of_mem (f := fun p => p.1) hx) x.1 hxΨ rfl
  -- `(OblProgram.ctx P).names = P.Φnames ++ P.Ψnames` — so nodup/no-reserved transfer directly
  have hcnames : (OblProgram.ctx P).names = P.Φ.map (·.1) ++ P.Ψ.map (·.1) := rfl
  have hufwf : UFCtxWF (SMTProgram.ctx block).ufs :=
    hinv.ufCtxWF (hcnames ▸ hnames) (hcnames ▸ hwf.noReserved)
  obtain ⟨huwf, hψwf⟩ := hinv.fnameCtxWF (hcnames ▸ hnames)
  -- (a) obligation satisfaction — need `goal` type-checks at the block `ufs`
  have hgtc : Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, []⟩ goal = .ok .bool := by
    have hb := HasSimpType_implies_HasTypeA hwf.obligationWF
    -- `toSMTTerm_typeChecks` at the block context, using the correspondences' `FNameCtxWF`
    exact toSMTTerm_typeChecks hwf.obligationWF hufwf hgoalenc rfl huwf hψwf
      ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  refine ⟨block, goal, hgtc, hsplit, hgoalenc, ?_, ?_, ?_⟩
  · -- (a): the constructed model satisfies the encoded obligation
    exact mkModel_sat_obligation hndΦ hndΨ hdisj opInterp hop fvarVal
      hwf.obligationWF hsat hufwf hgtc huwf hψwf hgoalenc
  · -- (b): the constructed model satisfies the `define-fun` preamble (mixed `fs`)
    intro hbtc
    exact mkModel_sat_preamble P.defs P.varDefs hndΦ hndΨ hdisj opInterp hop fvarVal
      (fun d hd => hwf.defsWF d hd) P.defs_sig_mem hopcons
      P.varDefs_Φ_mem (fun v hv => HasSimpType_base (hwf.varDefsWF v hv)) hwf.varDefsWF hvcons
      hufwf (SMTProgram.ctx block).fs hbtc huwf hψwf hinv.fsCorr
  · -- (c): every emitted assertion is satisfied — case-split `assertsCorr`
    intro t ht hatc
    rcases hinv.assertsCorr t ht with ⟨e, he, henc_e⟩ | ⟨es, hes, hd⟩
    · -- assumption: encoded closed bool expr; reuse the obligation transfer
      exact mkModel_sat_obligation hndΦ hndΨ hdisj opInterp hop fvarVal
        (hwf.assumptionsWF e he) (hAssumeSat e he) hufwf hatc huwf hψwf henc_e
    · -- distinct group: `t = distinct (map toSMTTerm es)`; the distinctness transfer
      obtain ⟨ts, hts, rfl⟩ := hd
      exact mkModel_sat_distinct hndΦ hndΨ hdisj opInterp hop fvarVal
        (hwf.distinctsWF es hes).choose_spec.1
        (fun e he => (hwf.distinctsWF es hes).choose_spec.2 e he)
        (hDistinctSat es hes) hufwf hatc huwf hψwf hts

/-! ## Validity / unsatisfiability and the headline soundness theorems

Source-side conclusions, in the source vocabulary (`simpDenote`/`(opInterp, fvarVal)`/
definition-consistency-as-hypotheses), accounting for all the obligation program's collected
fields. Both follow `LogConseq`:
  * `OblProgram.Valid P` = "assumptions + distincts ⟹ obligation", over every definition-consistent
    Lambda model;
  * `OblProgram.Unsat P` = its dual, "assumptions + distincts ⟹ ¬obligation" (no such model
    satisfies the assumptions, the distincts, and the obligation together).

On the SMT side `SMTProgram.Unsat prog` = `¬ SMTCtx.checkSat (ctx prog) []` — no `(ufInterp, smtEnv)`
respecting the `define-fun` preamble satisfies every asserted term. The headlines are the
contrapositive of the model transfer: a Lambda model refuting the relevant obligation direction
(while satisfying assumptions/distincts) would, via `mkModel_checkSat_block`, witness the check's
satisfiability — contradicting the "solver reported UNSAT" hypothesis. Two shapes, matching the
encoders:
  * single-check (`encode`/`encodeUnsat`): the trailing literal is a persistent assertion, so the
    whole-program `SMTProgram.Unsat` captures the verdict directly (`oblProgram_*_of_smtUnsat`); the
    `*_of_verdictUnsat` variants restate this over the reified output `checkVerdicts`;
  * incremental (`encodeIncremental`): two `check-sat-assuming` queries over one pushed block — the
    verdicts live in `checkVerdicts prog = [v₀, v₁]`, phrased directly there
    (`encodeIncremental_sound`), since transient literals never enter the persistent context.
-/

/-- **A definition-consistent Lambda model satisfies `P`'s assumptions.** The source-vocabulary
    analog of `Interp.satisfies` applied to every collected assumption: each denotes `true`.
    (Op-consistency (2) of the model — the deferred Factory projection — is carried separately as
    `hopcons`/`hvcons` at the use site, matching `Interp`'s `interpConsistent` field.) -/
def LambdaModelSatisfiesAsms (P : OblProgram) (hwf : OblProgramWF P)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) : Prop :=
  ∀ e (he : e ∈ P.assumptions),
    (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA (hwf.assumptionsWF e he)) : Bool) = true

/-- **A definition-consistent Lambda model satisfies `P`'s distinctness groups.** Each collected
    `distinct` group's elements denote (under `simpDenote`) to pairwise-distinct values. The
    fvar/distinct companion of `LambdaModelSatisfiesAsms`. -/
def LambdaModelSatisfiesDistincts (P : OblProgram) (hwf : OblProgramWF P)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) : Prop :=
  ∀ es (hes : es ∈ P.distincts),
    DistinctSat (Φ := P.Φ) (Ψ := P.Ψ) opInterp fvarVal es
      (hwf.distinctsWF es hes).choose
      (fun e he => (hwf.distinctsWF es hes).choose_spec.2 e he)

/-- **The obligation program is VALID** — the source-vocabulary analog of `LogConseq`
    (assumptions + distincts ⟹ obligation). For every definition-consistent Lambda model
    (`opInterp` op-consistent, and consistent (2) with `P`'s definitions) that satisfies `P`'s
    assumption context, the obligation denotes `true`. -/
def OblProgram.Valid (P : OblProgram) (hwf : OblProgramWF P) : Prop :=
  ∀ (divByZero modByZero : Int → Int)
    (opInterp : Lambda.OpInterp simpTcInterp) (_hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp),
    FnDefs.OpConsistent opInterp fvarVal P.defs (fun d hd => ((hwf.defsWF) d hd).hasTypeA) →
    VarDefs.Consistent opInterp fvarVal P.varDefs (fun v hv => (hwf.varDefsWF v hv).hasTypeA) →
    LambdaModelSatisfiesAsms P hwf opInterp fvarVal →
    LambdaModelSatisfiesDistincts P hwf opInterp fvarVal →
    (simpDenote opInterp fvarVal .nil P.obligation (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA hwf.obligationWF) : Bool) = true

/-- **The obligation program is UNSATISFIABLE** — the dual of `OblProgram.Valid`, matching
    production's `check-sat-assuming goal` (obligation AS-IS, un-negated). For every
    definition-consistent Lambda model (`opInterp` op-consistent, and consistent (2) with `P`'s
    definitions) that satisfies `P`'s assumption + distinctness context, the obligation denotes
    `false`: "assumptions + distincts ⟹ ¬obligation". -/
def OblProgram.Unsat (P : OblProgram) (hwf : OblProgramWF P) : Prop :=
  ∀ (divByZero modByZero : Int → Int)
    (opInterp : Lambda.OpInterp simpTcInterp) (_hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp),
    FnDefs.OpConsistent opInterp fvarVal P.defs (fun d hd => ((hwf.defsWF) d hd).hasTypeA) →
    VarDefs.Consistent opInterp fvarVal P.varDefs (fun v hv => (hwf.varDefsWF v hv).hasTypeA) →
    LambdaModelSatisfiesAsms P hwf opInterp fvarVal →
    LambdaModelSatisfiesDistincts P hwf opInterp fvarVal →
    (simpDenote opInterp fvarVal .nil P.obligation (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA hwf.obligationWF) : Bool) = false

/-- The satisfiability proposition keyed on the RAW context data `(ufs, fs, asserts)`: some model
    respects the `define-fun` preamble `fs` and satisfies every term in `asserts`. A model is a full
    SMT-LIB interpretation — a sort interpretation `σ`, an array theory `𝒜`, a UF interpretation and
    variable environment over them, and div/mod-by-zero functions — all existentially quantified, so
    this matches SMT-LIB satisfiability. Factored out of `SMTCtx.checkSat` so that context equalities
    (`(ctx prog).ufs = (ctx block).ufs`, etc.) can be rewritten as PLAIN arguments — the dependence on
    `ufs` stays sealed inside this def, sidestepping the dependent-`SMTSat`-proof transport that an
    `SMTCtx`-level rewrite would trigger. -/
def SMTSatAt (ufs : UFCtx) (fs : IFs) (asserts : List Term) : Prop :=
  ∃ (σ : SortInterp) (hσ : SortInterp.AllInhabited σ) (𝒜 : ArrayTheory)
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜) (divByZero modByZero : Int → Int),
    haveI := hσ
    (∀ (hbtc : ∀ f ∈ fs, Term.typeCheck ⟨[], ufs, f.args⟩ f.body = .ok f.out),
      IFs.UFConsistent fs hbtc ufInterp divByZero modByZero) ∧
    (∀ t (_ht : t ∈ asserts)
        (hatc : Term.typeCheck ⟨[], ufs, []⟩ t = .ok .bool),
      SMTSat (ufs := ufs) ufInterp smtEnv divByZero modByZero t hatc)

/-- **The denotation of a `check-sat` / `check-sat-assuming`** at an accumulated context `c` with
    TRANSIENT literals `lits` (empty for a plain `check-sat`). The command asks "is there a model?",
    so its meaning IS that satisfiability proposition: SOME model `(ufInterp, smtEnv)` that DEFINES
    every interpreted function as its body (the `define-fun` preamble) satisfies every PERSISTENT
    assertion AND every transient literal (`c.assertions ++ lits`). The solver reporting UNSAT is
    exactly `¬ SMTCtx.checkSat c lits`. The `lits` are queried but NOT added to `c` — that
    transience is `check-sat-assuming`'s whole point (`SMTCtx.step` leaves a check's context fixed). -/
def SMTCtx.checkSat (c : SMTCtx) (lits : List Term) : Prop :=
  SMTSatAt c.ufs c.fs (c.assertions ++ lits)

/-- **The SMT program is UNSATISFIABLE** (w.r.t. the `define-fun` preamble) — a WHOLE-program,
    block/goal-agnostic notion, treating every emitted assertion identically (as SMT-LIB does):
    NO model — under ANY sort interpretation and array theory — that respects the preamble satisfies
    every asserted term. Expressed as the NEGATION of a plain `check-sat` (no transient literals) at
    the program's final context — the term-level analog of a solver's "UNSAT modulo the define-fun
    theory". -/
def SMTProgram.Unsat (prog : SMTProgram) : Prop :=
  ¬ SMTCtx.checkSat (SMTProgram.ctx prog) []

/-! ## The output of an SMT program: the ordered list of check verdicts

Running an SMT-LIB script produces one sat/unsat verdict per `check-sat`(-assuming) command.
`checkVerdicts` is that output, reified as a `List Prop`: fold the commands left-to-right
accumulating the context (`SMTCtx.step`, exactly as a solver does), and at each check emit its
satisfiability proposition `SMTCtx.checkSat c lits` at the context `c` reached so far (with the
query's transient literals `lits`). Non-check commands contribute nothing. The `i`-th entry is the
meaning of the `i`-th check; "the solver reported UNSAT for check `i`" is `¬ verdicts[i]`. The
top-level soundness results read positionally off this list.
-/

/-- Fold the program from an accumulated context `c`, emitting one `SMTCtx.checkSat` proposition per
    check (at the context reached just before it) and nothing for context-building commands. -/
def verdictsFrom (c : SMTCtx) : SMTProgram → List Prop
  | [] => []
  | cmd :: rest =>
    (match cmd.checkLits? with
      | some lits => [SMTCtx.checkSat c lits]
      | none => []) ++ verdictsFrom (c.step cmd) rest

/-- **The output of an SMT program**: the ordered list of its check verdicts, from the empty
    context. `checkVerdicts prog` has one `Prop` per `check-sat`(-assuming) in `prog`; the solver
    reporting UNSAT for the `i`-th check is `¬ (checkVerdicts prog)[i]`. -/
def SMTProgram.checkVerdicts (prog : SMTProgram) : List Prop :=
  verdictsFrom {} prog

/-- `verdictsFrom` distributes over `++`: the second segment's verdicts are computed at the context
    reached after folding the first. -/
theorem verdictsFrom_append (a b : SMTProgram) (c : SMTCtx) :
    verdictsFrom c (a ++ b) = verdictsFrom c a ++ verdictsFrom (a.foldl SMTCtx.step c) b := by
  induction a generalizing c with
  | nil => simp [verdictsFrom]
  | cons hd tl ih =>
    simp only [List.cons_append, verdictsFrom, List.foldl_cons, ih, List.append_assoc]

/-- **A check-free segment emits no verdicts.** If every command of `seg` is a non-check
    (`isCheck = false`), `verdictsFrom c seg = []` at any starting context — in particular an
    encoded block (`encodeBlock_noCheck`) contributes nothing to the verdict list. -/
theorem verdictsFrom_noCheck (c : SMTCtx) {seg : SMTProgram}
    (h : ∀ cmd ∈ seg, cmd.isCheck = false) : verdictsFrom c seg = [] := by
  induction seg generalizing c with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : hd.checkLits? = none :=
      SMTCommand.checkLits?_eq_none_iff.mpr (h hd (by simp))
    simp only [verdictsFrom, hhd, ih (c.step hd) (fun cmd hcmd => h cmd (by simp [hcmd])),
      List.nil_append]

/-- **Single-check verdict list.** A program `block ++ [assert lit, checkSat]` — the shape of both
    single-check encoders (`encode` / `encodeUnsat`) — with a check-free `block` produces the ONE
    verdict `SMTCtx.checkSat (ctx block) [lit]`: the block emits nothing (`verdictsFrom_noCheck`),
    the `assert lit` emits nothing but folds `lit` into the context, and the trailing `checkSat`
    (transient literals `[]`) queries that extended context — which `SMTCtx.checkSat`-normalizes to
    the block context under the transient literal `[lit]` (append-to-`assertions` = transient). -/
theorem checkVerdicts_singleCheck {block : SMTProgram} (lit : Term)
    (hblock : ∀ cmd ∈ block, cmd.isCheck = false) :
    SMTProgram.checkVerdicts (block ++ [.assert lit, .checkSat])
      = [SMTCtx.checkSat (SMTProgram.ctx block) [lit]] := by
  unfold SMTProgram.checkVerdicts
  rw [verdictsFrom_append, verdictsFrom_noCheck _ hblock, List.nil_append]
  -- the trailing `[assert lit, checkSat]` at the block-folded context
  show verdictsFrom (block.foldl SMTCtx.step {}) [.assert lit, .checkSat] = _
  simp only [verdictsFrom, SMTCommand.checkLits?, SMTCtx.step, List.nil_append, List.append_nil]
  -- `checkSat` at `(ctx block)+lit` with no transient lits = `checkSat (ctx block) [lit]`
  show [SMTCtx.checkSat { (SMTProgram.ctx block) with
      assertions := (SMTProgram.ctx block).assertions ++ [lit] } []] = _
  simp only [SMTCtx.checkSat, List.append_nil, SMTProgram.ctx]

/-- The single-check program's plain `check-sat` (no transient literals) at its FINAL context IS the
    block's `check-sat` under the transient literal `[lit]` — the trailing `assert lit` folds `lit`
    into `assertions`, the trailing `checkSat` is a no-op. This is what identifies `SMTProgram.Unsat
    (block ++ [assert lit, checkSat])` with the sole `checkVerdicts` entry. -/
theorem checkSat_prog_singleCheck (block : SMTProgram) (lit : Term) :
    SMTCtx.checkSat (SMTProgram.ctx (block ++ [.assert lit, .checkSat])) []
      = SMTCtx.checkSat (SMTProgram.ctx block) [lit] := by
  simp only [SMTCtx.checkSat, SMTProgram.ctx, List.foldl_append, List.foldl_cons, List.foldl_nil,
    SMTCtx.step, List.append_nil]

/-- **Two-check verdict list (incremental shape).** `block ++ [checkSatAssuming [goal],
    checkSatAssuming [not goal]]` with a check-free `block` produces the TWO verdicts
    `[SMTCtx.checkSat (ctx block) [goal], SMTCtx.checkSat (ctx block) [not goal]]` — the shared
    block is queried under each transient literal in turn (neither `checkSatAssuming` mutates the
    context, so both verdicts are at the SAME `ctx block`). -/
theorem checkVerdicts_incremental {block : SMTProgram} (goal : Term)
    (hblock : ∀ cmd ∈ block, cmd.isCheck = false) :
    SMTProgram.checkVerdicts (block ++ [.checkSatAssuming [goal],
        .checkSatAssuming [.app (.core .not) [goal] .bool]])
      = [SMTCtx.checkSat (SMTProgram.ctx block) [goal],
         SMTCtx.checkSat (SMTProgram.ctx block) [.app (.core .not) [goal] .bool]] := by
  unfold SMTProgram.checkVerdicts
  rw [verdictsFrom_append, verdictsFrom_noCheck _ hblock, List.nil_append]
  show verdictsFrom (block.foldl SMTCtx.step {})
    [.checkSatAssuming [goal], .checkSatAssuming [.app (.core .not) [goal] .bool]] = _
  simp only [verdictsFrom, SMTCommand.checkLits?, SMTCtx.step, List.nil_append, List.append_nil,
    List.cons_append, SMTProgram.ctx]

/-- **The shared block-level model witness.** Given a well-formed `P` whose
    command block corresponds (`EncInv`) to `block`, a definition-consistent Lambda model that
    satisfies `P`'s assumptions/distincts, and a SINGLE trailing literal `lit` that the constructed
    model satisfies, the constructed `(mkUFInterp, mkSMTEnv)` WITNESSES `SMTCtx.checkSat` of `block`
    under the transient literal `lit`: it respects the `define-fun` preamble (b) and satisfies every
    block assertion (c) — assumptions/distincts — together with `lit`. This is the common core of
    every soundness direction: each supplies its own `lit` (`goal` / `not goal`) and its
    `hlitsat` (from `mkModel_sat_obligation` or the `mkModel_denote_obligation` flip). -/
theorem mkModel_checkSat_block {P : OblProgram} (hwf : OblProgramWF P) {block : SMTProgram}
    (hinv : EncInv (OblProgram.ctx P) (SMTProgram.ctx block))
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (hopcons : FnDefs.OpConsistent opInterp fvarVal P.defs
      (fun d hd => ((hwf.defsWF) d hd).hasTypeA))
    (hvcons : VarDefs.Consistent opInterp fvarVal P.varDefs
      (fun v hv => (hwf.varDefsWF v hv).hasTypeA))
    (hAssumeSat : LambdaModelSatisfiesAsms P hwf opInterp fvarVal)
    (hDistinctSat : LambdaModelSatisfiesDistincts P hwf opInterp fvarVal)
    (lit : Term)
    (hlittc : Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, []⟩ lit = .ok .bool)
    (hlitsat : SMTSat (ufs := (SMTProgram.ctx block).ufs)
      (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal) mkSMTEnv divByZero modByZero lit hlittc) :
    SMTCtx.checkSat (SMTProgram.ctx block) [lit] := by
  -- name hygiene from `OblProgramWF`
  have hnames := hwf.namesNodup
  have hndΦ : (P.Φ.map (·.1)).Nodup := (List.nodup_append.mp hnames).1
  have hndΨ : (P.Ψ.map (·.1)).Nodup := (List.nodup_append.mp hnames).2.1
  have hdisj : ∀ x ∈ P.Φ, x.1 ∉ P.Ψ.map (·.1) := by
    intro x hx hxΨ
    exact (List.nodup_append.mp hnames).2.2 x.1 (List.mem_map_of_mem (f := fun p => p.1) hx) x.1 hxΨ rfl
  have hcnames : (OblProgram.ctx P).names = P.Φ.map (·.1) ++ P.Ψ.map (·.1) := rfl
  have hufwf : UFCtxWF (SMTProgram.ctx block).ufs :=
    hinv.ufCtxWF (hcnames ▸ hnames) (hcnames ▸ hwf.noReserved)
  obtain ⟨huwf, hψwf⟩ := hinv.fnameCtxWF (hcnames ▸ hnames)
  -- (b) the constructed model respects the `define-fun` preamble
  have hpreamble : ∀ (hbtc : ∀ f ∈ (SMTProgram.ctx block).fs,
      Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, f.args⟩ f.body = .ok f.out),
      IFs.UFConsistent (SMTProgram.ctx block).fs hbtc
        (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal) divByZero modByZero := by
    intro hbtc
    exact mkModel_sat_preamble P.defs P.varDefs hndΦ hndΨ hdisj opInterp hop fvarVal
      (fun d hd => hwf.defsWF d hd) P.defs_sig_mem hopcons
      P.varDefs_Φ_mem (fun v hv => HasSimpType_base (hwf.varDefsWF v hv)) hwf.varDefsWF hvcons
      hufwf (SMTProgram.ctx block).fs hbtc huwf hψwf hinv.fsCorr
  -- assemble the SAT witness: `(mkUFInterp, mkSMTEnv)` satisfies preamble + block asserts + `lit`
  refine ⟨defaultσ, inferInstance, SmtArrayTheory,
    mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal, mkSMTEnv,
    divByZero, modByZero, hpreamble, ?_⟩
  intro t ht hatc
  rw [List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | rfl
  · -- (c) a block assertion: an assumption or a distinctness group
    rcases hinv.assertsCorr t ht with ⟨e, he, henc_e⟩ | ⟨es, hes, hd⟩
    · exact mkModel_sat_obligation hndΦ hndΨ hdisj opInterp hop fvarVal
        (hwf.assumptionsWF e he) (hAssumeSat e he) hufwf hatc huwf hψwf henc_e
    · obtain ⟨ts, hts, rfl⟩ := hd
      exact mkModel_sat_distinct hndΦ hndΨ hdisj opInterp hop fvarVal
        (hwf.distinctsWF es hes).choose_spec.1
        (fun e he => (hwf.distinctsWF es hes).choose_spec.2 e he)
        (hDistinctSat es hes) hufwf hatc huwf hψwf hts
  · -- the transient literal `lit`: satisfied by hypothesis (`hatc` proof-irrelevant to `hlittc`)
    exact hlitsat

/-- **Soundness core (explicit `encode P = .ok prog`): SMT-unsatisfiability ⟹ obligation-program
    validity.** The workhorse behind the headline `oblProgram_valid_of_smtUnsat`; takes the concrete
    `prog` and its encoding equation directly (the headline recovers them via `encode_succeeds`).
    Assumptions: `P` well-formed, `encode P = .ok prog`, and `prog` UNSAT (whole-program,
    block/goal-agnostic). The block/goal split, `goal = toSMTTerm P.obligation`, and the context
    correspondence are all DERIVED internally from `encode_encInv`. The contrapositive of the model
    transfer: a definition-consistent Lambda model satisfying the assumptions but REFUTING the
    obligation constructs (`mkUFInterp`) an SMT model respecting the preamble and satisfying EVERY
    assertion — the block assertions (via clauses (b)/(c)) and the trailing negated `goal` (since the
    obligation is refuted) — contradicting `Unsat`. -/
theorem oblProgram_valid_of_smtUnsat' {P : OblProgram} (hwf : OblProgramWF P)
    {prog : SMTProgram} (henc : encode P = .ok prog)
    (hunsat : SMTProgram.Unsat prog) :
    OblProgram.Valid P hwf := by
  intro divByZero modByZero opInterp hop fvarVal hopcons hvcons hAssumeSat hDistinctSat
  -- `encode_encInv` DERIVES the block/goal split (`prog = block ++ [assert (not goal), checkSat]`)
  obtain ⟨block, goal, hsplit, _, hgoalenc, hinv⟩ := encode_encInv hwf henc
  subst hsplit
  -- name hygiene + context WF at the block
  have hnames := hwf.namesNodup
  have hndΦ : (P.Φ.map (·.1)).Nodup := (List.nodup_append.mp hnames).1
  have hndΨ : (P.Ψ.map (·.1)).Nodup := (List.nodup_append.mp hnames).2.1
  have hdisj : ∀ x ∈ P.Φ, x.1 ∉ P.Ψ.map (·.1) := by
    intro x hx hxΨ
    exact (List.nodup_append.mp hnames).2.2 x.1 (List.mem_map_of_mem (f := fun p => p.1) hx) x.1 hxΨ rfl
  have hcnames : (OblProgram.ctx P).names = P.Φ.map (·.1) ++ P.Ψ.map (·.1) := rfl
  have hufwf : UFCtxWF (SMTProgram.ctx block).ufs :=
    hinv.ufCtxWF (hcnames ▸ hnames) (hcnames ▸ hwf.noReserved)
  obtain ⟨huwf, hψwf⟩ := hinv.fnameCtxWF (hcnames ▸ hnames)
  -- the negated goal type-checks at the block context (it's the emitted trailing assertion body)
  have hgtc : Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, []⟩ goal = .ok .bool :=
    toSMTTerm_typeChecks hwf.obligationWF hufwf hgoalenc rfl huwf hψwf
      ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  have hntc : Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, []⟩ (.app (.core .not) [goal] .bool)
      = .ok .bool := by
    simp only [Term.typeCheck, bind, Except.bind, hgtc, beq_self_eq_true, Bool.and_true, if_true]
  -- the single-check `prog`'s plain check IS the block's check under `[not goal]` (checkSat no-op).
  rw [SMTProgram.Unsat, checkSat_prog_singleCheck] at hunsat
  -- refute UNSAT: if the obligation were REFUTED, the model would satisfy the block + `not goal`
  cases hobl : (simpDenote opInterp fvarVal .nil P.obligation (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA hwf.obligationWF) : Bool) with
  | true => rfl
  | false =>
    exfalso; apply hunsat
    -- the model satisfies `not goal`: `Term.denoteTyped (not goal) = ! (Term.denoteTyped goal) = !false`
    have hnsat : SMTSat (ufs := (SMTProgram.ctx block).ufs)
        (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal) mkSMTEnv divByZero modByZero
        (.app (.core .not) [goal] .bool) hntc := by
      have hgdenote : (Term.denoteTyped (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal)
          mkSMTEnv divByZero modByZero goal .bool hgtc : Bool) = false := by
        rw [mkModel_denote_obligation hndΦ hndΨ hdisj opInterp hop fvarVal hwf.obligationWF
          hufwf hgtc huwf hψwf hgoalenc, hobl]
      unfold SMTSat Term.denoteTyped
      rcases htni : Term.typeCheck_not_inv hntc with ⟨ht', heq⟩
      dsimp only; rw [cast_eq]
      have hpi : Term.denoteTyped (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal)
          mkSMTEnv divByZero modByZero goal .bool ht'
        = Term.denoteTyped (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal)
          mkSMTEnv divByZero modByZero goal .bool hgtc := rfl
      rw [hpi, hgdenote]; rfl
    exact mkModel_checkSat_block hwf hinv opInterp hop fvarVal hopcons hvcons hAssumeSat
      hDistinctSat _ hntc hnsat

/-- **HEADLINE: SMT-unsatisfiability ⟹ obligation-program validity.** Stated as a MATCH on
    `encode P`: the encoder SUCCEEDS on a well-formed `P` (so the `.error` branch is `False`,
    discharged by `encode_succeeds`), and on success, unsatisfiability of the emitted `prog`
    (whole-program, block/goal-agnostic) implies `P` is `Valid`. The only assumption beyond
    well-formedness is the UNSAT of the actual compiled program — no separate `encode P = .ok _`.
    Delegates to `oblProgram_valid_of_smtUnsat'` once `encode_succeeds` pins the concrete `prog`. -/
theorem oblProgram_valid_of_smtUnsat {P : OblProgram} (hwf : OblProgramWF P) :
    match encode P with
      | .ok prog => SMTProgram.Unsat prog → OblProgram.Valid P hwf
      | .error _ => False := by
  obtain ⟨prog, henc⟩ := encode_succeeds hwf
  rw [henc]
  exact fun hunsat => oblProgram_valid_of_smtUnsat' hwf henc hunsat

/-- **HEADLINE over the program OUTPUT (validity).** `encode P` emits a program whose output is a
    single verdict, `checkVerdicts prog = [v]`; the solver reporting UNSAT for that check (`¬ v`)
    implies `P` is `Valid`. This reads the guarantee directly off the reified transcript output,
    rather than the whole-program `SMTProgram.Unsat`. -/
theorem oblProgram_valid_of_verdictUnsat {P : OblProgram} (hwf : OblProgramWF P) :
    match encode P with
      | .ok prog => ∃ v, SMTProgram.checkVerdicts prog = [v] ∧ (¬ v → OblProgram.Valid P hwf)
      | .error _ => False := by
  obtain ⟨prog, henc⟩ := encode_succeeds hwf
  rw [henc]
  obtain ⟨block, goal, hsplit, hblock, hgoalenc, hinv⟩ := encode_encInv hwf henc
  refine ⟨SMTCtx.checkSat (SMTProgram.ctx block) [.app (.core .not) [goal] .bool], ?_, ?_⟩
  · rw [hsplit]; exact checkVerdicts_singleCheck _ (encodeBlock_noCheck hblock)
  · -- the verdict is exactly `SMTProgram.Unsat prog`'s negatee (`checkSat_prog_singleCheck`)
    intro hv
    refine oblProgram_valid_of_smtUnsat' hwf henc ?_
    rw [SMTProgram.Unsat, hsplit, checkSat_prog_singleCheck]; exact hv

/-- **Soundness core, UNSAT direction (explicit `encodeUnsat P = .ok prog`): SMT-unsatisfiability
    (with the obligation AS-IS) ⟹ obligation-program UNSATISFIABILITY.** The dual of
    `oblProgram_valid_of_smtUnsat'`, and its exact structural mirror. Assumptions: `P` well-formed,
    `encodeUnsat P = .ok prog`, and `prog` UNSAT (whole-program, block/goal-agnostic). The block/goal
    split and context correspondence come from `encodeUnsat_encInv` (the twin of `encode_encInv`);
    the trailing literal is `assert goal` (not `assert (not goal)`). The contrapositive of the model
    transfer: a definition-consistent Lambda model satisfying the assumptions/distincts AND the
    obligation would construct (`mkUFInterp`) an SMT model respecting the preamble and satisfying
    EVERY assertion — the block assertions (assumptions/distincts) AND the trailing un-negated `goal`
    (since the obligation HOLDS) — contradicting `Unsat`. So the obligation must denote `false`. -/
theorem oblProgram_unsat_of_smtUnsat' {P : OblProgram} (hwf : OblProgramWF P)
    {prog : SMTProgram} (henc : encodeUnsat P = .ok prog)
    (hunsat : SMTProgram.Unsat prog) :
    OblProgram.Unsat P hwf := by
  intro divByZero modByZero opInterp hop fvarVal hopcons hvcons hAssumeSat hDistinctSat
  -- `encodeUnsat_encInv` DERIVES the block/goal split (`prog = block ++ [assert goal, checkSat]`)
  obtain ⟨block, goal, hsplit, _, hgoalenc, hinv⟩ := encodeUnsat_encInv hwf henc
  subst hsplit
  -- name hygiene + context WF at the block
  have hnames := hwf.namesNodup
  have hndΦ : (P.Φ.map (·.1)).Nodup := (List.nodup_append.mp hnames).1
  have hndΨ : (P.Ψ.map (·.1)).Nodup := (List.nodup_append.mp hnames).2.1
  have hdisj : ∀ x ∈ P.Φ, x.1 ∉ P.Ψ.map (·.1) := by
    intro x hx hxΨ
    exact (List.nodup_append.mp hnames).2.2 x.1 (List.mem_map_of_mem (f := fun p => p.1) hx) x.1 hxΨ rfl
  have hcnames : (OblProgram.ctx P).names = P.Φ.map (·.1) ++ P.Ψ.map (·.1) := rfl
  have hufwf : UFCtxWF (SMTProgram.ctx block).ufs :=
    hinv.ufCtxWF (hcnames ▸ hnames) (hcnames ▸ hwf.noReserved)
  obtain ⟨huwf, hψwf⟩ := hinv.fnameCtxWF (hcnames ▸ hnames)
  -- the goal type-checks at the block context (it's the emitted trailing assertion body)
  have hgtc : Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, []⟩ goal = .ok .bool :=
    toSMTTerm_typeChecks hwf.obligationWF hufwf hgoalenc rfl huwf hψwf
      ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  -- the single-check `prog`'s plain check IS the block's check under `[goal]` (checkSat no-op).
  rw [SMTProgram.Unsat, checkSat_prog_singleCheck] at hunsat
  -- refute UNSAT: if the obligation HELD, the model would satisfy the block + `goal`
  cases hobl : (simpDenote opInterp fvarVal .nil P.obligation (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA hwf.obligationWF) : Bool) with
  | false => rfl
  | true =>
    exfalso; apply hunsat
    -- the model satisfies `goal` directly (obligation holds ⇒ encoded goal denotes true)
    have hgsat : SMTSat (ufs := (SMTProgram.ctx block).ufs)
        (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal) mkSMTEnv divByZero modByZero goal hgtc :=
      mkModel_sat_obligation hndΦ hndΨ hdisj opInterp hop fvarVal
        hwf.obligationWF hobl hufwf hgtc huwf hψwf hgoalenc
    exact mkModel_checkSat_block hwf hinv opInterp hop fvarVal hopcons hvcons hAssumeSat
      hDistinctSat _ hgtc hgsat

/-- **HEADLINE (UNSAT direction): SMT-unsatisfiability (obligation AS-IS) ⟹ obligation-program
    UNSATISFIABILITY.** The dual of `oblProgram_valid_of_smtUnsat`. Stated as a MATCH on
    `encodeUnsat P`: the encoder SUCCEEDS on a well-formed `P` (the `.error` branch is `False`,
    discharged by `encodeUnsat_succeeds`), and on success, unsatisfiability of the emitted `prog`
    (whole-program, block/goal-agnostic) implies `P` is `Unsat`. Delegates to
    `oblProgram_unsat_of_smtUnsat'` once `encodeUnsat_succeeds` pins the concrete `prog`. -/
theorem oblProgram_unsat_of_smtUnsat {P : OblProgram} (hwf : OblProgramWF P) :
    match encodeUnsat P with
      | .ok prog => SMTProgram.Unsat prog → OblProgram.Unsat P hwf
      | .error _ => False := by
  obtain ⟨prog, henc⟩ := encodeUnsat_succeeds hwf
  rw [henc]
  exact fun hunsat => oblProgram_unsat_of_smtUnsat' hwf henc hunsat

/-- **HEADLINE over the program OUTPUT (unsatisfiability).** `encodeUnsat P` emits a program whose
    output is a single verdict, `checkVerdicts prog = [v]`; the solver reporting UNSAT for that
    check (`¬ v`) implies `P` is `Unsat` (no consistent model satisfies asms/distincts AND the
    obligation). Reads the guarantee directly off the reified transcript output. -/
theorem oblProgram_unsat_of_verdictUnsat {P : OblProgram} (hwf : OblProgramWF P) :
    match encodeUnsat P with
      | .ok prog => ∃ v, SMTProgram.checkVerdicts prog = [v] ∧ (¬ v → OblProgram.Unsat P hwf)
      | .error _ => False := by
  obtain ⟨prog, henc⟩ := encodeUnsat_succeeds hwf
  rw [henc]
  obtain ⟨block, goal, hsplit, hblock, hgoalenc, hinv⟩ := encodeUnsat_encInv hwf henc
  refine ⟨SMTCtx.checkSat (SMTProgram.ctx block) [goal], ?_, ?_⟩
  · rw [hsplit]; exact checkVerdicts_singleCheck _ (encodeBlock_noCheck hblock)
  · intro hv
    refine oblProgram_unsat_of_smtUnsat' hwf henc ?_
    rw [SMTProgram.Unsat, hsplit, checkSat_prog_singleCheck]; exact hv

/-! ## Incremental shape: two `check-sat-assuming` queries over one shared block

`encodeIncremental` pushes the block once and issues two `checkSatAssuming` queries under the
transient literals `goal` then `not goal`. Because the checks are pure queries (they do not fold
their literals into the persistent `assertions`), the shared block's `EncInv` — hence the whole
model transfer — is identical for both. So each verdict feeds the same `mkModel_checkSat_block`
workhorse: the sat query `¬ checkSat block [goal]` gives obligation unsatisfiability (dual of
`encodeUnsat`), and the validity query `¬ checkSat block [not goal]` gives obligation validity (dual
of `encode`).
-/

/-- **The two check verdicts of `encodeIncremental`, read off `checkVerdicts`.** For a well-formed
    `P` encoding (incrementally) to `prog`, the program's output list has exactly TWO verdicts —
    `checkVerdicts prog = [v₀, v₁]` — and:
      • the solver reporting UNSAT for the FIRST (satisfiability) check (`¬ v₀`) ⟹ `OblProgram.Unsat P`;
      • the solver reporting UNSAT for the SECOND (validity) check (`¬ v₁`) ⟹ `OblProgram.Valid P`.
    Both facts come from ONE shared block via `mkModel_checkSat_block` — the incremental transcript
    proves them from a single push, exactly as production's `check-sat-assuming` does. The verdicts
    are stated positionally over the reified program output rather than by re-deriving the split. -/
theorem encodeIncremental_sound {P : OblProgram} (hwf : OblProgramWF P) :
    match encodeIncremental P with
      | .ok prog =>
        ∃ v₀ v₁,
          SMTProgram.checkVerdicts prog = [v₀, v₁] ∧
          (¬ v₀ → OblProgram.Unsat P hwf) ∧
          (¬ v₁ → OblProgram.Valid P hwf)
      | .error _ => False := by
  obtain ⟨prog, henc⟩ := encodeIncremental_succeeds hwf
  rw [henc]
  obtain ⟨block, goal, hsplit, hblock, hgoalenc, hinv⟩ := encodeIncremental_encInv hwf henc
  -- name hygiene + context WF at the block (shared by both verdicts)
  have hnames := hwf.namesNodup
  have hndΦ : (P.Φ.map (·.1)).Nodup := (List.nodup_append.mp hnames).1
  have hndΨ : (P.Ψ.map (·.1)).Nodup := (List.nodup_append.mp hnames).2.1
  have hdisj : ∀ x ∈ P.Φ, x.1 ∉ P.Ψ.map (·.1) := by
    intro x hx hxΨ
    exact (List.nodup_append.mp hnames).2.2 x.1 (List.mem_map_of_mem (f := fun p => p.1) hx) x.1 hxΨ rfl
  have hcnames : (OblProgram.ctx P).names = P.Φ.map (·.1) ++ P.Ψ.map (·.1) := rfl
  have hufwf : UFCtxWF (SMTProgram.ctx block).ufs :=
    hinv.ufCtxWF (hcnames ▸ hnames) (hcnames ▸ hwf.noReserved)
  obtain ⟨huwf, hψwf⟩ := hinv.fnameCtxWF (hcnames ▸ hnames)
  have hgtc : Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, []⟩ goal = .ok .bool :=
    toSMTTerm_typeChecks hwf.obligationWF hufwf hgoalenc rfl huwf hψwf
      ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  have hntc : Term.typeCheck ⟨[], (SMTProgram.ctx block).ufs, []⟩ (.app (.core .not) [goal] .bool)
      = .ok .bool := by
    simp only [Term.typeCheck, bind, Except.bind, hgtc, beq_self_eq_true, Bool.and_true, if_true]
  -- the two verdicts, read off `checkVerdicts` (block is check-free by `encodeBlock_noCheck`)
  refine ⟨SMTCtx.checkSat (SMTProgram.ctx block) [goal],
    SMTCtx.checkSat (SMTProgram.ctx block) [.app (.core .not) [goal] .bool], ?_, ?_, ?_⟩
  · rw [hsplit]; exact checkVerdicts_incremental goal (encodeBlock_noCheck hblock)
  · -- ¬ v₀ (SAT query UNSAT) ⟹ obligation UNSATISFIABLE (mirrors `oblProgram_unsat_of_smtUnsat'`)
    intro hunsat divByZero modByZero opInterp hop fvarVal hopcons hvcons hAssumeSat hDistinctSat
    cases hobl : (simpDenote opInterp fvarVal .nil P.obligation (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA hwf.obligationWF) : Bool) with
    | false => rfl
    | true =>
      exfalso; apply hunsat
      have hgsat : SMTSat (ufs := (SMTProgram.ctx block).ufs)
          (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal) mkSMTEnv divByZero modByZero goal hgtc :=
        mkModel_sat_obligation hndΦ hndΨ hdisj opInterp hop fvarVal
          hwf.obligationWF hobl hufwf hgtc huwf hψwf hgoalenc
      exact mkModel_checkSat_block hwf hinv opInterp hop fvarVal hopcons hvcons hAssumeSat
        hDistinctSat _ hgtc hgsat
  · -- ¬ v₁ (VALIDITY query UNSAT) ⟹ obligation VALID (mirrors `oblProgram_valid_of_smtUnsat'`)
    intro hunsat divByZero modByZero opInterp hop fvarVal hopcons hvcons hAssumeSat hDistinctSat
    cases hobl : (simpDenote opInterp fvarVal .nil P.obligation (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA hwf.obligationWF) : Bool) with
    | true => rfl
    | false =>
      exfalso; apply hunsat
      have hnsat : SMTSat (ufs := (SMTProgram.ctx block).ufs)
          (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal) mkSMTEnv divByZero modByZero
          (.app (.core .not) [goal] .bool) hntc := by
        have hgdenote : (Term.denoteTyped (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal)
            mkSMTEnv divByZero modByZero goal .bool hgtc : Bool) = false := by
          rw [mkModel_denote_obligation hndΦ hndΨ hdisj opInterp hop fvarVal hwf.obligationWF
            hufwf hgtc huwf hψwf hgoalenc, hobl]
        unfold SMTSat Term.denoteTyped
        rcases htni : Term.typeCheck_not_inv hntc with ⟨ht', heq⟩
        dsimp only; rw [cast_eq]
        have hpi : Term.denoteTyped (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal)
            mkSMTEnv divByZero modByZero goal .bool ht'
          = Term.denoteTyped (mkUFInterp P.Φ P.Ψ (SMTProgram.ctx block).ufs opInterp fvarVal)
            mkSMTEnv divByZero modByZero goal .bool hgtc := rfl
        rw [hpi, hgdenote]; rfl
      exact mkModel_checkSat_block hwf hinv opInterp hop fvarVal hopcons hvcons hAssumeSat
        hDistinctSat _ hntc hnsat

end Core.ModelTransfer
