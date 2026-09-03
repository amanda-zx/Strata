/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
import all Strata.Languages.Core.PrototypeSMTGen.FunDef
import all Strata.DL.SMT.DenoteTyped

/-!
# Construction layer for the interpreted-function SMT encoder

This file defines the two IRs — the obligation program (`OblProgram`/`OblCtx`) and the SMT program
(`SMTProgram`/`SMTCtx`) — the encoder `encode : OblProgram → Except Format SMTProgram` (with the
`encodeUnsat` / `encodeIncremental` variants, matching the production encoder), and the SYNTACTIC
correspondence between the two. `EncInv (c : OblCtx) (s : SMTCtx)` says the emitted SMT context
matches the source obligation context structurally: emitted UF ids permute the source declared
names, each source signature resolves to an emitted UF, each emitted `define-fun` is the syntactic
encoding of a source `fnDef`/`varDef`, and each emitted assertion is an encoded source assumption or
distinct group. `encode_encInv` proves the encoder establishes this invariant, via a walk folding
the command list into growing contexts on both sides, `(Φ, Ψ, defs)` and `(ufs, fs)`, maintaining
the correspondence per step. On top of this structural match, `ModelTransfer` builds the SEMANTIC
correspondence that yields soundness.

This file builds the SMT-side objects — `UFCtx`/`IFs`, bound-variable contexts, encoded bodies — and
discharges the abstract witnesses the relational theorems take as hypotheses.

Key definitions: `canonicalArgBvs`, `FnDef.encodeToIF`, `SMTCommand` / `SMTProgram` with
`SMTProgram.ctx` and `SMTProgramWF`, `OblProgram` with `OblProgramWF`, and `encode` (with the
`encodeUnsat` / `encodeIncremental` variants). Key results: `encodeToIF_succeeds`,
`encodeToIF_ok_inv`, `encode_succeeds`, `encode_wf`, `encode_encInv`.
-/

open Core Lambda Imperative Strata.SMT Std
open Strata.SMT.DenoteTyped

namespace Core.Construct

/-! ## Canonical bound-variable formals

A `FnDef`'s formals encode to canonical `TermVar`s named by the `$__bv{…}` scheme
(position-determined, innermost-last), matching what `toSMTTerm` emits for `.bvar` nodes and what
`BVarCtxWF.id_scheme` requires. -/

/-- Build canonical `TermVar`s from ALREADY-ENCODED SMT sorts: position `i` (from the
    right) gets id `$__bv{i}` and the given sort. Total (the encodability question is
    handled once by `baseTysToTermTypes` in `canonicalArgBvs`). -/
def canonicalArgBvsOfSorts : List TermType → TermVarCtx
  | [] => []
  | sty :: stys => ⟨s!"$__bv{stys.length}", sty⟩ :: canonicalArgBvsOfSorts stys

/-- The canonical `TermVar`s for a bound-variable context. FAILS (`.error`) if any
    formal type is non-base. -/
def canonicalArgBvs (Δ : List LMonoTy) : Except Format TermVarCtx :=
  match baseTysToTermTypes Δ with
  | some stys => .ok (canonicalArgBvsOfSorts stys)
  | none => .error f!"canonicalArgBvs: a formal type is non-base in {repr Δ}"

theorem canonicalArgBvsOfSorts_length (stys : List TermType) :
    (canonicalArgBvsOfSorts stys).length = stys.length := by
  induction stys with
  | nil => rfl
  | cons sty stys ih => simp only [canonicalArgBvsOfSorts, List.length_cons, ih]

/-- The i-th canonical var carries the i-th encoded sort. -/
theorem canonicalArgBvsOfSorts_getElem_ty (stys : List TermType) (i : Nat)
    (hi : i < (canonicalArgBvsOfSorts stys).length) :
    ((canonicalArgBvsOfSorts stys)[i]'hi).ty = stys[i]'(by rwa [canonicalArgBvsOfSorts_length] at hi) := by
  induction stys generalizing i with
  | nil => simp [canonicalArgBvsOfSorts] at hi
  | cons sty stys ih =>
    cases i with
    | zero => simp only [canonicalArgBvsOfSorts, List.getElem_cons_zero]
    | succ j =>
      simp only [canonicalArgBvsOfSorts, List.getElem_cons_succ]
      exact ih j (by simpa [canonicalArgBvsOfSorts] using hi)

/-- The i-th canonical var's id follows the `$__bv{len-1-i}` scheme. -/
theorem canonicalArgBvsOfSorts_getElem_id (stys : List TermType) (i : Nat)
    (hi : i < (canonicalArgBvsOfSorts stys).length) :
    ((canonicalArgBvsOfSorts stys)[i]'hi).id
      = s!"$__bv{stys.length - 1 - i}" := by
  induction stys generalizing i with
  | nil => simp [canonicalArgBvsOfSorts] at hi
  | cons sty stys ih =>
    have hilt : i < stys.length + 1 := by
      rw [canonicalArgBvsOfSorts_length] at hi; simpa using hi
    cases i with
    | zero =>
      simp only [canonicalArgBvsOfSorts, List.getElem_cons_zero, List.length_cons]
      congr 1
    | succ j =>
      have hj : j < (canonicalArgBvsOfSorts stys).length := by
        rw [canonicalArgBvsOfSorts_length]; omega
      simp only [canonicalArgBvsOfSorts, List.getElem_cons_succ, List.length_cons]
      rw [ih j hj]
      have hnat : stys.length - 1 - j = stys.length + 1 - 1 - (j + 1) := by omega
      rw [hnat]

/-- `baseTysToTermTypes` preserves length. -/
theorem baseTysToTermTypes_length {Δ : List LMonoTy} {stys : List TermType}
    (h : baseTysToTermTypes Δ = some stys) : stys.length = Δ.length := by
  induction Δ generalizing stys with
  | nil => simp only [baseTysToTermTypes, Option.some.injEq] at h; subst h; rfl
  | cons ty tys ih =>
    simp only [baseTysToTermTypes, bind, Option.bind] at h
    cases hty : baseTyToTermType ty with
    | none => rw [hty] at h; exact absurd h (by simp)
    | some sty =>
      rw [hty] at h; simp only at h
      cases hrest : baseTysToTermTypes tys with
      | none => rw [hrest] at h; exact absurd h (by simp)
      | some srest =>
        rw [hrest] at h; simp only [Option.some.injEq] at h
        rw [← h, List.length_cons, List.length_cons, ih hrest]

/-- The i-th encoded sort is `baseTyToTermType Δ[i]`. -/
theorem baseTysToTermTypes_getElem {Δ : List LMonoTy} {stys : List TermType}
    (h : baseTysToTermTypes Δ = some stys) (i : Nat) (hi : i < Δ.length) :
    baseTyToTermType (Δ[i]'hi) = some (stys[i]'(by rw [baseTysToTermTypes_length h]; exact hi)) := by
  induction Δ generalizing stys i with
  | nil => simp at hi
  | cons ty tys ih =>
    simp only [baseTysToTermTypes, bind, Option.bind] at h
    cases hty : baseTyToTermType ty with
    | none => rw [hty] at h; exact absurd h (by simp)
    | some sty =>
      rw [hty] at h; simp only at h
      cases hrest : baseTysToTermTypes tys with
      | none => rw [hrest] at h; exact absurd h (by simp)
      | some srest =>
        rw [hrest] at h; simp only [Option.some.injEq] at h; subst h
        cases i with
        | zero => simp only [List.getElem_cons_zero, hty]
        | succ j =>
          simp only [List.length_cons] at hi
          simp only [List.getElem_cons_succ]
          exact ih hrest j (by omega)

/-- **Canonical formals are well-formed.** Whenever `canonicalArgBvs` succeeds, its result
    satisfies `BVarCtxWF` — success already witnesses that every formal type encoded. -/
theorem canonical_bvarCtxWF {Δ : List LMonoTy} {bvs : TermVarCtx}
    (h : canonicalArgBvs Δ = .ok bvs) :
    BVarCtxWF Δ bvs := by
  simp only [canonicalArgBvs] at h
  split at h
  · rename_i stys hstys
    simp only [Except.ok.injEq] at h; subst h
    have hlen_ss : stys.length = Δ.length := baseTysToTermTypes_length hstys
    refine ⟨?_, ?_, ?_⟩
    · rw [canonicalArgBvsOfSorts_length]; exact hlen_ss.symm
    · intro i hi
      have hi' : i < (canonicalArgBvsOfSorts stys).length := by
        rw [canonicalArgBvsOfSorts_length, hlen_ss]; exact hi
      rw [canonicalArgBvsOfSorts_getElem_ty stys i hi', baseTysToTermTypes_getElem hstys i hi]
    · intro i hi
      rw [canonicalArgBvsOfSorts_getElem_id stys i hi, canonicalArgBvsOfSorts_length]
  · exact absurd h (by simp)

/-! ## The per-`FnDef` encoder step (the FnDef → SMT map)

`FnDef.encodeToIF` runs `toSMTTerm` on the bvar-lifted body, so it is partial (`Except`). A defined
function's SMT construct is a `define-fun` (the `IF`), and its `declare-fun` signature is the derived
`IF.toUF`, so no separate UF encoder is needed. The return-sort and body encodings are both monadic:
an unencodable return type propagates as an `.error`. -/

/-- **`d`'s emitted IF** — the FnDef→IF encoder step (`define-fun`-level); the `declare-fun`
    signature is the derived `(encodeToIF d).toUF`. PARTIAL: encoding can fail on a non-base return
    type or a non-encodable body (real constants / out-of-range bvars / non-encodable quantifier
    types), all excluded when `d` is well-typed. Argument types, return type, and body all fail
    monadically. -/
def _root_.FnDef.encodeToIF (d : FnDef) : Except Format IF := do
  let bvs ← canonicalArgBvs d.argTys
  let some out := baseTyToTermType d.retTy
    | .error f!"FnDef.encodeToIF: non-base return type {repr d.retTy}"
  let body ← toSMTTerm bvs d.body
  .ok ⟨d.name, bvs, out, body⟩

/-! ## Encoder correctness: `encodeToIF` succeeds, and inverting its output

Totality (`encodeToIF_succeeds`) comes from well-formedness: all argument types base (`FnDef.WF`)
⇒ `canonicalArgBvs` succeeds; return type base (`HasSimpType_base` of `WFIn`) ⇒ the sort check
passes; the body is `HasSimpType`-well-typed (`WFIn`) ⇒ `toSMTTerm` succeeds
(`toSMTTerm_succeeds`). Inversion (`encodeToIF_ok_inv`) reads the four syntactic facts back off a
produced `f` — name / body-bridge / return-sort / bvar-context — which the syntactic
`FnDef.EncodedBySyn` core packages for the model transfer. -/

/-- All base types in a list ⇒ the list encodes (`baseTysToTermTypes` succeeds). -/
theorem baseTysToTermTypes_isSome_of_allBase {Δ : List LMonoTy}
    (hbase : ∀ t ∈ Δ, LExpr.MonoTyIsBase t) :
    ∃ stys, baseTysToTermTypes Δ = some stys := by
  induction Δ with
  | nil => exact ⟨[], rfl⟩
  | cons ty tys ih =>
    obtain ⟨sty, hsty⟩ := MonoTyIsBase_baseTyToTermType (hbase ty (by simp))
    obtain ⟨srest, hsrest⟩ := ih (fun t ht => hbase t (by simp [ht]))
    exact ⟨sty :: srest, by simp only [baseTysToTermTypes, hsty, hsrest, bind, Option.bind]⟩

/-- **`canonicalArgBvs` succeeds** when all formal types are base (`d.WF`). -/
theorem canonicalArgBvs_succeeds {Δ : List LMonoTy}
    (hbase : ∀ t ∈ Δ, LExpr.MonoTyIsBase t) :
    ∃ bvs, canonicalArgBvs Δ = .ok bvs := by
  obtain ⟨stys, hstys⟩ := baseTysToTermTypes_isSome_of_allBase hbase
  exact ⟨canonicalArgBvsOfSorts stys, by simp only [canonicalArgBvs, hstys]⟩

/-- **`encodeToIF` succeeds** on a well-formed, well-typed definition. Given `d.WF`
    (formal types base) and `d.WFIn Φ Ψ` (body `HasSimpType`-typed against WF contexts),
    the encoder produces some `IF`. The `IF`'s shape is exposed: its formals are
    `canonicalArgBvs`'s output, its `out` the encoded return sort, its `body` the
    `toSMTTerm` of `d.body`. -/
theorem encodeToIF_succeeds {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (d : FnDef)
    (hwf : d.WF) (hbody : d.WFIn Φ Ψ)
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) :
    ∃ bvs out body,
      canonicalArgBvs d.argTys = .ok bvs ∧
      baseTyToTermType d.retTy = some out ∧
      toSMTTerm bvs d.body = .ok body ∧
      d.encodeToIF = .ok ⟨d.name, bvs, out, body⟩ := by
  -- argument context encodes (from `d.WF`)
  obtain ⟨bvs, hbvs⟩ := canonicalArgBvs_succeeds hwf
  -- return sort encodes (from `HasSimpType_base` of the body typing)
  obtain ⟨out, hout⟩ := MonoTyIsBase_baseTyToTermType (HasSimpType_base hbody)
  -- body encodes (from `toSMTTerm_succeeds`, using the bvar-context WF from `hbvs`)
  have hbwf : BVarCtxWF d.argTys bvs := canonical_bvarCtxWF hbvs
  have hsucc := toSMTTerm_succeeds hbody huwf hψwf hbwf
  cases hbody_ok : toSMTTerm bvs d.body with
  | error e => rw [hbody_ok] at hsucc; exact hsucc.elim
  | ok body =>
    refine ⟨bvs, out, body, hbvs, hout, hbody_ok, ?_⟩
    simp only [FnDef.encodeToIF, hbvs, hout, hbody_ok, bind, Except.bind]

/-- **Inversion of `encodeToIF`.** If encoding produced `f`, then each of the three
    monadic binds succeeded and `f` is exactly `⟨d.name, f.args, f.out, f.body⟩` with
    `f.args = canonicalArgBvs`'s output, `f.out` the encoded return sort, and `f.body`
    the `toSMTTerm` of `d.body`. -/
theorem encodeToIF_ok_inv {d : FnDef} {f : IF} (hf : d.encodeToIF = .ok f) :
    f.id = d.name ∧
    canonicalArgBvs d.argTys = .ok f.args ∧
    baseTyToTermType d.retTy = some f.out ∧
    toSMTTerm f.args d.body = .ok f.body := by
  simp only [FnDef.encodeToIF, bind, Except.bind] at hf
  -- peel the `canonicalArgBvs` bind
  cases hbvs : canonicalArgBvs d.argTys with
  | error e => rw [hbvs] at hf; simp at hf
  | ok bvs =>
    rw [hbvs] at hf; simp only at hf
    -- peel the return-sort match
    cases hout : baseTyToTermType d.retTy with
    | none => rw [hout] at hf; simp at hf
    | some out =>
      rw [hout] at hf; simp only at hf
      -- peel the `toSMTTerm` bind
      cases hbody : toSMTTerm bvs d.body with
      | error e => rw [hbody] at hf; simp at hf
      | ok body =>
        rw [hbody] at hf; simp only [Except.ok.injEq] at hf
        subst hf
        refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp only [] <;> assumption

/-! ## Reified SMT program (the solver-consumable artifact)

The encoder targets a first-class SMT program — a list of `declare-fun`/`define-fun`/`assert`
commands. This is what makes the top-level statement faithful: the theorem can name "the SMT program
the solver sees" and derive its contexts from it (`SMTProgram.ctx`) exactly as a solver would.

Minimal by design: `UF`/`IF`/`Term` are reused verbatim from `DL/SMT`. -/

/-- An SMT-LIB command. Mirrors production's `declare-fun` / `define-fun` / `assert` buckets.
    `declareFun` carries a full `UF` (opaque fvar / function declaration); `defineFun`
    carries an `IF` (whose `IF.toUF` is the derived declared signature); `assert` an
    assumption or the obligation. -/
inductive SMTCommand where
  | declareFun (u : UF)
  | defineFun  (f : IF)
  | assert     (t : Term)
  /-- `check-sat`: query whether the current assertion set (modulo the `define-fun` preamble) is
      satisfiable; a pure QUERY that leaves the accumulated context unchanged. -/
  | checkSat
  /-- `check-sat-assuming`: query with `lits` as TRANSIENT extra assumptions in scope for THIS query
      only; they are not folded into the persistent assertion set. Push the block once, query under
      different literals. -/
  | checkSatAssuming (lits : List Term)
  deriving Repr, Inhabited

/-- A reified SMT program: an ordered list of commands (append order = emission order,
    callee-before-caller for `defineFun`s). -/
abbrev SMTProgram := List SMTCommand

/-- The SMT-side contexts a solver accumulates from a program: declared function
    signatures (`ufs`), interpreted-function bodies (`fs`), and asserted terms (`assertions`).
    Exactly the tuple the relational layer's per-function bridges consume. -/
structure SMTCtx where
  ufs  : UFCtx := []
  fs   : IFs := []
  assertions : List Term := []
  deriving Inhabited

/-- Fold one command into the accumulated SMT contexts. A `defineFun f` contributes to
    BOTH `ufs` (via `f.toUF` — the function is declared) AND `fs` (its body is defined),
    mirroring how a solver treats a `define-fun`. -/
def SMTCtx.step (c : SMTCtx) : SMTCommand → SMTCtx
  | .declareFun u => { c with ufs := c.ufs ++ [u] }
  | .defineFun f  => { c with ufs := c.ufs ++ [f.toUF], fs := c.fs ++ [f] }
  | .assert t     => { c with assertions := c.assertions ++ [t] }
  -- checks are pure QUERIES: they leave `(ufs, fs, assertions)` untouched. In particular a
  -- `checkSatAssuming`'s literals are transient and never enter `assertions`.
  | .checkSat            => c
  | .checkSatAssuming _  => c

/-- **Contexts read off an SMT program**, as a solver would: fold the commands
    left-to-right accumulating `(ufs, fs, assertions)`. -/
def SMTProgram.ctx (P : SMTProgram) : SMTCtx :=
  P.foldl SMTCtx.step {}

/-! ## SMT-program well-formedness (the "legal SMT-LIB script" conditions)

Prefix form: each command is checked against the context accumulated by the commands before it —
declare-before-use, exactly as a solver reads a script top-to-bottom. A body/assertion may
reference only functions already declared; forward references are rejected.

`defineFun f` bodies type-check against the context before `f` (not including `f.toUF`): production
emits a `define-fun` only for non-recursive functions, and encodes even a non-recursive body before
its own UF is committed. So an `IF` body never references itself; recursion lives entirely in the
UF+axioms (`declareFun` + `assert`) path.

The final-whole-program facts the relational layer consumes (`UFCtxWF (SMTProgram.ctx P).ufs` and
per-`IF` type-checking at the final `ufs`) are derived from this prefix condition via positive
monotonicity (`toSMTTerm` needs no `ufs`; `Term.typeCheck` tests `∈ ufs` positively, so
prefix ⊆ final preserves success) plus nodup-accumulation. -/

/-- Well-formedness of one command against the context accumulated so far: fresh,
    non-reserved id for declarations/definitions; a `defineFun` body type-checking at
    its signature against the PRIOR `ufs` (before `f` — non-recursive); an assertion
    type-checking to `.bool`. -/
def SMTCtx.cmdWF (c : SMTCtx) : SMTCommand → Prop
  | .declareFun u =>
      u.id ∉ c.ufs.map (·.id) ∧ (∀ n : Nat, u.id ≠ s!"$__bv{n}")
  | .defineFun f =>
      f.id ∉ c.ufs.map (·.id) ∧ (∀ n : Nat, f.id ≠ s!"$__bv{n}") ∧
      Term.typeCheck ⟨[], c.ufs, f.args⟩ f.body = .ok f.out
  | .assert t =>
      Term.typeCheck ⟨[], c.ufs, []⟩ t = .ok .bool
  -- `check-sat` queries the accumulated assertions — always well-formed.
  | .checkSat => True
  -- `check-sat-assuming`'s transient literals must each type-check to `.bool` at the current `ufs`.
  | .checkSatAssuming lits =>
      ∀ t ∈ lits, Term.typeCheck ⟨[], c.ufs, []⟩ t = .ok .bool

/-- **Prefix well-formedness from a starting context.** Each command is `cmdWF` against
    the context accumulated by its predecessors; the tail is checked against the context
    extended by the head. This is the faithful declare-before-use condition. -/
def SMTProgramWFfrom : SMTProgram → SMTCtx → Prop
  | [], _ => True
  | cmd :: rest, c => c.cmdWF cmd ∧ SMTProgramWFfrom rest (c.step cmd)

/-- **A well-formed SMT program** — legal as a solver script: `SMTProgramWFfrom` from the
    empty context. -/
def SMTProgramWF (P : SMTProgram) : Prop := SMTProgramWFfrom P {}

/-! ## Monotonicity: type-checking survives extending `ufs`

`Term.typeCheck` consults `ufs` in exactly one place — the `.uf` case, via the positive test
`sig ∈ ufs`. So appending UFs can never break an existing type-check:
`sig ∈ ufs → sig ∈ ufs ++ us` (`mem_append_left`). This is the "prefix ⊆ final" lift the three
derived theorems rest on. Proved by the mutual functional-induction eliminator
`Term.typeCheck.induct`. -/

/-- **Type-checking is monotone in `ufs`** (mutual with the args version, via the
    functional-induction eliminator with the args motive set to args-monotonicity).
    Extending the UF context with `us` on the right preserves every successful
    type-check. The ONLY case that touches `ufs` is `.uf` — a positive `∈ ufs` test,
    lifted by `mem_append_left`; every other case just threads the IHs. -/
theorem typeCheck_mono (ufs us : UFCtx) (Γ : List TermVar) (tm : Term) {τ : TermType}
    (h : Term.typeCheck ⟨[], ufs, Γ⟩ tm = .ok τ) :
    Term.typeCheck ⟨[], (ufs ++ us), Γ⟩ tm = .ok τ := by
  exact typeCheck_ufs_mono_append h

/-! ## Monotonicity: `HasSimpType` survives extending `Φ`/`Ψ`

The Lambda-side dual of `typeCheck_mono`. `HasSimpType`/`AppSpine` consult the contexts in exactly
two places — the positive membership tests `AppSpine.fvar`'s `(f.name, τ) ∈ Φ` and `AppSpine.fnOp`'s
`(o.name, oty) ∈ Ψ`. So appending entries on the right can never break a derivation: each
membership lifts by `List.mem_append_left`, every other case just re-applies the constructor to the
lifted IHs. This is the "prefix ⊆ full" lift by which the order-free relational triangle's
full-context inputs (`FnDefsWF P.Φ P.Ψ …`, `varDefsWF`, `assumptionsWF`, `obligationWF`) are derived
from the prefix `OblProgramWFfrom` contract. Mutual structural recursion over the derivation,
mirroring `HasSimpType_base`/`AppSpine_base`. -/
mutual
theorem HasSimpType_mono {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {τ : LMonoTy} (Φ' : FVarCtx) (Ψ' : FnCtx)
    (he : LExpr.HasSimpType Φ Ψ Δ e τ) :
    LExpr.HasSimpType (Φ ++ Φ') (Ψ ++ Ψ') Δ e τ := by
  match he with
  | .const c hbase => exact .const c hbase
  | .bvar i t hlook hbase => exact .bvar i t hlook hbase
  | .app fn arg rty hspine => exact .app fn arg rty (AppSpine_mono Φ' Ψ' hspine)
  | .fvarNullary f t rty hspine => exact .fvarNullary f t rty (AppSpine_mono Φ' Ψ' hspine)
  | .ite c t t' d hc ht he_ =>
    exact .ite c t t' d (HasSimpType_mono Φ' Ψ' hc) (HasSimpType_mono Φ' Ψ' ht)
      (HasSimpType_mono Φ' Ψ' he_)
  | .eq e1 e2 t hbase he1 he2 =>
    exact .eq e1 e2 t hbase (HasSimpType_mono Φ' Ψ' he1) (HasSimpType_mono Φ' Ψ' he2)
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody =>
    exact .quant qty qbody qk qname qtr qτtr hbase (HasSimpType_mono Φ' Ψ' htr)
      (HasSimpType_mono Φ' Ψ' hbody)

theorem AppSpine_mono {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {acc : List LMonoTy} {rty : LMonoTy} (Φ' : FVarCtx) (Ψ' : FnCtx)
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    LExpr.AppSpine (Φ ++ Φ') (Ψ ++ Ψ') Δ e acc rty := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    exact .app fn arg aty acc' rty (HasSimpType_mono Φ' Ψ' harg) (AppSpine_mono Φ' Ψ' hrest)
  | .fvar f t acc' rty hmem hcollect hbase =>
    exact .fvar f t acc' rty (List.mem_append_left Φ' hmem) hcollect hbase
  | .op o oty acc' rty hop hcollect =>
    exact .op o oty acc' rty hop hcollect
  | .fnOp o oty acc' rty hmem hnpre hcollect hbase =>
    exact .fnOp o oty acc' rty (List.mem_append_left Ψ' hmem) hnpre hcollect hbase
termination_by structural hspine
end

/-! ## Fold-accumulation lemmas: lift the per-prefix `cmdWF` facts to the final context

`SMTProgram.ctx` is `foldl SMTCtx.step`. The `ufs` only ever grows by append, so any fact
established at a prefix `ufs` lifts to the final `ufs` by `typeCheck_mono` (for type-checks) or
`mem_append_left`/`Nodup`-of-append (for the WF fields). -/

/-- The invariant threaded through the fold: the three final-context facts, stated for
    an arbitrary accumulated context. Carried as BOTH hypothesis (for `c`) and
    conclusion (for the fold), so the induction preserves it. -/
structure SMTCtx.Good (c : SMTCtx) : Prop where
  ufCtxWF : UFCtxWF c.ufs
  fsTC : ∀ f ∈ c.fs, Term.typeCheck ⟨[], c.ufs, f.args⟩ f.body = .ok f.out
  assertsTC : ∀ t ∈ c.assertions, Term.typeCheck ⟨[], c.ufs, []⟩ t = .ok .bool

/-- One step preserves `Good`: extending a good `c` by a well-formed command
    (`c.cmdWF cmd`) yields a good `c.step cmd`. The existing `fs`/assertions facts are
    lifted across the appended `ufs` by `typeCheck_mono`; the new element is checked
    at `c.ufs` (by `cmdWF`) and lifted the same way; `UFCtxWF` extends by the freshness
    fields of `cmdWF`. -/
theorem SMTCtx.Good.step {c : SMTCtx} {cmd : SMTCommand}
    (hc : c.Good) (hcmd : c.cmdWF cmd) : (c.step cmd).Good := by
  cases cmd with
  | declareFun u =>
    obtain ⟨hfresh, hnr⟩ := hcmd
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- uf_nodup
      simp only [SMTCtx.step, List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨hc.ufCtxWF.uf_nodup, by simp, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb
      exact fun heq => hfresh (heq ▸ ha)
    · -- no_reserved
      intro n
      simp only [SMTCtx.step, List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton]
      rintro (hmem | hmem)
      · exact hc.ufCtxWF.no_reserved n hmem
      · exact hnr n hmem.symm
    · -- fsTC: fs unchanged; lift to the extended ufs
      intro f hf
      simpa only [SMTCtx.step] using typeCheck_mono c.ufs [u] f.args f.body (hc.fsTC f hf)
    · -- assertsTC: assertions unchanged; lift
      intro t ht
      simpa only [SMTCtx.step] using typeCheck_mono c.ufs [u] [] t (hc.assertsTC t ht)
  | defineFun f =>
    obtain ⟨hfresh, hnr, htc⟩ := hcmd
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [SMTCtx.step, List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨hc.ufCtxWF.uf_nodup, by simp, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton, IF.toUF] at hb; subst hb
      -- `f.toUF.id = f.id` (after the `IF.toUF` simp), so `hfresh : f.id ∉ …` closes it
      exact fun heq => hfresh (heq ▸ ha)
    · intro n
      simp only [SMTCtx.step, List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton]
      rintro (hmem | hmem)
      · exact hc.ufCtxWF.no_reserved n hmem
      · exact hnr n hmem.symm
    · -- fsTC: old fs (lift) plus the new `f` (checked at `c.ufs` by `htc`, then lifted)
      intro g hg
      simp only [SMTCtx.step, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · simpa only [SMTCtx.step] using typeCheck_mono c.ufs [f.toUF] g.args g.body (hc.fsTC g hg)
      · simpa only [SMTCtx.step] using typeCheck_mono c.ufs [g.toUF] g.args g.body htc
    · intro t ht
      simpa only [SMTCtx.step] using typeCheck_mono c.ufs [f.toUF] [] t (hc.assertsTC t ht)
  | assert s =>
    refine ⟨hc.ufCtxWF, ?_, ?_⟩
    · intro f hf; simpa only [SMTCtx.step] using hc.fsTC f hf
    · -- assertions: old (unchanged ufs) plus new `s` (checked at `c.ufs` by `hcmd`)
      intro t ht
      simp only [SMTCtx.step, List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact hc.assertsTC t ht
      · exact hcmd
  -- checks leave the context UNCHANGED (`c.step _ = c`), so `Good` is preserved verbatim.
  | checkSat => exact hc
  | checkSatAssuming lits => exact hc

/-- `Good` propagates along the whole fold. -/
theorem SMTCtx.Good.fold (P : SMTProgram) :
    ∀ (c : SMTCtx), c.Good → SMTProgramWFfrom P c → (P.foldl SMTCtx.step c).Good := by
  induction P with
  | nil => intro c hc _; exact hc
  | cons cmd rest ih =>
    intro c hc hprog
    obtain ⟨hcmd, hrest⟩ := hprog
    exact ih (c.step cmd) (hc.step hcmd) hrest

/-- The empty context is `Good`. -/
theorem SMTCtx.Good.empty : SMTCtx.Good {} :=
  ⟨⟨by simp, by intro n; simp⟩, by simp, by simp⟩

/- The FINAL-context facts the relational layer consumes, DERIVED from the prefix
   condition via the `Good` fold-invariant + `typeCheck_mono`. -/

/-- The accumulated UF context of a well-formed program is `UFCtxWF`. -/
theorem SMTProgramWF.ufCtxWF {P : SMTProgram} (h : SMTProgramWF P) :
    UFCtxWF (SMTProgram.ctx P).ufs :=
  (SMTCtx.Good.fold P {} SMTCtx.Good.empty h).ufCtxWF

/-- Every emitted `IF` body type-checks at its signature against the FINAL `ufs`. -/
theorem SMTProgramWF.IFsTypeCheck {P : SMTProgram} (h : SMTProgramWF P) :
    ∀ f ∈ (SMTProgram.ctx P).fs, Term.typeCheck ⟨[], (SMTProgram.ctx P).ufs, f.args⟩ f.body = .ok f.out :=
  (SMTCtx.Good.fold P {} SMTCtx.Good.empty h).fsTC

/-- Every asserted term type-checks to `.bool` against the FINAL `ufs`. -/
theorem SMTProgramWF.assertsTypeCheck {P : SMTProgram} (h : SMTProgramWF P) :
    ∀ t ∈ (SMTProgram.ctx P).assertions, Term.typeCheck ⟨[], (SMTProgram.ctx P).ufs, []⟩ t = .ok .bool :=
  (SMTCtx.Good.fold P {} SMTCtx.Good.empty h).assertsTC

/-! ## The obligation program (the verified encoder's input)

A reified obligation program — the Lambda-side dual of `SMTProgram`, and the analog of
production's `ProofObligation` (one obligation program ↔ one `ProofObligation` ↔ one SMT query). It
is the output of the trusted pre-pass (sort + factory-materialization) and extraction (the single
fvar→bvar body lift, at the model boundary); `encode` reads it and emits an `SMTProgram` almost by
homomorphism.

Command-list form, mirroring `SMTProgram = List SMTCommand`: an ordered `List OblCommand` plus one
trailing `obligation`. Two payoffs from the symmetry with the SMT side:
  • `encode` is a per-command homomorphism (`flatMap` over `cmds`), and `encode_wf` a structural
    induction over the list;
  • the WF walk (`OblProgramWFfrom`) and the context walk (`OblCtx.step`) are the same two folds
    run SMT-side (`SMTProgramWFfrom` / `SMTProgram.ctx`).
Commands may interleave in whatever order the source obligation has; the only ordering constraint
is prefix / declare-before-use (`OblProgramWFfrom`), which is exactly SMT-LIB's and is what
`encode`'s emission preserves. The single obligation, emitted last, is kept structurally as the
`obligation` field, so it needs no WF clause and no proof.

fn-side (`.fnDecl`/`.fnDef`, `Ψ`/`opInterp`) and fvar-side (`.fvarDecl`/`.varDef`, `Φ`/`fvarVal`)
stay distinct constructors even though the SMT commands they map to are uniform, because which
consistency bridge applies depends on the source reference kind. A recursive function is a `.fnDecl`
(signature) + `.assume`s (its axioms), so a `.fnDef` body never references itself and type-checks at
the context before it, mirroring the SMT-side `defineFun`. -/

/-- One obligation-program command — the Lambda-side dual of `SMTCommand`. Declarations
    (`fnDecl`/`fvarDecl`) map to `declare-fun`; definitions (`fnDef`/`varDef`) to
    `define-fun`; assertions (`assume`/`distinct`) to `assert`. Kept fn-side vs fvar-side so the
    right consistency bridge is selected per reference kind. -/
inductive OblCommand where
  /-- Opaque / recursive-function signature → `declare-fun` (op-side). `sig` is the full
      arrow type (the `FnCtx` entry's monotype). -/
  | fnDecl   (name : String) (sig : LMonoTy)
  /-- Function definition (bvar body) → `define-fun` (op-side). Non-recursive, so the
      body type-checks at the context BEFORE this command. -/
  | fnDef    (d : FnDef)
  /-- Opaque / nondet program variable → `declare-fun` (fvar-side). -/
  | fvarDecl (name : String) (τ : LMonoTy)
  /-- `.det` variable definition → `define-fun` (fvar-side; body closed, `Δ = []`). Carries a
      `VarDef` (the fvar-side dual of `FnDef`) so the accumulator collects `varDefs` symmetric
      to `defs`. -/
  | varDef   (v : VarDef)
  /-- Asserted formula (axiom or `assume`) → `assert` (bool-typed). -/
  | assume   (e : Expression.Expr)
  /-- Distinctness group → `assert (distinct …)`; n-ary over a LIST of LExprs. Since there is no
      `distinct` LExpr operator (only the SMT `Term` one), it is its own constructor. -/
  | distinct (es : List Expression.Expr)

/-- The obligation program: an ordered command list plus the SINGLE obligation goal (emitted
    last, negated at the seam). -/
structure OblProgram where
  cmds       : List OblCommand
  obligation : Expression.Expr

/-- Context accumulator — the FULL Lambda-side dual of `SMTCtx`. Where `SMTCtx` carries
    `{ufs, fs, assertions}`, `OblCtx` carries the SAME three roles, each SPLIT by the
    fn-side/fvar-side distinction the relational layer needs:
      • declarations `ufs` ↔ `(Φ, Ψ)`   — fvar-side / fn-side declaration contexts;
      • define-fun bodies `fs : IFs` ↔ `(defs : FnDefs, varDefs : VarDefs)`  — the SMT side
        merges both into `fs`; we keep them split (different consistency bridge);
      • asserts `assertions : List Term` ↔ `(assumptions, distincts)`  — SMT merges (a
        `distinct` is a `Term`); we split (no `distinct` LExpr op).
    So `OblCtx.step` is the exact parallel of `SMTCtx.step` (a definition grows BOTH its
    declaration context AND its body list), and `OblCtx.Good` mirrors `SMTCtx.Good` field for
    field. -/
structure OblCtx where
  Φ : FVarCtx := []
  Ψ : FnCtx := []
  defs : FnDefs := []
  varDefs : VarDefs := []
  assumptions : List Expression.Expr := []
  distincts : List (List Expression.Expr) := []
  deriving Inhabited

/-- The declared source names accumulated so far (Φ then Ψ). Freshness against this is what
    accumulates to joint `Φ`/`Ψ` name-nodup (the source of `UFCtxWF`'s `uf_nodup`). -/
def OblCtx.names (c : OblCtx) : List String := c.Φ.map (·.1) ++ c.Ψ.map (·.1)

/-- Fold one command into the accumulated contexts — the exact parallel of `SMTCtx.step`:
    `fnDecl` grows `Ψ` (declaration only); `fnDef` grows BOTH `Ψ` (its signature) AND `defs`
    (its body), as `defineFun` grows both `ufs` and `fs`; `fvarDecl` grows `Φ`; `varDef`
    grows both `Φ` AND `varDefs`; `assume`/`distinct` grow the assertion lists. -/
def OblCtx.step (c : OblCtx) : OblCommand → OblCtx
  | .fnDecl name sig => { c with Ψ := c.Ψ ++ [(name, sig)] }
  | .fnDef d         => { c with Ψ := c.Ψ ++ [d.sig], defs := c.defs ++ [d] }
  | .fvarDecl name τ => { c with Φ := c.Φ ++ [(name, τ)] }
  | .varDef v        => { c with Φ := c.Φ ++ [(v.name, v.ty)], varDefs := c.varDefs ++ [v] }
  | .assume e        => { c with assumptions := c.assumptions ++ [e] }
  | .distinct es     => { c with distincts := c.distincts ++ [es] }

/-- The contexts read off the whole program (Lambda-side dual of `SMTProgram.ctx`). -/
def OblProgram.ctx (P : OblProgram) : OblCtx := P.cmds.foldl OblCtx.step {}

/-- Full free-variable context Φ (a `.varDef`'s defined variable is still a free variable —
    it just carries a defining body too). Order-incidental for the relational triangle. -/
def OblProgram.Φ (P : OblProgram) : FVarCtx := P.ctx.Φ

/-- Full function context Ψ: the `Ψ = decls ++ FnDef-sigs` shape `FnDefsWF` and the per-function
    bridges consume (interleaved here, but order-free downstream). -/
def OblProgram.Ψ (P : OblProgram) : FnCtx := P.ctx.Ψ

/-- The function definitions (op-side), for the relational layer's `defs`. Read off the fold,
    symmetric with `(SMTProgram.ctx P).fs`. -/
def OblProgram.defs (P : OblProgram) : FnDefs := P.ctx.defs

/-- The variable definitions (fvar-side), the split companion of `defs`. -/
def OblProgram.varDefs (P : OblProgram) : VarDefs := P.ctx.varDefs

/-- The asserted formulas (axioms + `assume`s), for the assertion side. -/
def OblProgram.assumptions (P : OblProgram) : List Expression.Expr := P.ctx.assumptions

/-- The distinctness groups, the split companion of `assumptions`. -/
def OblProgram.distincts (P : OblProgram) : List (List Expression.Expr) := P.ctx.distincts

/-! ## Obligation-program well-formedness (prefix / declare-before-use)

The verified encoder's input contract, in the same shape as the SMT-side `SMTProgramWF`: each
command is checked against the context accumulated by the commands before it (`OblCtx.cmdWF` + the
`OblProgramWFfrom` fold). This is the faithful declare-before-use condition, and it mirrors the
(assumed) reference imperative small-step semantics — each command is well-typed against the state
its predecessors built.

Prefix form, symmetric with `SMTProgramWFfrom`, so `encode_wf` is a structural induction over the
command list (prefix ⟹ prefix, contexts growing in lockstep). The full-context facts the order-free
relational triangle consumes (`FnDefsWF P.Φ P.Ψ P.defs`, etc.) are derived from prefix by the upward
positive monotonicity `HasSimpType_mono` (prefix ⊆ full preserves typing — the Lambda-side analog of
`typeCheck_mono`).

Name hygiene is folded into the per-command freshness checks (a declared name is fresh against
`OblCtx.names` so far, and non-reserved), which accumulate to the joint `Φ`/`Ψ` nodup that becomes
`UFCtxWF`'s `uf_nodup` — again mirroring the SMT side, where `cmdWF`'s per-command freshness
accumulates to `UFCtxWF` via the `Good` fold. The single `obligation` is checked at the final
context (it is emitted after every command, so its prefix is the full context). -/

/-- Well-formedness of one obligation command against the context accumulated so far: a
    fresh, non-reserved name for declarations/definitions; a bare `fnDecl`/`fvarDecl`
    additionally has an SMT-encodable signature (`MonoTyIsSimp` — a first-order arrow of base
    types); a `fnDef` additionally has base formal types (`d.WF`) and a body `HasSimpType`-typed
    at the PRIOR context (before its own signature — non-recursive); a `varDef` body typed at its
    declared type; an `assume` bool-typed; a `distinct` group of `≥ 2` operands sharing one base
    type (the `2 ≤` bound is SMT-LIB's). The Lambda-side dual of `SMTCtx.cmdWF`. -/
def OblCtx.cmdWF (c : OblCtx) : OblCommand → Prop
  | .fnDecl name sig =>
      name ∉ c.names ∧ (∀ n : Nat, name ≠ s!"$__bv{n}") ∧ LExpr.MonoTyIsSimp sig
  | .fnDef d =>
      d.name ∉ c.names ∧ (∀ n : Nat, d.name ≠ s!"$__bv{n}") ∧
      d.WF ∧ d.WFIn c.Φ c.Ψ
  | .fvarDecl name τ =>
      name ∉ c.names ∧ (∀ n : Nat, name ≠ s!"$__bv{n}") ∧ LExpr.MonoTyIsSimp τ
  | .varDef v =>
      v.name ∉ c.names ∧ (∀ n : Nat, v.name ≠ s!"$__bv{n}") ∧
      v.WFIn c.Φ c.Ψ
  | .assume e =>
      LExpr.HasSimpType c.Φ c.Ψ [] e (.tcons "bool" [])
  | .distinct es =>
      2 ≤ es.length ∧ ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es, LExpr.HasSimpType c.Φ c.Ψ [] e τ

/-- **Prefix well-formedness from a starting context** — the Lambda-side dual of
    `SMTProgramWFfrom`. Each command is `cmdWF` against the context accumulated by its
    predecessors; the tail is checked against the context extended by the head. -/
def OblProgramWFfrom : List OblCommand → OblCtx → Prop
  | [], _ => True
  | cmd :: rest, c => c.cmdWF cmd ∧ OblProgramWFfrom rest (c.step cmd)

/-- **The obligation program is well-formed** (the verified encoder's input contract): the
    command list is prefix-well-formed from the empty context, and the single obligation is
    a bool-typed formula at the FINAL context (its prefix, since it is emitted last). -/
structure OblProgramWF (P : OblProgram) : Prop where
  /-- Every command is well-typed against the context its predecessors built. -/
  cmdsWF : OblProgramWFfrom P.cmds {}
  /-- The obligation goal is bool-typed at the full context. -/
  obligationWF : LExpr.HasSimpType P.Φ P.Ψ [] P.obligation (.tcons "bool" [])

/-! ## Fold-accumulation for the obligation side

The Lambda-side dual of `SMTCtx.Good` and its fold, lifting the per-prefix `cmdWF` facts to the
final context. `OblProgram.ctx` is `foldl OblCtx.step`. Where the SMT side grows only `ufs` (so a
lift is a single right-append and nodup grows at the tail), here both `Φ` and `Ψ` grow, so:
  • a declared name is inserted into the middle of `Φnames ++ Ψnames` — nodup/no-reserved go
    through a `List.Perm` to `name :: names`;
  • every accumulated body-typing invariant is lifted across a one-sided context append
    (`HasSimpType_mono` with the other side empty).
Otherwise this is the exact mirror of `SMTCtx.Good`: `.step` preserves the invariant, `.fold`
propagates it, `.empty` seeds it, and the derived `OblProgramWF.*` facts read the full-context
triangle inputs off the final fold. -/

/-- One-sided `HasSimpType_mono`: append on the `Ψ` side only. -/
theorem HasSimpType_mono_Ψ {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {τ : LMonoTy} (Ψ' : FnCtx) (h : LExpr.HasSimpType Φ Ψ Δ e τ) :
    LExpr.HasSimpType Φ (Ψ ++ Ψ') Δ e τ := by
  have := HasSimpType_mono (Φ := Φ) (Ψ := Ψ) [] Ψ' h
  rwa [List.append_nil] at this

/-- One-sided `HasSimpType_mono`: append on the `Φ` side only. -/
theorem HasSimpType_mono_Φ {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {τ : LMonoTy} (Φ' : FVarCtx) (h : LExpr.HasSimpType Φ Ψ Δ e τ) :
    LExpr.HasSimpType (Φ ++ Φ') Ψ Δ e τ := by
  have := HasSimpType_mono (Φ := Φ) (Ψ := Ψ) Φ' [] h
  rwa [List.append_nil] at this

/-- Nodup transfers along a permutation to `a :: l` given `a` fresh and `l` nodup. -/
private theorem nodup_of_perm_cons {α} {l l' : List α} {a : α}
    (hp : l'.Perm (a :: l)) (ha : a ∉ l) (hl : l.Nodup) : l'.Nodup :=
  hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨ha, hl⟩)

/-- Non-membership transfers along a permutation to `a :: l`. -/
private theorem not_mem_of_perm_cons {α} {l l' : List α} {a x : α}
    (hp : l'.Perm (a :: l)) (hxa : x ≠ a) (hxl : x ∉ l) : x ∉ l' := by
  rw [hp.mem_iff]
  simp only [List.mem_cons]
  rintro (h | h)
  · exact hxa h
  · exact hxl h

/-- Growing `Ψ` by `[(a, sig)]`: the names permute to `a :: names`. -/
private theorem perm_names_growΨ (P Q : List String) (a : String) :
    (P ++ (Q ++ [a])).Perm (a :: (P ++ Q)) := by
  rw [← List.append_assoc]; exact List.perm_append_comm

/-- Growing `Φ` by `[(a, τ)]`: the names permute to `a :: names`. -/
private theorem perm_names_growΦ (P Q : List String) (a : String) :
    ((P ++ [a]) ++ Q).Perm (a :: (P ++ Q)) :=
  (List.perm_append_comm.append_right Q)

/-- A `foldr arrow` signature is `MonoTyIsSimp` when its argument types are all base and its
    return type is base — the shape of `FnDef.sig`'s type. Feeds the `Ψsimp` fact for `fnDef`
    entries (from `d.WF` + `HasSimpType_base` of `d.WFIn`). -/
theorem foldr_arrow_simp {argTys : List LMonoTy} {rty : LMonoTy}
    (harg : ∀ t ∈ argTys, LExpr.MonoTyIsBase t) (hret : LExpr.MonoTyIsBase rty) :
    LExpr.MonoTyIsSimp (List.foldr LMonoTy.arrow rty argTys) := by
  induction argTys with
  | nil => exact .base hret
  | cons a as ih =>
    exact .arrow (harg a (by simp)) (ih (fun t ht => harg t (by simp [ht])))

/-- The invariant threaded through the obligation fold — the field-for-field mirror of
    `SMTCtx.Good`, stated at an arbitrary accumulated context. `namesNodup`/`noReserved`
    mirror `UFCtxWF`'s two fields (source-side); `defsWF`/`varDefsWF` mirror `fsTC` (the
    define-fun bodies, split fn/fvar); `assumptionsWF`/`distinctsWF` mirror `assertsTC` (the
    asserts, split). Each body-typing fact is stated at the accumulated `(c.Φ, c.Ψ)`. -/
structure OblCtx.Good (c : OblCtx) : Prop where
  namesNodup : c.names.Nodup
  noReserved : ∀ n : Nat, s!"$__bv{n}" ∉ c.names
  /-- Every `Φ` entry's declared type is SMT-encodable — the reflection foundation:
      `FNameCtxWF c.Φ ufs` needs each entry to encode. From `fvarDecl`'s `MonoTyIsSimp` clause
      and (for a `.det` variable) `HasSimpType_base` of `varDef`'s `WFIn` (`ty` base ⊆ simp). -/
  Φsimp : ∀ x ∈ c.Φ, LExpr.MonoTyIsSimp x.2
  /-- Every `Ψ` entry's declared type is SMT-encodable. From `fnDecl`'s `MonoTyIsSimp` clause
      and (for a `.fnDef`) `foldr_arrow_simp` of `d.WF` + `HasSimpType_base` of `d.WFIn`. -/
  Ψsimp : ∀ x ∈ c.Ψ, LExpr.MonoTyIsSimp x.2
  defsWF : ∀ d ∈ c.defs, d.WF ∧ d.WFIn c.Φ c.Ψ
  varDefsWF : ∀ v ∈ c.varDefs, v.WFIn c.Φ c.Ψ
  assumptionsWF : ∀ e ∈ c.assumptions, LExpr.HasSimpType c.Φ c.Ψ [] e (.tcons "bool" [])
  distinctsWF : ∀ es ∈ c.distincts, ∃ τ, LExpr.MonoTyIsBase τ ∧
    ∀ e ∈ es, LExpr.HasSimpType c.Φ c.Ψ [] e τ

/-- One step preserves `Good` — the mirror of `SMTCtx.Good.step`. Declarations/definitions
    grow one context side: nodup/no-reserved go through the `perm_names_grow*` permutation to
    `name :: names`, and every accumulated body-typing invariant is lifted across the append
    by `HasSimpType_mono_Φ`/`_Ψ` (the new definition's own body, checked at the PRIOR context
    by `cmdWF`, is lifted the same way — as the SMT side lifts the new `f` across `[f.toUF]`).
    Assertions leave the contexts unchanged, so their facts need no lift. -/
theorem OblCtx.Good.step {c : OblCtx} {cmd : OblCommand}
    (hc : c.Good) (hcmd : c.cmdWF cmd) : (c.step cmd).Good := by
  cases cmd with
  | fnDecl name sig =>
    obtain ⟨hfresh, hnr, hsimp⟩ := hcmd
    have hperm : (c.step (.fnDecl name sig)).names.Perm (name :: c.names) := by
      simp only [OblCtx.names, OblCtx.step, List.map_append, List.map_cons, List.map_nil]
      exact perm_names_growΨ _ _ _
    refine ⟨nodup_of_perm_cons hperm hfresh hc.namesNodup,
      fun n => not_mem_of_perm_cons hperm (hnr n).symm (hc.noReserved n), hc.Φsimp, ?_, ?_, ?_, ?_, ?_⟩
    · -- Ψsimp: old entries (hc.Ψsimp) plus the new `(name, sig)` (from `hsimp`)
      intro x hx
      simp only [OblCtx.step, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hc.Ψsimp x hx
      · exact hsimp
    · intro d hd
      obtain ⟨hwf, hwfin⟩ := hc.defsWF d hd
      exact ⟨hwf, HasSimpType_mono_Ψ [(name, sig)] hwfin⟩
    · intro v hv; exact HasSimpType_mono_Ψ [(name, sig)] (hc.varDefsWF v hv)
    · intro e he; exact HasSimpType_mono_Ψ [(name, sig)] (hc.assumptionsWF e he)
    · intro es hes
      obtain ⟨τ, hbase, hall⟩ := hc.distinctsWF es hes
      exact ⟨τ, hbase, fun e he => HasSimpType_mono_Ψ [(name, sig)] (hall e he)⟩
  | fnDef d =>
    obtain ⟨hfresh, hnr, hdwf, hdwfin⟩ := hcmd
    have hperm : (c.step (.fnDef d)).names.Perm (d.name :: c.names) := by
      simp only [OblCtx.names, OblCtx.step, List.map_append, List.map_cons, List.map_nil,
        FnDef.sig]
      exact perm_names_growΨ _ _ _
    refine ⟨nodup_of_perm_cons hperm hfresh hc.namesNodup,
      fun n => not_mem_of_perm_cons hperm (hnr n).symm (hc.noReserved n), hc.Φsimp, ?_, ?_, ?_, ?_, ?_⟩
    · -- Ψsimp: old entries plus the new `d.sig` (a `foldr arrow`, simp by `foldr_arrow_simp`)
      intro x hx
      simp only [OblCtx.step, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hc.Ψsimp x hx
      · exact foldr_arrow_simp hdwf (HasSimpType_base hdwfin)
    · -- old defs (lift) plus the new `d` (checked at `c.Ψ` by `hdwfin`, then lifted)
      intro d' hd'
      simp only [OblCtx.step, List.mem_append, List.mem_singleton] at hd'
      rcases hd' with hd' | rfl
      · obtain ⟨hwf, hwfin⟩ := hc.defsWF d' hd'
        exact ⟨hwf, HasSimpType_mono_Ψ [d.sig] hwfin⟩
      · exact ⟨hdwf, HasSimpType_mono_Ψ [d'.sig] hdwfin⟩
    · intro v hv; exact HasSimpType_mono_Ψ [d.sig] (hc.varDefsWF v hv)
    · intro e he; exact HasSimpType_mono_Ψ [d.sig] (hc.assumptionsWF e he)
    · intro es hes
      obtain ⟨τ, hbase, hall⟩ := hc.distinctsWF es hes
      exact ⟨τ, hbase, fun e he => HasSimpType_mono_Ψ [d.sig] (hall e he)⟩
  | fvarDecl name τ =>
    obtain ⟨hfresh, hnr, hsimp⟩ := hcmd
    have hperm : (c.step (.fvarDecl name τ)).names.Perm (name :: c.names) := by
      simp only [OblCtx.names, OblCtx.step, List.map_append, List.map_cons, List.map_nil]
      exact perm_names_growΦ _ _ _
    refine ⟨nodup_of_perm_cons hperm hfresh hc.namesNodup,
      fun n => not_mem_of_perm_cons hperm (hnr n).symm (hc.noReserved n), ?_, hc.Ψsimp, ?_, ?_, ?_, ?_⟩
    · -- Φsimp: old entries plus the new `(name, τ)` (from `hsimp`)
      intro x hx
      simp only [OblCtx.step, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hc.Φsimp x hx
      · exact hsimp
    · intro d hd
      obtain ⟨hwf, hwfin⟩ := hc.defsWF d hd
      exact ⟨hwf, HasSimpType_mono_Φ [(name, τ)] hwfin⟩
    · intro v hv; exact HasSimpType_mono_Φ [(name, τ)] (hc.varDefsWF v hv)
    · intro e he; exact HasSimpType_mono_Φ [(name, τ)] (hc.assumptionsWF e he)
    · intro es hes
      obtain ⟨τ', hbase, hall⟩ := hc.distinctsWF es hes
      exact ⟨τ', hbase, fun e he => HasSimpType_mono_Φ [(name, τ)] (hall e he)⟩
  | varDef v =>
    obtain ⟨hfresh, hnr, hvwfin⟩ := hcmd
    have hperm : (c.step (.varDef v)).names.Perm (v.name :: c.names) := by
      simp only [OblCtx.names, OblCtx.step, List.map_append, List.map_cons, List.map_nil]
      exact perm_names_growΦ _ _ _
    refine ⟨nodup_of_perm_cons hperm hfresh hc.namesNodup,
      fun n => not_mem_of_perm_cons hperm (hnr n).symm (hc.noReserved n), ?_, hc.Ψsimp, ?_, ?_, ?_, ?_⟩
    · -- Φsimp: old entries plus the new `(v.name, v.ty)` (base ⊆ simp, from `WFIn`)
      intro x hx
      simp only [OblCtx.step, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hc.Φsimp x hx
      · exact .base (HasSimpType_base hvwfin)
    · intro d hd
      obtain ⟨hwf, hwfin⟩ := hc.defsWF d hd
      exact ⟨hwf, HasSimpType_mono_Φ [(v.name, v.ty)] hwfin⟩
    · -- old varDefs (lift) plus the new `v` (checked at `c.Φ` by `hvwfin`, then lifted)
      intro v' hv'
      simp only [OblCtx.step, List.mem_append, List.mem_singleton] at hv'
      rcases hv' with hv' | rfl
      · exact HasSimpType_mono_Φ [(v.name, v.ty)] (hc.varDefsWF v' hv')
      · exact HasSimpType_mono_Φ [(v'.name, v'.ty)] hvwfin
    · intro e he; exact HasSimpType_mono_Φ [(v.name, v.ty)] (hc.assumptionsWF e he)
    · intro es hes
      obtain ⟨τ, hbase, hall⟩ := hc.distinctsWF es hes
      exact ⟨τ, hbase, fun e he => HasSimpType_mono_Φ [(v.name, v.ty)] (hall e he)⟩
  | assume e =>
    -- contexts unchanged; existing facts hold verbatim, new `e` from `hcmd`
    refine ⟨hc.namesNodup, hc.noReserved, hc.Φsimp, hc.Ψsimp, hc.defsWF, hc.varDefsWF, ?_, hc.distinctsWF⟩
    intro e' he'
    simp only [OblCtx.step, List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact hc.assumptionsWF e' he'
    · exact hcmd
  | distinct es =>
    refine ⟨hc.namesNodup, hc.noReserved, hc.Φsimp, hc.Ψsimp, hc.defsWF, hc.varDefsWF,
      hc.assumptionsWF, ?_⟩
    intro es' hes'
    simp only [OblCtx.step, List.mem_append, List.mem_singleton] at hes'
    rcases hes' with hes' | rfl
    · exact hc.distinctsWF es' hes'
    · exact hcmd.2

/-- `Good` propagates along the whole fold — the mirror of `SMTCtx.Good.fold`. -/
theorem OblCtx.Good.fold (cmds : List OblCommand) :
    ∀ (c : OblCtx), c.Good → OblProgramWFfrom cmds c → (cmds.foldl OblCtx.step c).Good := by
  induction cmds with
  | nil => intro c hc _; exact hc
  | cons cmd rest ih =>
    intro c hc hprog
    obtain ⟨hcmd, hrest⟩ := hprog
    exact ih (c.step cmd) (hc.step hcmd) hrest

/-- The empty context is `Good`. -/
theorem OblCtx.Good.empty : OblCtx.Good {} :=
  ⟨by simp [OblCtx.names], by intro n; simp [OblCtx.names], by simp, by simp, by simp, by simp,
   by simp, by simp⟩

/- The FINAL-context facts the ORDER-FREE relational triangle consumes, DERIVED from the
   prefix `OblProgramWF` contract via the `Good` fold-invariant + `HasSimpType_mono`. These are
   the Lambda-side analogs of `SMTProgramWF.ufCtxWF`/`IFsTypeCheck`/`assertsTypeCheck`. -/

/-- The accumulated context of a well-formed obligation program is `Good`. -/
theorem OblProgramWF.ctxGood {P : OblProgram} (h : OblProgramWF P) : P.ctx.Good :=
  OblCtx.Good.fold P.cmds {} OblCtx.Good.empty h.cmdsWF

/-- **Source-name hygiene at the full context** — the `nodup` + `no_reserved` that the
    encoding boundary turns into `UFCtxWF ufs`. -/
theorem OblProgramWF.namesNodup {P : OblProgram} (h : OblProgramWF P) :
    (P.Φ.map (·.1) ++ P.Ψ.map (·.1)).Nodup :=
  h.ctxGood.namesNodup

theorem OblProgramWF.noReserved {P : OblProgram} (h : OblProgramWF P) :
    ∀ n : Nat, s!"$__bv{n}" ∉ (P.Φ.map (·.1) ++ P.Ψ.map (·.1)) :=
  h.ctxGood.noReserved

/-- **Every function definition is `WFIn` at the FULL context** — exactly `FnDefsWF P.Φ P.Ψ
    P.defs`, the collection premise the model transfer consumes. -/
theorem OblProgramWF.defsWF {P : OblProgram} (h : OblProgramWF P) :
    FnDefsWF P.Φ P.Ψ P.defs :=
  fun d hd => (h.ctxGood.defsWF d hd).2

/-- **Every function definition's signature is encodable** (`d.WF`) — the `defsSigWF` premise. -/
theorem OblProgramWF.defsSigWF {P : OblProgram} (h : OblProgramWF P) :
    ∀ d ∈ P.defs, d.WF :=
  fun d hd => (h.ctxGood.defsWF d hd).1

/-- **Every variable definition is `WFIn` at the FULL context** — `VarDefsWF P.Φ P.Ψ
    P.varDefs`, the fvar-side collection premise. -/
theorem OblProgramWF.varDefsWF {P : OblProgram} (h : OblProgramWF P) :
    VarDefsWF P.Φ P.Ψ P.varDefs :=
  h.ctxGood.varDefsWF

/-- **Every assumption is bool-typed at the FULL context.** -/
theorem OblProgramWF.assumptionsWF {P : OblProgram} (h : OblProgramWF P) :
    ∀ e ∈ P.assumptions, LExpr.HasSimpType P.Φ P.Ψ [] e (.tcons "bool" []) :=
  h.ctxGood.assumptionsWF

/-- **Every distinctness group shares a base type at the FULL context.** -/
theorem OblProgramWF.distinctsWF {P : OblProgram} (h : OblProgramWF P) :
    ∀ es ∈ P.distincts, ∃ τ, LExpr.MonoTyIsBase τ ∧
      ∀ e ∈ es, LExpr.HasSimpType P.Φ P.Ψ [] e τ :=
  h.ctxGood.distinctsWF

/- Membership fold invariants: `defs` and `Ψ` (resp. `varDefs` and `Φ`) grow in LOCKSTEP under
   `OblCtx.step` (a `.fnDef d` step appends `d.sig` to `Ψ` and `d` to `defs` together; a
   `.varDef v` step appends `(v.name, v.ty)` to `Φ` and `v` to `varDefs`). So every definition's
   signature is a context entry — the membership the seam's per-function bridges consume. -/

/-- Each collected `fnDef`'s signature is in `Ψ` (fold invariant, monotone). -/
theorem foldl_step_defs_sig (cmds : List OblCommand) :
    ∀ (c : OblCtx), (∀ d ∈ c.defs, d.sig ∈ c.Ψ) →
      ∀ d ∈ (cmds.foldl OblCtx.step c).defs, d.sig ∈ (cmds.foldl OblCtx.step c).Ψ := by
  induction cmds with
  | nil => intro c hc; exact hc
  | cons cmd rest ih =>
    intro c hc
    refine ih (c.step cmd) ?_
    intro d hd
    cases cmd <;> simp only [OblCtx.step] at hd ⊢ <;>
      first
        | exact List.mem_append_left _ (hc d hd)  -- fnDecl: Ψ grows, defs unchanged
        | (simp only [List.mem_append, List.mem_singleton] at hd ⊢
           rcases hd with hd | rfl
           · exact Or.inl (hc d hd)
           · exact Or.inr rfl)                     -- fnDef: both grow in lockstep
        | exact hc d hd                            -- fvarDecl/varDef/assume/distinct: unchanged

/-- Each collected `varDef`'s `(name, ty)` is in `Φ` (fold invariant, monotone). -/
theorem foldl_step_varDefs_Φ (cmds : List OblCommand) :
    ∀ (c : OblCtx), (∀ v ∈ c.varDefs, (v.name, v.ty) ∈ c.Φ) →
      ∀ v ∈ (cmds.foldl OblCtx.step c).varDefs, (v.name, v.ty) ∈ (cmds.foldl OblCtx.step c).Φ := by
  induction cmds with
  | nil => intro c hc; exact hc
  | cons cmd rest ih =>
    intro c hc
    refine ih (c.step cmd) ?_
    intro v hv
    cases cmd <;> simp only [OblCtx.step] at hv ⊢ <;>
      first
        | exact List.mem_append_left _ (hc v hv)  -- fvarDecl: Φ grows, varDefs unchanged
        | (simp only [List.mem_append, List.mem_singleton] at hv ⊢
           rcases hv with hv | rfl
           · exact Or.inl (hc v hv)
           · exact Or.inr rfl)                     -- varDef: both grow in lockstep
        | exact hc v hv                            -- fnDecl/fnDef/assume/distinct: unchanged

/-- **Each `fnDef`'s signature is in `Ψ`** — the membership the model transfer's op branch consumes. -/
theorem OblProgram.defs_sig_mem (P : OblProgram) : ∀ d ∈ P.defs, d.sig ∈ P.Ψ :=
  foldl_step_defs_sig P.cmds {} (by intro d hd; simp at hd)

/-- **Each `varDef`'s `(name, ty)` is in `Φ`.** The membership the fvar branch wants. -/
theorem OblProgram.varDefs_Φ_mem (P : OblProgram) : ∀ v ∈ P.varDefs, (v.name, v.ty) ∈ P.Φ :=
  foldl_step_varDefs_Φ P.cmds {} (by intro v hv; simp at hv)

/-! ## The encoder `encode : OblProgram → Except Format SMTProgram`

The encoder itself — a per-command homomorphism into `SMTProgram`: `encode` maps each `OblCommand`
to one `SMTCommand`, lists them in order, and appends the single trailing `assert (not obligation)`.
It is partial (`Except`) — a non-encodable type/body fails monadically — but on a well-formed input
every step succeeds (`encode_succeeds`).

No context threading: `toSMTTerm` takes no `ufs`, definition bodies are closed (`toSMTTerm []`) or
bvar-lifted inside `encodeToIF`, and declared signatures encode purely from their arrow type. So
`encode` is a plain `mapM`/flatten — the source of the clean `encode_wf` structural induction,
where the two `Good` invariants line up step by step. -/

/-- Build a `declare-fun` UF from a name and its (arrow) type — the shared signature encoder
    for `fnDecl`/`fvarDecl`. Decomposes the arrow type by `collectArrowTy` and encodes the
    argument/return sorts, exactly as `buildAppHead` does for a `.fvar`/UDF application head
    (so a declaration and its uses encode to the SAME `UF` signature). Partial: fails on a
    non-base argument/return type. -/
def encodeSig (name : String) (ty : LMonoTy) : Except Format UF :=
  let (argTys, rty) := collectArrowTy ty
  match baseTyToTermType rty, baseTysToTermTypes argTys with
  | some smtRty, some smtArgTys => .ok ⟨name, smtArgTys, smtRty⟩
  | _, _ => .error f!"encodeSig: cannot encode signature {repr ty} for {name}"

/-- Under `MonoTyIsSimp`, `collectArrowTy` splits into all-base arg types and a base return
    type — the semantic-encodability content, feeding `encodeSig_succeeds`. -/
theorem collectArrowTy_simp_base {ty : LMonoTy} (h : LExpr.MonoTyIsSimp ty) :
    (∀ t ∈ (collectArrowTy ty).1, LExpr.MonoTyIsBase t) ∧
    LExpr.MonoTyIsBase (collectArrowTy ty).2 := by
  induction h with
  | base hb =>
    -- a base type has no arrow head, so `collectArrowTy` returns `([], ty)`
    cases hb <;>
      exact ⟨by intro t ht; simp [collectArrowTy] at ht, by constructor⟩
  | arrow haty hrty ih =>
    obtain ⟨iharg, ihret⟩ := ih
    refine ⟨?_, ?_⟩
    · intro t ht
      simp only [collectArrowTy, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact haty
      · exact iharg t ht
    · simpa only [collectArrowTy] using ihret

/-- **`encodeSig` succeeds** on an SMT-encodable signature (`MonoTyIsSimp`) — the declaration
    analog of `encodeToIF_succeeds`. -/
theorem encodeSig_succeeds {name : String} {ty : LMonoTy} (h : LExpr.MonoTyIsSimp ty) :
    ∃ u, encodeSig name ty = .ok u := by
  obtain ⟨harg, hret⟩ := collectArrowTy_simp_base h
  obtain ⟨smtRty, hrty⟩ := MonoTyIsBase_baseTyToTermType hret
  obtain ⟨smtArgTys, hargs⟩ := baseTysToTermTypes_isSome_of_allBase harg
  refine ⟨⟨name, smtArgTys, smtRty⟩, ?_⟩
  simp only [encodeSig]
  -- destructure `collectArrowTy ty` so the `let` and the two matches reduce
  obtain ⟨aTys, rTy, hcol⟩ : ∃ a r, collectArrowTy ty = (a, r) := ⟨_, _, rfl⟩
  rw [hcol] at hrty hargs
  simp only [hcol, hrty, hargs]

/-- **Inversion of `encodeSig`.** A successful encoding pins the UF's id and exposes the two
    encoding equalities `FNameCtxWF`'s `args_eq`/`out_eq` want (stated over `collectArrowTy`). -/
theorem encodeSig_ok_inv {name : String} {ty : LMonoTy} {u : UF}
    (h : encodeSig name ty = .ok u) :
    u.id = name ∧
    baseTysToTermTypes (collectArrowTy ty).1 = some u.args ∧
    baseTyToTermType (collectArrowTy ty).2 = some u.out := by
  simp only [encodeSig] at h
  obtain ⟨aTys, rTy, hcol⟩ : ∃ a r, collectArrowTy ty = (a, r) := ⟨_, _, rfl⟩
  rw [hcol] at h
  simp only at h
  cases hrty : baseTyToTermType rTy with
  | none => rw [hrty] at h; simp at h
  | some smtRty =>
    cases hargs : baseTysToTermTypes aTys with
    | none => rw [hrty, hargs] at h; simp at h
    | some smtArgs =>
      rw [hrty, hargs] at h; simp only [Except.ok.injEq] at h; subst h
      exact ⟨rfl, by rw [hcol]; exact hargs, by rw [hcol]; exact hrty⟩

/-- `lookupUF` returns the (unique, by id-nodup) UF present with the given id. -/
theorem lookupUF_canonical {ufs : UFCtx} {name : String} {u : UF}
    (hmem : u ∈ ufs) (hid : u.id = name) (hnd : (ufs.map (·.id)).Nodup) :
    lookupUF ufs name = some u := by
  subst hid
  simp only [lookupUF]
  induction ufs with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hndtl⟩ := hnd
    simp only [List.mem_cons] at hmem
    rw [List.find?_cons]
    rcases hmem with rfl | hmem
    · simp
    · have hne : (hd.id == u.id) = false := by
        simp only [beq_eq_false_iff_ne]; intro heq
        exact hnotin (heq ▸ List.mem_map_of_mem (f := (·.id)) hmem)
      rw [hne]; exact ih hmem hndtl

/-- **`FNameCtxWF` builder.** A name context resolves against `ufs` whenever every entry's
    canonical `encodeSig` UF is present in `ufs` and the `ufs` ids are unique: resolution is
    `lookupUF_canonical`, and the signature equalities come from `encodeSig_ok_inv`. This is
    the reflection lemma both `encode_succeeds` (totality) and `encode_wf` (type-checking)
    rest on — instantiated at the REAL emitted context `(SMTProgram.ctx (encode P)).ufs`. -/
theorem fnameCtxWF_of_mem {Φ : FNameCtx} {ufs : UFCtx}
    (hmem : ∀ x ∈ Φ, ∃ u, encodeSig x.1 x.2 = .ok u ∧ u ∈ ufs)
    (hnd : (ufs.map (·.id)).Nodup) :
    FNameCtxWF Φ ufs := by
  refine ⟨?_, ?_, ?_⟩
  · intro name τ hmemΦ
    obtain ⟨u, henc, humem⟩ := hmem (name, τ) hmemΦ
    have hid := (encodeSig_ok_inv henc).1
    rw [lookupUF_canonical humem hid hnd]; rfl
  · intro name τ uf hmemΦ hlk
    obtain ⟨u, henc, humem⟩ := hmem (name, τ) hmemΦ
    have hid := (encodeSig_ok_inv henc).1
    have : lookupUF ufs name = some u := lookupUF_canonical humem hid hnd
    rw [this] at hlk; injection hlk with hlk; subst hlk
    exact (encodeSig_ok_inv henc).2.1
  · intro name τ uf hmemΦ hlk
    obtain ⟨u, henc, humem⟩ := hmem (name, τ) hmemΦ
    have hid := (encodeSig_ok_inv henc).1
    have : lookupUF ufs name = some u := lookupUF_canonical humem hid hnd
    rw [this] at hlk; injection hlk with hlk; subst hlk
    exact (encodeSig_ok_inv henc).2.2

/-! ## A constructed witness `ufs` for the totality preconditions

`fnameCtxWF_of_mem` reflects `FNameCtxWF` against a given `ufs`. For `encode_wf` that `ufs` is the
real emitted `(SMTProgram.ctx (encode P)).ufs`. But `encode_succeeds` is upstream of that (it proves
`encode P` succeeds), so it needs an independently-constructed `ufs` to feed `toSMTTerm_succeeds`.
`ufsOf` builds one canonical UF per source entry (`sigUF`); under the source contexts' `MonoTyIsSimp`
+ name-nodup it satisfies `FNameCtxWF` for any sub-context — via `fnameCtxWF_of_mem`, discharging
its membership premise by `sigUF_eq_encodeSig` and its id-nodup premise by the source-name nodup. -/

/-- Total signature encoder — `encodeSig` with a fallback, so it is a plain function. Under
    `MonoTyIsSimp` the fallback is never taken (`sigUF_eq_encodeSig`). -/
noncomputable def sigUF (name : String) (ty : LMonoTy) : UF :=
  let (argTys, rty) := collectArrowTy ty
  ⟨name, (baseTysToTermTypes argTys).getD [], (baseTyToTermType rty).getD .bool⟩

theorem sigUF_id (name : String) (ty : LMonoTy) : (sigUF name ty).id = name := by
  simp only [sigUF]

/-- Under `MonoTyIsSimp`, the total `sigUF` agrees with `encodeSig`'s success. -/
theorem sigUF_eq_encodeSig {name : String} {ty : LMonoTy} (h : LExpr.MonoTyIsSimp ty) :
    encodeSig name ty = .ok (sigUF name ty) := by
  obtain ⟨harg, hret⟩ := collectArrowTy_simp_base h
  obtain ⟨smtRty, hrty⟩ := MonoTyIsBase_baseTyToTermType hret
  obtain ⟨smtArgTys, hargs⟩ := baseTysToTermTypes_isSome_of_allBase harg
  simp only [encodeSig, sigUF]
  obtain ⟨aTys, rTy, hcol⟩ : ∃ a r, collectArrowTy ty = (a, r) := ⟨_, _, rfl⟩
  rw [hcol] at hrty hargs
  simp only [hcol, hrty, hargs, Option.getD_some]

/-- The canonical UF context reflecting a source context: one `sigUF` per entry. -/
noncomputable def ufsOf (Γ : FNameCtx) : UFCtx := Γ.map (fun x => sigUF x.1 x.2)

/-- The ids of `ufsOf Γ` are exactly `Γ`'s names. -/
theorem ufsOf_ids (Γ : FNameCtx) : (ufsOf Γ).map (·.id) = Γ.map (·.1) := by
  simp only [ufsOf, List.map_map]
  apply List.map_congr_left; intro x _; exact sigUF_id x.1 x.2

/-- **The canonical `ufs` witnesses `FNameCtxWF`** for any sub-context `Γ'` of a nodup,
    all-`MonoTyIsSimp` context `Γ`. Discharges `toSMTTerm_succeeds`'s `FNameCtxWF Φ ufs` /
    `FNameCtxWF Ψ ufs` at `ufs := ufsOf Γ`, `Γ := Φ ++ Ψ`. -/
theorem FNameCtxWF_ufsOf {Γ Γ' : FNameCtx}
    (hnodup : (Γ.map (·.1)).Nodup) (hsub : ∀ x ∈ Γ', x ∈ Γ)
    (hsimp : ∀ x ∈ Γ, LExpr.MonoTyIsSimp x.2) :
    FNameCtxWF Γ' (ufsOf Γ) := by
  refine fnameCtxWF_of_mem (fun x hx => ?_) (by rw [ufsOf_ids]; exact hnodup)
  refine ⟨sigUF x.1 x.2, sigUF_eq_encodeSig (hsimp x (hsub x hx)), ?_⟩
  exact List.mem_map_of_mem (hsub x hx)

/-! ## Agreement: an emitted definition's declared UF equals its `encodeSig`

For `encode_wf` the reflection `fnameCtxWF_of_mem` is instantiated at the real emitted `ufs`. A
`fnDecl`/`fvarDecl` contributes exactly `encodeSig name τ`. A `fnDef`/`varDef` emits a `defineFun`,
whose declared UF is `f.toUF` (resp. the nullary `⟨v.name, [], out, body⟩.toUF`) — and this section
proves that UF equals `encodeSig`'s output on the entry's `Ψ`/`Φ` signature. That is what lets a
defined function's `Ψ`/`Φ` entry resolve against the emitted `ufs` (its `.toUF` is the entry's
`encodeSig`). -/

/-- `collectArrowTy` inverts `foldr arrow` when the return type is base (no arrow head to
    over-collect). The signature-shape fact behind the `fnDef` agreement. -/
theorem collectArrowTy_foldr_base {argTys : List LMonoTy} {rty : LMonoTy}
    (hret : LExpr.MonoTyIsBase rty) :
    collectArrowTy (List.foldr LMonoTy.arrow rty argTys) = (argTys, rty) := by
  induction argTys with
  | nil => cases hret <;> rfl
  | cons a as ih =>
    show collectArrowTy (LMonoTy.arrow a (List.foldr LMonoTy.arrow rty as)) = _
    rw [show collectArrowTy (LMonoTy.arrow a (List.foldr LMonoTy.arrow rty as))
          = (a :: (collectArrowTy (List.foldr LMonoTy.arrow rty as)).1,
             (collectArrowTy (List.foldr LMonoTy.arrow rty as)).2) from rfl, ih]

/-- **A `fnDef`'s emitted UF is its `encodeSig`.** When `d.encodeToIF = .ok f`, the declared
    signature `f.toUF` equals `encodeSig d.name d.sig.2` — so `d`'s `Ψ` entry `(d.name, d.sig.2)`
    resolves against the emitted `ufs` (which contains `f.toUF`). -/
theorem encodeToIF_toUF_eq_encodeSig {d : FnDef} {f : IF} (hf : d.encodeToIF = .ok f)
    (hret : LExpr.MonoTyIsBase d.retTy) :
    encodeSig d.name d.sig.2 = .ok f.toUF := by
  obtain ⟨hname, hbvs, hout, _⟩ := encodeToIF_ok_inv hf
  -- `f.args = canonicalArgBvs`'s output; its `.map (·.ty)` is `baseTysToTermTypes d.argTys`
  have hbwf : BVarCtxWF d.argTys f.args := canonical_bvarCtxWF hbvs
  have hargs : baseTysToTermTypes d.argTys = some (f.args.map (·.ty)) := hbwf.baseTysToTermTypes_eq
  simp only [encodeSig, FnDef.sig, collectArrowTy_foldr_base hret, IF.toUF, hargs, hout, hname]

/-- **A `varDef`'s emitted UF is its `encodeSig`.** The nullary IF `⟨v.name, [], out, body⟩`
    declares `⟨v.name, [], out⟩`, which equals `encodeSig v.name v.ty` (a base type: no args). -/
theorem varDef_toUF_eq_encodeSig {v : VarDef} {out : TermType}
    (hout : baseTyToTermType v.ty = some out) :
    encodeSig v.name v.ty = .ok ⟨v.name, [], out⟩ := by
  -- `v.ty` is base, so `collectArrowTy v.ty = ([], v.ty)`
  have hcol : collectArrowTy v.ty = ([], v.ty) := by
    have hbase := baseTyToTermType_isBase hout
    generalize v.ty = τ at *; cases hbase <;> rfl
  simp only [encodeSig, hcol, hout, baseTysToTermTypes]

/-- Encode one obligation command into one SMT command. `fnDecl`/`fvarDecl` →
    `declareFun` (via `encodeSig`); `fnDef` → `defineFun` (via `encodeToIF`); `varDef` →
    `defineFun` of a NULLARY `IF` (closed body, `[]` formals, encoded return sort); `assume` →
    `assert` of the encoded body; `distinct` → `assert` of a `distinct` term over the encoded
    operands. Mirrors the fn/fvar split at the source level onto the uniform SMT commands. -/
def encodeCmd : OblCommand → Except Format SMTCommand
  | .fnDecl name sig => do
      let u ← encodeSig name sig
      .ok (.declareFun u)
  | .fnDef d => do
      let f ← d.encodeToIF
      .ok (.defineFun f)
  | .fvarDecl name τ => do
      let u ← encodeSig name τ
      .ok (.declareFun u)
  | .varDef v => do
      let some out := baseTyToTermType v.ty
        | .error f!"encodeCmd: non-base type {repr v.ty} for variable {v.name}"
      let body ← toSMTTerm [] v.body
      .ok (.defineFun ⟨v.name, [], out, body⟩)
  | .assume e => do
      let t ← toSMTTerm [] e
      .ok (.assert t)
  | .distinct es => do
      let ts ← es.mapM (toSMTTerm [])
      .ok (.assert (.app (.core .distinct) ts .bool))

/-- Whether a command is a `check-sat` / `check-sat-assuming` query. Used to state that an ENCODED
    command block carries no checks — every check in an emitted program comes from the trailing
    queries. -/
def SMTCommand.isCheck : SMTCommand → Bool
  | .checkSat => true
  | .checkSatAssuming _ => true
  | _ => false

/-- The TRANSIENT literals a command queries under, if it is a check: `some []` for a plain
    `check-sat`, `some lits` for `check-sat-assuming lits`, `none` for a context-building command.
    This is the per-command hook the verdict fold (`SMTProgram.checkVerdicts`) reads: at a check it
    emits one satisfiability proposition (`SMTCtx.checkSat c lits`), at a non-check nothing. -/
def SMTCommand.checkLits? : SMTCommand → Option (List Term)
  | .checkSat => some []
  | .checkSatAssuming lits => some lits
  | _ => none

/-- A non-check command queries no literals (`checkLits? = none`), and conversely. -/
theorem SMTCommand.checkLits?_eq_none_iff {cmd : SMTCommand} :
    cmd.checkLits? = none ↔ cmd.isCheck = false := by
  cases cmd <;> simp [SMTCommand.checkLits?, SMTCommand.isCheck]

/-- `encodeCmd` NEVER produces a check: each obligation command maps to a
    `declareFun`/`defineFun`/`assert`. -/
theorem encodeCmd_isCheck_false {cmd : OblCommand} {smtcmd : SMTCommand}
    (h : encodeCmd cmd = .ok smtcmd) : smtcmd.isCheck = false := by
  -- `smtcmd` is one of `declareFun`/`defineFun`/`assert` in every branch; obtaining that shape
  -- and rewriting `h` (via `Except.ok.inj`) makes `smtcmd.isCheck` reduce to `false` by `rfl`.
  cases cmd <;>
    simp only [encodeCmd, bind, Except.bind] at h <;>
    (try split at h) <;> (try split at h) <;>
    (try simp only [reduceCtorEq] at h) <;>
    rw [← Except.ok.inj h] <;> rfl

/-- **The pushed-once SMT command block.** The per-command homomorphism over the obligation
    program's declarations, define-funs, and assume/distinct asserts — everything EXCEPT the
    trailing obligation literal. This is the shared prefix that production's incremental
    `check-sat-assuming` pushes once; the two check directions (`encode` / `encodeUnsat`) differ
    only in the single trailing assertion appended to it. -/
def encodeBlock (P : OblProgram) : Except Format SMTProgram :=
  P.cmds.mapM encodeCmd

/-- **The encoder (validity direction, single-check shape).** The command block, then
    `assert (not obligation)` followed by a `checkSat` — mirroring production's non-incremental
    branch (`Solver.assert (not obligation); Solver.checkSat`). The negated goal is a PERSISTENT
    assertion; the `checkSat` queries it (validity via UNSAT). -/
def encode (P : OblProgram) : Except Format SMTProgram := do
  let cmds ← encodeBlock P
  let goal ← toSMTTerm [] P.obligation
  .ok (cmds ++ [.assert (.app (.core .not) [goal] .bool), .checkSat])

/-- **The encoder (unsatisfiability direction, single-check shape).** The SAME block, then
    `assert obligation` (the goal as-is) followed by a `checkSat` — production's satisfiability
    branch (`Solver.assert obligation; Solver.checkSat`). UNSAT of the queried program witnesses
    that no consistent model satisfies the assumptions/distincts together with the obligation
    (obligation-program unsatisfiability). -/
def encodeUnsat (P : OblProgram) : Except Format SMTProgram := do
  let cmds ← encodeBlock P
  let goal ← toSMTTerm [] P.obligation
  .ok (cmds ++ [.assert goal, .checkSat])

/-- **The encoder (incremental shape).** The block pushed ONCE, then two `checkSatAssuming`
    queries under TRANSIENT literals — the goal as-is (satisfiability) then its negation
    (validity) — mirroring production's incremental branch (`checkSatAssuming [obligation]` then
    `checkSatAssuming [not obligation]`). Neither literal is a persistent assertion: the shared
    block is queried under each in turn. -/
def encodeIncremental (P : OblProgram) : Except Format SMTProgram := do
  let cmds ← encodeBlock P
  let goal ← toSMTTerm [] P.obligation
  .ok (cmds ++ [.checkSatAssuming [goal],
                .checkSatAssuming [.app (.core .not) [goal] .bool]])

/-! ## Encoder totality: `encode_succeeds`

On a well-formed obligation program every encoding step succeeds. Per command: declarations by
`encodeSig_succeeds` (from the `MonoTyIsSimp` clause); `fnDef` by `encodeToIF_succeeds`;
`varDef`/`assume`/`distinct`/obligation by `toSMTTerm_succeeds`. Each body-carrying step needs
`FNameCtxWF (prefix Φ) ufs` / `FNameCtxWF (prefix Ψ) ufs` — supplied at the constructed witness
`ufs := ufsOf (P.Φ ++ P.Ψ)` via `FNameCtxWF_ufsOf`, since a prefix context is a sub-context of the
full one (all-simp + nodup from `OblProgramWF.ctxGood`). -/

/-- A closed body that is `HasSimpType`-well-typed encodes (`toSMTTerm []` succeeds). Wraps
    `toSMTTerm_succeeds` at the empty bvar context, threading the two name-context witnesses. -/
theorem toSMTTerm_closed_succeeds {Φ : FVarCtx} {Ψ : FnCtx} {e : Expression.Expr} {τ : LMonoTy}
    {ufs : UFCtx} (he : LExpr.HasSimpType Φ Ψ [] e τ)
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) :
    ∃ t, toSMTTerm [] e = .ok t := by
  have hbwf : BVarCtxWF [] [] := ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  have hsucc := toSMTTerm_succeeds he huwf hψwf hbwf
  cases h : toSMTTerm [] e with
  | error _ => rw [h] at hsucc; exact hsucc.elim
  | ok t => exact ⟨t, rfl⟩

/-- `mapM` in `Except` succeeds when every element encodes. -/
theorem mapM_succeeds {α β} (l : List α) (f : α → Except Format β)
    (h : ∀ a ∈ l, ∃ b, f a = .ok b) : ∃ bs, l.mapM f = .ok bs := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons hd tl ih =>
    obtain ⟨b, hb⟩ := h hd (by simp)
    obtain ⟨bs, hbs⟩ := ih (fun a ha => h a (by simp [ha]))
    exact ⟨b :: bs, by simp only [List.mapM_cons, hb, hbs, bind, Except.bind, pure, Except.pure]⟩

/-- **Each command encodes** against name-context witnesses at the PREFIX context `c`. -/
theorem encodeCmd_succeeds {c : OblCtx} {cmd : OblCommand} {ufs : UFCtx}
    (hcmd : c.cmdWF cmd) (huwf : FNameCtxWF c.Φ ufs) (hψwf : FNameCtxWF c.Ψ ufs) :
    ∃ smtcmd, encodeCmd cmd = .ok smtcmd := by
  cases cmd with
  | fnDecl name sig =>
    obtain ⟨_, _, hsimp⟩ := hcmd
    obtain ⟨u, hu⟩ := encodeSig_succeeds (name := name) hsimp
    exact ⟨.declareFun u, by simp only [encodeCmd, hu, bind, Except.bind]⟩
  | fnDef d =>
    obtain ⟨_, _, hdwf, hdwfin⟩ := hcmd
    obtain ⟨bvs, out, body, _, _, _, henc⟩ := encodeToIF_succeeds d hdwf hdwfin huwf hψwf
    exact ⟨.defineFun ⟨d.name, bvs, out, body⟩,
      by simp only [encodeCmd, henc, bind, Except.bind]⟩
  | fvarDecl name τ =>
    obtain ⟨_, _, hsimp⟩ := hcmd
    obtain ⟨u, hu⟩ := encodeSig_succeeds (name := name) hsimp
    exact ⟨.declareFun u, by simp only [encodeCmd, hu, bind, Except.bind]⟩
  | varDef v =>
    obtain ⟨_, _, hvwfin⟩ := hcmd
    obtain ⟨out, hout⟩ := MonoTyIsBase_baseTyToTermType (HasSimpType_base hvwfin)
    obtain ⟨t, ht⟩ := toSMTTerm_closed_succeeds hvwfin huwf hψwf
    refine ⟨.defineFun ⟨v.name, [], out, t⟩, ?_⟩
    simp only [encodeCmd, hout, ht, bind, Except.bind]
  | assume e =>
    obtain ⟨t, ht⟩ := toSMTTerm_closed_succeeds hcmd huwf hψwf
    exact ⟨.assert t, by simp only [encodeCmd, ht, bind, Except.bind]⟩
  | distinct es =>
    obtain ⟨_, τ, _, hall⟩ := hcmd
    obtain ⟨ts, hts⟩ := mapM_succeeds es (toSMTTerm [])
      (fun e he => toSMTTerm_closed_succeeds (hall e he) huwf hψwf)
    exact ⟨.assert (.app (.core .distinct) ts .bool),
      by simp only [encodeCmd, hts, bind, Except.bind]⟩

/-- `OblCtx.step` only ever GROWS `Φ` by append, so a `Φ`-membership is preserved. -/
theorem OblCtx.step_mem_Φ {c : OblCtx} {cmd : OblCommand} {x : String × LMonoTy}
    (hx : x ∈ c.Φ) : x ∈ (c.step cmd).Φ := by
  cases cmd <;> simp only [OblCtx.step] <;>
    first | exact hx | (simp only [List.mem_append]; exact Or.inl hx)

/-- `OblCtx.step` only ever GROWS `Ψ` by append, so a `Ψ`-membership is preserved. -/
theorem OblCtx.step_mem_Ψ {c : OblCtx} {cmd : OblCommand} {x : String × LMonoTy}
    (hx : x ∈ c.Ψ) : x ∈ (c.step cmd).Ψ := by
  cases cmd <;> simp only [OblCtx.step] <;>
    first | exact hx | (simp only [List.mem_append]; exact Or.inl hx)

/-- Along the fold, the accumulated `Φ`/`Ψ` only grow — so every prefix context's entries are
    entries of the final `(cmds.foldl step c).Φ`/`.Ψ`. -/
theorem foldl_step_mem {cmds : List OblCommand} {c : OblCtx} {x : String × LMonoTy} :
    (x ∈ c.Φ → x ∈ (cmds.foldl OblCtx.step c).Φ) ∧
    (x ∈ c.Ψ → x ∈ (cmds.foldl OblCtx.step c).Ψ) := by
  induction cmds generalizing c with
  | nil => exact ⟨id, id⟩
  | cons cmd rest ih =>
    exact ⟨fun hx => (ih (c := c.step cmd)).1 (OblCtx.step_mem_Φ hx),
           fun hx => (ih (c := c.step cmd)).2 (OblCtx.step_mem_Ψ hx)⟩

/-! ## Encoder totality: assembling `encode_succeeds` -/

/-- The witness `ufs` for the totality proof: the canonical reflection of the FULL contexts. -/
private noncomputable def totalityUFs (P : OblProgram) : UFCtx := ufsOf (P.Φ ++ P.Ψ)

/-- Both name-context witnesses hold at ANY prefix context `c` reached by the fold, at the
    single witness `totalityUFs P`: a prefix entry is a full-context entry (`foldl_step_mem`),
    the full context is all-`MonoTyIsSimp` and name-nodup (`OblProgramWF.ctxGood`), so
    `FNameCtxWF_ufsOf` applies to both `c.Φ ⊆ P.Φ ⊆ P.Φ ++ P.Ψ` and the `Ψ` analog. -/
theorem prefix_fnameCtxWF {P : OblProgram} (h : OblProgramWF P) {rest : List OblCommand}
    {c : OblCtx} (hfold : ∃ done, done ++ rest = P.cmds ∧ done.foldl OblCtx.step {} = c) :
    FNameCtxWF c.Φ (totalityUFs P) ∧ FNameCtxWF c.Ψ (totalityUFs P) := by
  obtain ⟨done, hdone, hc⟩ := hfold
  have hgood := h.ctxGood
  -- names of the full context are nodup; entries all simp
  have hnodup : ((P.Φ ++ P.Ψ).map (·.1)).Nodup := by
    rw [List.map_append]; exact hgood.namesNodup
  have hsimp : ∀ x ∈ P.Φ ++ P.Ψ, LExpr.MonoTyIsSimp x.2 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hgood.Φsimp x hx
    · exact hgood.Ψsimp x hx
  -- `c`'s entries are full-context entries: `c = done.foldl step {}`, and `P.cmds` extends
  -- `done`, so `c.Φ ⊆ (P.cmds.foldl step {}).Φ = P.Φ`.
  have hΦsub : ∀ x ∈ c.Φ, x ∈ P.Φ ++ P.Ψ := by
    intro x hx
    have : x ∈ P.Φ := by
      rw [OblProgram.Φ, OblProgram.ctx, ← hdone, List.foldl_append, hc]
      exact (foldl_step_mem (cmds := rest) (c := c)).1 hx
    exact List.mem_append.mpr (Or.inl this)
  have hΨsub : ∀ x ∈ c.Ψ, x ∈ P.Φ ++ P.Ψ := by
    intro x hx
    have : x ∈ P.Ψ := by
      rw [OblProgram.Ψ, OblProgram.ctx, ← hdone, List.foldl_append, hc]
      exact (foldl_step_mem (cmds := rest) (c := c)).2 hx
    exact List.mem_append.mpr (Or.inr this)
  exact ⟨FNameCtxWF_ufsOf hnodup hΦsub hsimp, FNameCtxWF_ufsOf hnodup hΨsub hsimp⟩

/-- The command list encodes, from any prefix context reached by the fold. Threads the fold's
    accumulator so each command sees name-context witnesses at ITS prefix (`prefix_fnameCtxWF`),
    exactly where `cmdWF` typed its body. -/
theorem encodeCmds_succeeds {P : OblProgram} (h : OblProgramWF P) :
    ∀ (done rest : List OblCommand), done ++ rest = P.cmds →
      OblProgramWFfrom rest (done.foldl OblCtx.step {}) →
      ∃ cmds, rest.mapM encodeCmd = .ok cmds := by
  intro done rest
  induction rest generalizing done with
  | nil => intro _ _; exact ⟨[], rfl⟩
  | cons cmd tl ih =>
    intro hdone hwf
    obtain ⟨hcmd, htl⟩ := hwf
    obtain ⟨huwf, hψwf⟩ := prefix_fnameCtxWF h ⟨done, hdone, rfl⟩
    obtain ⟨smtcmd, hsmtcmd⟩ := encodeCmd_succeeds hcmd huwf hψwf
    -- recurse with `done' = done ++ [cmd]`, whose fold is `(done.foldl step {}).step cmd`
    have hdone' : (done ++ [cmd]) ++ tl = P.cmds := by rw [List.append_assoc]; exact hdone
    have hfold' : (done ++ [cmd]).foldl OblCtx.step {}
        = (done.foldl OblCtx.step {}).step cmd := by
      rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil]
    obtain ⟨cmds, hcmds⟩ := ih (done ++ [cmd]) hdone' (by rw [hfold']; exact htl)
    exact ⟨smtcmd :: cmds,
      by simp only [List.mapM_cons, hsmtcmd, hcmds, bind, Except.bind, pure, Except.pure]⟩

/-- **The encoder is total on well-formed input.** Every command encodes (`encodeCmds_succeeds`)
    and the obligation encodes (its `HasSimpType` at the full context feeds
    `toSMTTerm_closed_succeeds` at the witness `ufs`). -/
theorem encode_succeeds {P : OblProgram} (h : OblProgramWF P) :
    ∃ prog, encode P = .ok prog := by
  obtain ⟨cmds, hcmds⟩ := encodeCmds_succeeds h [] P.cmds (by simp) h.cmdsWF
  -- obligation: `HasSimpType P.Φ P.Ψ [] obligation bool` + full-context witnesses
  obtain ⟨huwf, hψwf⟩ := prefix_fnameCtxWF h (rest := []) (c := P.cmds.foldl OblCtx.step {})
    ⟨P.cmds, by simp, rfl⟩
  have hΦ : (P.cmds.foldl OblCtx.step {}).Φ = P.Φ := by rw [OblProgram.Φ, OblProgram.ctx]
  have hΨ : (P.cmds.foldl OblCtx.step {}).Ψ = P.Ψ := by rw [OblProgram.Ψ, OblProgram.ctx]
  rw [hΦ] at huwf; rw [hΨ] at hψwf
  obtain ⟨goal, hgoal⟩ := toSMTTerm_closed_succeeds h.obligationWF huwf hψwf
  exact ⟨cmds ++ [.assert (.app (.core .not) [goal] .bool), .checkSat],
    by simp only [encode, encodeBlock, hcmds, hgoal, bind, Except.bind]⟩

/-! ## Encoder WF-preservation: `encode_wf`

The SMT-side soundness theorem: a well-formed obligation program encodes to a legal SMT-LIB script
(declare-before-use, unique non-reserved ids, every body/assertion type-checks). It is the
cross-side simulation over the encoding walk — the two prefix-WF folds (`OblProgramWFfrom` and
`SMTProgramWFfrom`) advance in lockstep, linked by `EncInv`:
  • emitted UF ids permute the source declared names (`idsPerm`) — carries id-nodup and
    no-reserved from the source `Good` to the SMT side;
  • every `Φ`/`Ψ` entry's `encodeSig` UF is already present in the emitted `ufs` (`resolves`) —
    gives `FNameCtxWF` at the real emitted context, feeding `toSMTTerm_typeChecks` so each emitted
    body type-checks against exactly the declarations visible to it.
`EncInv` is the cross-side companion of `OblCtx.Good`/`SMTCtx.Good`. -/

/- ── Syntactic encoding graph (model-FREE) ──
   `EncInv` is model-free, so it carries only the four SYNTACTIC per-function facts
   (name/bridge/rty/bwf); the model-dependent correspondence `corr` is supplied at
   model-transfer time from `FnEnvCorresponds` and fed to the per-function bridges. These
   `EncodedBySyn` predicates are exactly that syntactic core. -/

/-- The syntactic (model-free) encoding facts for a `FnDef`: the emitted IF carries `d`'s name,
    its body/return-sort are `d`'s encodings, and `d.argTys`/`f.args` form a WF bvar context. -/
structure FnDef.EncodedBySyn (d : FnDef) (f : IF) : Prop where
  name_eq : f.id = d.name
  bridge : toSMTTerm f.args d.body = .ok f.body
  rty : baseTyToTermType d.retTy = some f.out
  bwf : BVarCtxWF d.argTys f.args

/-- The syntactic encoding graph of a `.det` variable definition: a NULLARY IF (`f.args = []`)
    named `v.name`, whose body/return-sort encode `v`'s closed body / declared type. -/
structure VarDef.EncodedBySyn (v : VarDef) (f : IF) : Prop where
  name_eq : f.id = v.name
  args_nil : f.args = []
  bridge : toSMTTerm [] v.body = .ok f.body
  rty : baseTyToTermType v.ty = some f.out

/-- Syntactic encoding of a distinctness group into its SMT `distinct` term. -/
def DistinctEncodedBySyn (es : List Expression.Expr) (t : Term) : Prop :=
  ∃ ts, es.mapM (toSMTTerm []) = .ok ts ∧ t = .app (.core .distinct) ts .bool

/-- The **syntactic (structural) correspondence** between a source obligation context `c` and the
    emitted SMT context `s`: every emitted symbol/assertion is the encoding of a matching source one,
    and vice versa. `ModelTransfer` promotes this structural match to a semantic one (a source model
    transfers to an SMT model that agrees value-for-value). -/
structure EncInv (c : OblCtx) (s : SMTCtx) : Prop where
  /-- Emitted UF ids are the source declared names, up to permutation. -/
  idsPerm : (s.ufs.map (·.id)).Perm c.names
  /-- Every source `Φ`/`Ψ` entry's `encodeSig` UF is present in the emitted `ufs`. -/
  resolves : ∀ x ∈ c.Φ ++ c.Ψ, ∃ u, encodeSig x.1 x.2 = .ok u ∧ u ∈ s.ufs
  /-- Every emitted interpreted function `f ∈ s.fs` is the syntactic encoding of SOME source
      definition — a `fnDef` (op-side) OR a `varDef` (fvar-side); the mixed `fs` is discharged
      per-`f` by the corresponding bridge in the model transfer. -/
  fsCorr : ∀ f ∈ s.fs,
    (∃ d ∈ c.defs, FnDef.EncodedBySyn d f) ∨ (∃ v ∈ c.varDefs, VarDef.EncodedBySyn v f)
  /-- Every emitted assertion `t ∈ s.assertions` is the encoding of SOME source assumption OR
      the `distinct` encoding of a source distinctness group. (This invariant holds at the command
      BLOCK, before the trailing obligation assert.) -/
  assertsCorr : ∀ t ∈ s.assertions,
    (∃ e ∈ c.assumptions, toSMTTerm [] e = .ok t) ∨ (∃ es ∈ c.distincts, DistinctEncodedBySyn es t)

/-- The emitted `ufs` ids are nodup (from `idsPerm` + source name-nodup). -/
theorem EncInv.ids_nodup {c : OblCtx} {s : SMTCtx} (hinv : EncInv c s)
    (hnd : c.names.Nodup) : (s.ufs.map (·.id)).Nodup :=
  hinv.idsPerm.nodup_iff.mpr hnd

/-- `FNameCtxWF Φ` / `FNameCtxWF Ψ` at the emitted context (from `resolves` + id-nodup). -/
theorem EncInv.fnameCtxWF {c : OblCtx} {s : SMTCtx} (hinv : EncInv c s)
    (hnd : c.names.Nodup) :
    FNameCtxWF c.Φ s.ufs ∧ FNameCtxWF c.Ψ s.ufs := by
  have hidnd := hinv.ids_nodup hnd
  refine ⟨fnameCtxWF_of_mem (fun x hx => hinv.resolves x ?_) hidnd,
          fnameCtxWF_of_mem (fun x hx => hinv.resolves x ?_) hidnd⟩
  · exact List.mem_append.mpr (Or.inl hx)
  · exact List.mem_append.mpr (Or.inr hx)

/-- `UFCtxWF` at the emitted context (from id-nodup + no-reserved via the perm). -/
theorem EncInv.ufCtxWF {c : OblCtx} {s : SMTCtx} (hinv : EncInv c s)
    (hnd : c.names.Nodup) (hnr : ∀ n : Nat, s!"$__bv{n}" ∉ c.names) :
    UFCtxWF s.ufs := by
  refine ⟨hinv.ids_nodup hnd, fun n hmem => ?_⟩
  exact hnr n (hinv.idsPerm.mem_iff.mp hmem)

/-- A `Φ`-side declaration/definition step: names insert `name` on the `Φ` side. -/
private theorem names_step_Φ (c : OblCtx) (name : String) (τ : LMonoTy) :
    ((c.Φ ++ [(name, τ)]).map (·.1) ++ c.Ψ.map (·.1)).Perm (name :: c.names) := by
  simp only [OblCtx.names, List.map_append, List.map_cons, List.map_nil]
  exact (List.perm_append_comm.append_right _)

/-- A `Ψ`-side declaration/definition step: names insert `name` on the `Ψ` side. -/
private theorem names_step_Ψ (c : OblCtx) (name : String) (τ : LMonoTy) :
    (c.Φ.map (·.1) ++ (c.Ψ ++ [(name, τ)]).map (·.1)).Perm (name :: c.names) := by
  simp only [OblCtx.names, List.map_append, List.map_cons, List.map_nil]
  rw [← List.append_assoc]; exact List.perm_append_comm

/-- Emitted UF ids grow by appending one id — permuting to a `cons`. -/
private theorem ufs_ids_step (ufs : UFCtx) (u : UF) :
    ((ufs ++ [u]).map (·.id)).Perm (u.id :: ufs.map (·.id)) := by
  rw [List.map_append]; simp only [List.map_cons, List.map_nil]; exact List.perm_append_comm

/-- The `resolves` field is preserved when `ufs` grows by a fresh UF and one entry is added on
    the `Φ` side, provided the new entry's `encodeSig` is the appended UF. -/
private theorem resolves_step_Φ {c : OblCtx} {s : SMTCtx} (hinv : EncInv c s)
    {name : String} {τ : LMonoTy} {u : UF} (hu : encodeSig name τ = .ok u) :
    ∀ x ∈ (c.Φ ++ [(name, τ)]) ++ c.Ψ, ∃ u', encodeSig x.1 x.2 = .ok u' ∧ u' ∈ s.ufs ++ [u] := by
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | rfl) | hx
  · obtain ⟨u', hu', hmem⟩ := hinv.resolves x (List.mem_append.mpr (Or.inl hx))
    exact ⟨u', hu', List.mem_append_left _ hmem⟩
  · exact ⟨u, hu, List.mem_append_right _ (by simp)⟩
  · obtain ⟨u', hu', hmem⟩ := hinv.resolves x (List.mem_append.mpr (Or.inr hx))
    exact ⟨u', hu', List.mem_append_left _ hmem⟩

/-- The `resolves` field is preserved for a `Ψ`-side addition. -/
private theorem resolves_step_Ψ {c : OblCtx} {s : SMTCtx} (hinv : EncInv c s)
    {name : String} {τ : LMonoTy} {u : UF} (hu : encodeSig name τ = .ok u) :
    ∀ x ∈ c.Φ ++ (c.Ψ ++ [(name, τ)]), ∃ u', encodeSig x.1 x.2 = .ok u' ∧ u' ∈ s.ufs ++ [u] := by
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx | rfl
  · obtain ⟨u', hu', hmem⟩ := hinv.resolves x (List.mem_append.mpr (Or.inl hx))
    exact ⟨u', hu', List.mem_append_left _ hmem⟩
  · obtain ⟨u', hu', hmem⟩ := hinv.resolves x (List.mem_append.mpr (Or.inr hx))
    exact ⟨u', hu', List.mem_append_left _ hmem⟩
  · exact ⟨u, hu, List.mem_append_right _ (by simp)⟩

/-- `fsCorr` preserved by a `fnDef` step: `s.fs += [f]`, `c.defs += [d]`; old entries weaken
    their `∈ c.defs`, the new `f` is the left disjunct with `d` (via its syntactic encoding). -/
private theorem fsCorr_step_fnDef {c : OblCtx} {s : SMTCtx} (hinv : EncInv c s)
    {d : FnDef} {f : IF} (hsyn : FnDef.EncodedBySyn d f) :
    ∀ f' ∈ s.fs ++ [f],
      (∃ d' ∈ c.defs ++ [d], FnDef.EncodedBySyn d' f') ∨
      (∃ v ∈ c.varDefs, VarDef.EncodedBySyn v f') := by
  intro f' hf'
  simp only [List.mem_append, List.mem_singleton] at hf'
  rcases hf' with hf' | rfl
  · rcases hinv.fsCorr f' hf' with ⟨d', hd', hs⟩ | ⟨v, hv, hs⟩
    · exact Or.inl ⟨d', List.mem_append_left _ hd', hs⟩
    · exact Or.inr ⟨v, hv, hs⟩
  · exact Or.inl ⟨d, List.mem_append_right _ (by simp), hsyn⟩

/-- `fsCorr` preserved by a `varDef` step (symmetric to `fnDef`, right disjunct). -/
private theorem fsCorr_step_varDef {c : OblCtx} {s : SMTCtx} (hinv : EncInv c s)
    {v : VarDef} {f : IF} (hsyn : VarDef.EncodedBySyn v f) :
    ∀ f' ∈ s.fs ++ [f],
      (∃ d ∈ c.defs, FnDef.EncodedBySyn d f') ∨
      (∃ v' ∈ c.varDefs ++ [v], VarDef.EncodedBySyn v' f') := by
  intro f' hf'
  simp only [List.mem_append, List.mem_singleton] at hf'
  rcases hf' with hf' | rfl
  · rcases hinv.fsCorr f' hf' with ⟨d, hd, hs⟩ | ⟨v', hv', hs⟩
    · exact Or.inl ⟨d, hd, hs⟩
    · exact Or.inr ⟨v', List.mem_append_left _ hv', hs⟩
  · exact Or.inr ⟨v, List.mem_append_right _ (by simp), hsyn⟩

/-- `assertsCorr` preserved by an `assume` step: `s.assertions += [t]`, `c.assumptions += [e]`. -/
private theorem assertsCorr_step_assume {c : OblCtx} {s : SMTCtx} (hinv : EncInv c s)
    {e : Expression.Expr} {t : Term} (ht : toSMTTerm [] e = .ok t) :
    ∀ t' ∈ s.assertions ++ [t],
      (∃ e' ∈ c.assumptions ++ [e], toSMTTerm [] e' = .ok t') ∨
      (∃ es ∈ c.distincts, DistinctEncodedBySyn es t') := by
  intro t' ht'
  simp only [List.mem_append, List.mem_singleton] at ht'
  rcases ht' with ht' | rfl
  · rcases hinv.assertsCorr t' ht' with ⟨e', he', hs⟩ | ⟨es, hes, hs⟩
    · exact Or.inl ⟨e', List.mem_append_left _ he', hs⟩
    · exact Or.inr ⟨es, hes, hs⟩
  · exact Or.inl ⟨e, List.mem_append_right _ (by simp), ht⟩

/-- `assertsCorr` preserved by a `distinct` step (symmetric, right disjunct). -/
private theorem assertsCorr_step_distinct {c : OblCtx} {s : SMTCtx} (hinv : EncInv c s)
    {es : List Expression.Expr} {t : Term} (hd : DistinctEncodedBySyn es t) :
    ∀ t' ∈ s.assertions ++ [t],
      (∃ e ∈ c.assumptions, toSMTTerm [] e = .ok t') ∨
      (∃ es' ∈ c.distincts ++ [es], DistinctEncodedBySyn es' t') := by
  intro t' ht'
  simp only [List.mem_append, List.mem_singleton] at ht'
  rcases ht' with ht' | rfl
  · rcases hinv.assertsCorr t' ht' with ⟨e, he, hs⟩ | ⟨es', hes', hs⟩
    · exact Or.inl ⟨e, he, hs⟩
    · exact Or.inr ⟨es', List.mem_append_left _ hes', hs⟩
  · exact Or.inr ⟨es, List.mem_append_right _ (by simp), hd⟩

/-- `mapM` in `Except` that succeeds transports a pointwise property from inputs to outputs
    (and equates lengths) — used to lift per-operand type-checks to the `distinct` operand list. -/
theorem mapM_ok_forall {α β} {l : List α} {out : List β} {f : α → Except Format β}
    {P : β → Prop} (hf : ∀ a ∈ l, ∀ b, f a = .ok b → P b)
    (h : l.mapM f = .ok out) : out.length = l.length ∧ ∀ b ∈ out, P b := by
  induction l generalizing out with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨rfl, by simp⟩
  | cons hd tl ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hhd : f hd with
    | error e => rw [hhd] at h; simp at h
    | ok bhd =>
      rw [hhd] at h; simp only at h
      cases htl : tl.mapM f with
      | error e => rw [htl] at h; simp at h
      | ok bs =>
        rw [htl] at h; simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨hlen, hall⟩ := ih (fun a ha => hf a (by simp [ha])) htl
        rw [← h]
        refine ⟨by simp [hlen], ?_⟩
        intro b' hb'; simp only [List.mem_cons] at hb'
        rcases hb' with heq | hb'
        · rw [heq]; exact hf hd (by simp) bhd hhd
        · exact hall b' hb'

/-- **An encoded block carries no checks** — every command emitted by `encodeBlock` is a
    `declare`/`define`/`assert`, so any `check-sat`(-assuming) in an emitted program is one of the
    TRAILING queries, never part of the shared block. -/
theorem encodeBlock_noCheck {P : OblProgram} {block : SMTProgram} (h : encodeBlock P = .ok block) :
    ∀ c ∈ block, c.isCheck = false :=
  (mapM_ok_forall (P := fun c => c.isCheck = false)
    (fun _ _ _ hb => encodeCmd_isCheck_false hb) h).2

/-- `typeCheckArgs` against a `replicate ty` succeeds when every argument type-checks to `ty`. -/
theorem typeCheckArgs_replicate {ufs : UFCtx} {ts : List Term} {ty : TermType}
    (h : ∀ t ∈ ts, Term.typeCheck ⟨[], ufs, []⟩ t = .ok ty) :
    Term.typeCheckArgs ⟨[], ufs, []⟩ ts (List.replicate ts.length ty) = true := by
  induction ts with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.length_cons, List.replicate, Term.typeCheckArgs, h hd (by simp),
      beq_self_eq_true, Bool.true_and]
    exact ih (fun t ht => h t (by simp [ht]))

/-- **A `distinct` term type-checks** when it has `≥ 2` operands, all type-checking to one sort. -/
theorem distinct_typeChecks {ufs : UFCtx} {ts : List Term} {ty : TermType}
    (hlen : 2 ≤ ts.length) (h : ∀ t ∈ ts, Term.typeCheck ⟨[], ufs, []⟩ t = .ok ty) :
    Term.typeCheck ⟨[], ufs, []⟩ (.app (.core .distinct) ts .bool) = .ok .bool := by
  match ts, hlen with
  | t1 :: t2 :: rest, _ =>
    have hargs : Term.typeCheckArgs ⟨[], ufs, []⟩ (t2 :: rest)
        (List.replicate (t2 :: rest).length ty) = true :=
      typeCheckArgs_replicate (fun t ht => h t (by simp [ht]))
    simp only [Term.typeCheck, h t1 (by simp), bind, Except.bind, hargs, beq_self_eq_true,
      Bool.and_true, if_true]

/-- **Per-command WF-preservation** (the cross-side simulation step). Given the invariant at a
    prefix, source command WF (with the prefix's name-nodup/no-reserved from `Good`), and the
    (singleton) emitted command, the emitted command is `SMTCtx.cmdWF` against the emitted
    prefix AND the invariant is re-established at the stepped contexts. Type-checks come from
    `toSMTTerm_typeChecks` at the REAL emitted `ufs` (via `EncInv.fnameCtxWF`/`.ufCtxWF`);
    freshness from source freshness transported by `idsPerm`; the new UF's presence from the
    agreement lemmas (`encodeSig`/`encodeToIF_toUF`/`varDef_toUF`). -/
theorem encodeCmd_preserves {c : OblCtx} {s : SMTCtx} {cmd : OblCommand} {smtcmd : SMTCommand}
    (hinv : EncInv c s) (hcmd : c.cmdWF cmd)
    (hnd : c.names.Nodup) (hnr : ∀ n : Nat, s!"$__bv{n}" ∉ c.names)
    (henc : encodeCmd cmd = .ok smtcmd) :
    SMTCtx.cmdWF s smtcmd ∧ EncInv (c.step cmd) (s.step smtcmd) := by
  have hufwf := hinv.ufCtxWF hnd hnr
  obtain ⟨huΦ, huΨ⟩ := hinv.fnameCtxWF hnd
  cases cmd with
  | fnDecl name sig =>
    obtain ⟨hfresh, hnres, hsimp⟩ := hcmd
    obtain ⟨u, hu⟩ := encodeSig_succeeds (name := name) hsimp
    have hid : u.id = name := (encodeSig_ok_inv hu).1
    simp only [encodeCmd, hu, bind, Except.bind] at henc; obtain rfl := (Except.ok.inj henc).symm
    refine ⟨⟨?_, fun n => ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hid]; exact fun hm => hfresh (hinv.idsPerm.mem_iff.mp hm)
    · rw [hid]; exact hnres n
    · -- idsPerm: (s.ufs ++ [u]).ids ~ u.id :: s.ufs.ids ~ name :: c.names ~ (step).names
      refine (ufs_ids_step s.ufs u).trans ?_
      rw [hid]
      exact (hinv.idsPerm.cons name).trans (names_step_Ψ c name sig).symm
    · -- resolves: entries persist; new `(name, sig)` resolves via `hu`
      have := resolves_step_Ψ hinv hu
      simpa only [OblCtx.step, SMTCtx.step] using this
    · -- fsCorr/assertsCorr: `fs`/`defs`/`varDefs`/assertions all unchanged by a declaration
      simpa only [OblCtx.step, SMTCtx.step] using hinv.fsCorr
    · simpa only [OblCtx.step, SMTCtx.step] using hinv.assertsCorr
  | fvarDecl name τ =>
    obtain ⟨hfresh, hnres, hsimp⟩ := hcmd
    obtain ⟨u, hu⟩ := encodeSig_succeeds (name := name) hsimp
    have hid : u.id = name := (encodeSig_ok_inv hu).1
    simp only [encodeCmd, hu, bind, Except.bind] at henc; obtain rfl := (Except.ok.inj henc).symm
    refine ⟨⟨?_, fun n => ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hid]; exact fun hm => hfresh (hinv.idsPerm.mem_iff.mp hm)
    · rw [hid]; exact hnres n
    · refine (ufs_ids_step s.ufs u).trans ?_
      rw [hid]
      exact (hinv.idsPerm.cons name).trans (names_step_Φ c name τ).symm
    · have := resolves_step_Φ hinv hu
      simpa only [OblCtx.step, SMTCtx.step] using this
    · simpa only [OblCtx.step, SMTCtx.step] using hinv.fsCorr
    · simpa only [OblCtx.step, SMTCtx.step] using hinv.assertsCorr
  | fnDef d =>
    obtain ⟨hfresh, hnres, hdwf, hdwfin⟩ := hcmd
    obtain ⟨bvs, out, body, _, _, _, hfenc⟩ := encodeToIF_succeeds d hdwf hdwfin huΦ huΨ
    have hsig := encodeToIF_toUF_eq_encodeSig hfenc (HasSimpType_base hdwfin)
    have hid : (⟨d.name, bvs, out, body⟩ : IF).toUF.id = d.name := rfl
    -- the body type-checks at the emitted `ufs` (real context), via `toSMTTerm_typeChecks`
    obtain ⟨_, hbvs, hout, hbody⟩ := encodeToIF_ok_inv hfenc
    have hbwf : BVarCtxWF d.argTys bvs := canonical_bvarCtxWF hbvs
    have htc : Term.typeCheck ⟨[], s.ufs, bvs⟩ body = .ok out :=
      toSMTTerm_typeChecks hdwfin hufwf hbody hout huΦ huΨ hbwf
    -- the syntactic encoding graph of `d` into the emitted IF
    have hsyn : FnDef.EncodedBySyn d ⟨d.name, bvs, out, body⟩ := ⟨rfl, hbody, hout, hbwf⟩
    simp only [encodeCmd, hfenc, bind, Except.bind] at henc; obtain rfl := (Except.ok.inj henc).symm
    refine ⟨⟨?_, fun n => ?_, htc⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · exact fun hm => hfresh (hinv.idsPerm.mem_iff.mp hm)
    · exact hnres n
    · refine (ufs_ids_step s.ufs (⟨d.name, bvs, out, body⟩ : IF).toUF).trans ?_
      have := (hinv.idsPerm.cons d.name).trans (names_step_Ψ c d.name d.sig.2).symm
      simpa only [OblCtx.step, FnDef.sig] using this
    · -- resolves: `d.sig = (d.name, d.sig.2)`; its `encodeSig` is `.toUF` (agreement `hsig`)
      have hr := resolves_step_Ψ hinv (name := d.name) (τ := d.sig.2)
        (u := (⟨d.name, bvs, out, body⟩ : IF).toUF) hsig
      simpa only [OblCtx.step, SMTCtx.step, FnDef.sig] using hr
    · -- fsCorr: new `f` is `d`'s syntactic encoding (left disjunct)
      simpa only [OblCtx.step, SMTCtx.step] using fsCorr_step_fnDef hinv hsyn
    · -- assertsCorr: assertions/assumptions/distincts unchanged
      simpa only [OblCtx.step, SMTCtx.step] using hinv.assertsCorr
  | varDef v =>
    obtain ⟨hfresh, hnres, hvwfin⟩ := hcmd
    obtain ⟨out, hout⟩ := MonoTyIsBase_baseTyToTermType (HasSimpType_base hvwfin)
    obtain ⟨t, ht⟩ := toSMTTerm_closed_succeeds hvwfin huΦ huΨ
    have hsig := varDef_toUF_eq_encodeSig (v := v) hout
    have hid : (⟨v.name, [], out, t⟩ : IF).toUF.id = v.name := rfl
    have hbwf : BVarCtxWF [] [] := ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
    have htc : Term.typeCheck ⟨[], s.ufs, []⟩ t = .ok out :=
      toSMTTerm_typeChecks hvwfin hufwf ht hout huΦ huΨ hbwf
    have hsyn : VarDef.EncodedBySyn v ⟨v.name, [], out, t⟩ := ⟨rfl, rfl, ht, hout⟩
    simp only [encodeCmd, hout, ht, bind, Except.bind] at henc; obtain rfl := (Except.ok.inj henc).symm
    refine ⟨⟨?_, fun n => ?_, htc⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · exact fun hm => hfresh (hinv.idsPerm.mem_iff.mp hm)
    · exact hnres n
    · refine (ufs_ids_step s.ufs (⟨v.name, [], out, t⟩ : IF).toUF).trans ?_
      exact (hinv.idsPerm.cons v.name).trans (names_step_Φ c v.name v.ty).symm
    · have hr := resolves_step_Φ hinv (name := v.name) (τ := v.ty)
        (u := (⟨v.name, [], out, t⟩ : IF).toUF) hsig
      simpa only [OblCtx.step, SMTCtx.step] using hr
    · simpa only [OblCtx.step, SMTCtx.step] using fsCorr_step_varDef hinv hsyn
    · simpa only [OblCtx.step, SMTCtx.step] using hinv.assertsCorr
  | assume e =>
    obtain ⟨t, ht⟩ := toSMTTerm_closed_succeeds hcmd huΦ huΨ
    have htc : Term.typeCheck ⟨[], s.ufs, []⟩ t = .ok .bool :=
      toSMTTerm_typeChecks hcmd hufwf ht rfl huΦ huΨ
        ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
    simp only [encodeCmd, ht, bind, Except.bind] at henc; obtain rfl := (Except.ok.inj henc).symm
    refine ⟨htc, ⟨?_, ?_, ?_, ?_⟩⟩
    · simpa only [OblCtx.step, SMTCtx.step] using hinv.idsPerm
    · simpa only [OblCtx.step, SMTCtx.step] using hinv.resolves
    · simpa only [OblCtx.step, SMTCtx.step] using hinv.fsCorr
    · -- assertsCorr: new `t` is `e`'s encoding (left disjunct)
      simpa only [OblCtx.step, SMTCtx.step] using assertsCorr_step_assume hinv ht
  | distinct es =>
    obtain ⟨hlen, τ, hbase, hall⟩ := hcmd
    obtain ⟨smtτ, hτ⟩ := MonoTyIsBase_baseTyToTermType hbase
    obtain ⟨ts, hts⟩ := mapM_succeeds es (toSMTTerm [])
      (fun e he => toSMTTerm_closed_succeeds (hall e he) huΦ huΨ)
    -- every operand type-checks to `smtτ` (per-element `toSMTTerm_typeChecks`), and `ts.length = es.length ≥ 2`
    obtain ⟨htlen, htall⟩ := mapM_ok_forall
      (P := fun t => Term.typeCheck ⟨[], s.ufs, []⟩ t = .ok smtτ)
      (fun e he t het => toSMTTerm_typeChecks (hall e he) hufwf het hτ huΦ huΨ
        ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩) hts
    have htc : Term.typeCheck ⟨[], s.ufs, []⟩ (.app (.core .distinct) ts .bool) = .ok .bool :=
      distinct_typeChecks (by omega) htall
    have hdsyn : DistinctEncodedBySyn es (.app (.core .distinct) ts .bool) := ⟨ts, hts, rfl⟩
    simp only [encodeCmd, hts, bind, Except.bind] at henc; obtain rfl := (Except.ok.inj henc).symm
    refine ⟨htc, ⟨?_, ?_, ?_, ?_⟩⟩
    · simpa only [OblCtx.step, SMTCtx.step] using hinv.idsPerm
    · simpa only [OblCtx.step, SMTCtx.step] using hinv.resolves
    · simpa only [OblCtx.step, SMTCtx.step] using hinv.fsCorr
    · -- assertsCorr: new `t` is the `distinct` encoding of `es` (right disjunct)
      simpa only [OblCtx.step, SMTCtx.step] using assertsCorr_step_distinct hinv hdsyn

/-- `SMTProgramWFfrom` is compositional over `++`: a program is WF from `c` iff its prefix is
    WF from `c` and its suffix is WF from the prefix-folded context. -/
theorem SMTProgramWFfrom_append (a b : SMTProgram) (c : SMTCtx) :
    SMTProgramWFfrom (a ++ b) c ↔
      SMTProgramWFfrom a c ∧ SMTProgramWFfrom b (a.foldl SMTCtx.step c) := by
  induction a generalizing c with
  | nil => simp [SMTProgramWFfrom]
  | cons hd tl ih =>
    simp only [List.cons_append, SMTProgramWFfrom, List.foldl_cons, ih, and_assoc]

/-! ## The joint fold: source command list ⟹ WF emitted SMT command block + final `EncInv` -/

/-- **The command block encodes to a WF SMT prefix**, threading `EncInv` and the source `Good`
    invariant through the fold. From any prefix `c`/`s` with `EncInv c s` and `Good c`, a
    source-prefix-WF command list `rest` emits (via `mapM`) some `cmds` that is
    `SMTProgramWFfrom` from `s`, and the invariant re-establishes at the final contexts. Each
    step is `encodeCmd_preserves` (the emitted command is `cmdWF` and `EncInv` advances), with
    `Good` supplying the prefix name-nodup/no-reserved and advancing by `OblCtx.Good.step`. -/
theorem encodeCmds_wf {c : OblCtx} {s : SMTCtx} (rest : List OblCommand)
    (hinv : EncInv c s) (hgood : c.Good) (hwf : OblProgramWFfrom rest c) :
    ∃ cmds, rest.mapM encodeCmd = .ok cmds ∧
      SMTProgramWFfrom cmds s ∧
      EncInv (rest.foldl OblCtx.step c) (cmds.foldl SMTCtx.step s) := by
  induction rest generalizing c s with
  | nil => exact ⟨[], rfl, trivial, hinv⟩
  | cons cmd tl ih =>
    obtain ⟨hcmd, htl⟩ := hwf
    obtain ⟨huΦ, huΨ⟩ := hinv.fnameCtxWF hgood.namesNodup
    obtain ⟨smtcmd, henc⟩ := encodeCmd_succeeds hcmd huΦ huΨ
    obtain ⟨hcmdWF, hinv'⟩ :=
      encodeCmd_preserves hinv hcmd hgood.namesNodup hgood.noReserved henc
    -- recurse at the stepped contexts
    obtain ⟨cmds, htlenc, htlwf, htlinv⟩ := ih hinv' (hgood.step hcmd) htl
    refine ⟨smtcmd :: cmds, ?_, ?_, ?_⟩
    · simp only [List.mapM_cons, henc, htlenc, bind, Except.bind, pure, Except.pure]
    · exact ⟨hcmdWF, htlwf⟩
    · simpa only [List.foldl_cons] using htlinv

/-- **The encoder preserves well-formedness.** A well-formed obligation program encodes to a
    legal SMT-LIB script: every command declares-before-use, ids are unique and non-reserved,
    and every body/assertion (including the negated obligation) type-checks. The cross-side
    simulation (`encodeCmds_wf`) handles the command block; the trailing `assert (not goal)`
    type-checks via `toSMTTerm_typeChecks` at the final emitted context, whose `UFCtxWF`/
    `FNameCtxWF` come from the final `EncInv` + the full-context `Good`. -/
theorem encode_wf {P : OblProgram} (h : OblProgramWF P) {prog : SMTProgram}
    (henc : encode P = .ok prog) : SMTProgramWF prog := by
  -- run the joint fold over the whole command list from the empty contexts
  obtain ⟨cmds, hcmds, hblockwf, hfinv⟩ :=
    encodeCmds_wf P.cmds (c := {}) (s := {}) ⟨by simp [OblCtx.names], by intro x hx; simp at hx, by intro f hf; simp at hf, by intro t ht; simp at ht⟩
      OblCtx.Good.empty h.cmdsWF
  -- the final source context is the full `P.ctx`; its `Good` gives full nodup/no-reserved
  have hgood : P.ctx.Good := h.ctxGood
  have hfoldΦ : (P.cmds.foldl OblCtx.step {}).Φ = P.Φ := by rw [OblProgram.Φ, OblProgram.ctx]
  have hfoldΨ : (P.cmds.foldl OblCtx.step {}).Ψ = P.Ψ := by rw [OblProgram.Ψ, OblProgram.ctx]
  -- name-context witnesses at the final emitted `ufs`
  have hnd : (P.cmds.foldl OblCtx.step {}).names.Nodup := hgood.namesNodup
  obtain ⟨huΦ, huΨ⟩ := hfinv.fnameCtxWF hnd
  have hufwf := hfinv.ufCtxWF hnd hgood.noReserved
  rw [hfoldΦ] at huΦ; rw [hfoldΨ] at huΨ
  -- the obligation encodes and (negated) type-checks
  obtain ⟨goal, hgoal⟩ := toSMTTerm_closed_succeeds h.obligationWF huΦ huΨ
  have hgtc : Term.typeCheck ⟨[], (cmds.foldl SMTCtx.step {}).ufs, []⟩ goal = .ok .bool :=
    toSMTTerm_typeChecks h.obligationWF hufwf hgoal rfl huΦ huΨ
      ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  -- `prog = cmds ++ [assert (not goal), checkSat]`
  have hprog : prog = cmds ++ [.assert (.app (.core .not) [goal] .bool), .checkSat] := by
    have : encode P = .ok (cmds ++ [.assert (.app (.core .not) [goal] .bool), .checkSat]) := by
      simp only [encode, encodeBlock, hcmds, hgoal, bind, Except.bind]
    rw [henc] at this; exact (Except.ok.inj this)
  -- assemble: block WF (from `encodeCmds_wf`) + trailing assert WF (the `not goal` type-checks) +
  -- `checkSat` WF (`True`, a pure query that leaves the context untouched)
  rw [hprog, SMTProgramWF, SMTProgramWFfrom_append]
  refine ⟨hblockwf, ?_⟩
  simp only [SMTProgramWFfrom, SMTCtx.cmdWF]
  refine ⟨?_, trivial, trivial⟩
  -- `typeCheck ufs [] (not goal) = some .bool` from `hgtc`
  simp only [Term.typeCheck, bind, Except.bind, hgtc, beq_self_eq_true, Bool.and_true, if_true]

/-! ## Whole-program context correspondence: `encode_encInv`

The cross-side correspondence exposed as a first-class result: the contexts read off the source
obligation program (`OblProgram.ctx P` — the `OblCtx.step` fold) correspond (`EncInv`) to those
read off the emitted SMT command block (`block.foldl SMTCtx.step {}`), where
`prog = block ++ [assert (not goal)]`. The fold work is done inside `encodeCmds_wf`; this wrapper
names the block/goal split and the block-level `EncInv`.

This is what the model-transfer layer consumes: `EncInv.fnameCtxWF`/`.ufCtxWF` give
`FNameCtxWF`/`UFCtxWF` at the emitted context (feeding the relational triangle), `fsCorr` gives the
per-`IF` `hlink` (after upgrading each syntactic `EncodedBySyn` via the model's `corr`,
`FnDef.EncodedBySyn.toEncodedBy`), and `assertsCorr` pins each SMT assertion to its source
assumption/distinctness group. The trailing negated obligation is exposed separately (it is the
goal). -/

/-- **The source and emitted contexts correspond.** For a well-formed `P` that encodes to
    `prog`, `prog` splits as a COMMAND BLOCK `block` followed by the single trailing
    `assert (not goal)`, and the source-side fold `OblProgram.ctx P` corresponds (`EncInv`) to
    the block-folded SMT context `block.foldl SMTCtx.step {}`:
      • emitted UF ids permute the source `Φ`/`Ψ` names, and every source entry's `encodeSig`
        UF sits in the emitted `ufs` (⇒ `UFCtxWF`/`FNameCtxWF` at the emitted context);
      • every emitted `IF` is the syntactic encoding of some `fnDef`/`varDef` (the per-function
        bridges then upgrade this via the model's `corr`);
      • every emitted assertion is a source assumption's or distinctness group's encoding.
    The correspondence is stated at the BLOCK: the trailing obligation `assert` is `goal`'s
    NEGATION, exposed SEPARATELY (`hgoal`/`hsplit`). Since an `.assert` leaves `ufs`/`fs` untouched,
    the ufs- and fs-level facts transfer to `SMTProgram.ctx prog` unchanged when the model transfer
    needs them there. -/
theorem encode_encInv {P : OblProgram} (h : OblProgramWF P) {prog : SMTProgram}
    (henc : encode P = .ok prog) :
    ∃ block goal,
      prog = block ++ [.assert (.app (.core .not) [goal] .bool), .checkSat] ∧
      encodeBlock P = .ok block ∧
      toSMTTerm [] P.obligation = .ok goal ∧
      EncInv (OblProgram.ctx P) (SMTProgram.ctx block) := by
  -- the command block: `EncInv` at the end of the source/SMT command folds
  obtain ⟨block, hblock, _, hfinv⟩ :=
    encodeCmds_wf P.cmds (c := {}) (s := {}) ⟨by simp [OblCtx.names], by intro x hx; simp at hx, by intro f hf; simp at hf, by intro t ht; simp at ht⟩
      OblCtx.Good.empty h.cmdsWF
  -- the obligation encodes; reconstruct `prog = block ++ [assert (not goal), checkSat]`
  obtain ⟨huwf, hψwf⟩ := prefix_fnameCtxWF h (rest := []) (c := P.cmds.foldl OblCtx.step {})
    ⟨P.cmds, by simp, rfl⟩
  have hΦ : (P.cmds.foldl OblCtx.step {}).Φ = P.Φ := by rw [OblProgram.Φ, OblProgram.ctx]
  have hΨ : (P.cmds.foldl OblCtx.step {}).Ψ = P.Ψ := by rw [OblProgram.Ψ, OblProgram.ctx]
  rw [hΦ] at huwf; rw [hΨ] at hψwf
  obtain ⟨goal, hgoal⟩ := toSMTTerm_closed_succeeds h.obligationWF huwf hψwf
  have hprog : prog = block ++ [.assert (.app (.core .not) [goal] .bool), .checkSat] := by
    have : encode P = .ok (block ++ [.assert (.app (.core .not) [goal] .bool), .checkSat]) := by
      simp only [encode, encodeBlock, hblock, hgoal, bind, Except.bind]
    rw [henc] at this; exact (Except.ok.inj this)
  exact ⟨block, goal, hprog, hblock, hgoal, hfinv⟩

/-- **`encodeUnsat` is total on well-formed input** — the twin of `encode_succeeds`. The command
    block and the obligation encode exactly as in the validity direction; only the trailing literal
    (`assert goal` instead of `assert (not goal)`) differs, so totality transfers verbatim. -/
theorem encodeUnsat_succeeds {P : OblProgram} (h : OblProgramWF P) :
    ∃ prog, encodeUnsat P = .ok prog := by
  obtain ⟨cmds, hcmds⟩ := encodeCmds_succeeds h [] P.cmds (by simp) h.cmdsWF
  obtain ⟨huwf, hψwf⟩ := prefix_fnameCtxWF h (rest := []) (c := P.cmds.foldl OblCtx.step {})
    ⟨P.cmds, by simp, rfl⟩
  have hΦ : (P.cmds.foldl OblCtx.step {}).Φ = P.Φ := by rw [OblProgram.Φ, OblProgram.ctx]
  have hΨ : (P.cmds.foldl OblCtx.step {}).Ψ = P.Ψ := by rw [OblProgram.Ψ, OblProgram.ctx]
  rw [hΦ] at huwf; rw [hΨ] at hψwf
  obtain ⟨goal, hgoal⟩ := toSMTTerm_closed_succeeds h.obligationWF huwf hψwf
  exact ⟨cmds ++ [.assert goal, .checkSat],
    by simp only [encodeUnsat, encodeBlock, hcmds, hgoal, bind, Except.bind]⟩

/-- **The source and emitted contexts correspond, unsat direction** — the twin of `encode_encInv`.
    `encodeUnsat P` splits as the SAME command `block` as `encode P` followed by the trailing
    `assert goal` (the obligation AS-IS, un-negated), and the source-side fold `OblProgram.ctx P`
    corresponds (`EncInv`) to the block-folded SMT context. Since the `block` and `goal` are
    computed identically to the validity direction (only the trailing literal changes), the proof
    reuses the exact block/goal reconstruction. The trailing `assert goal` leaves `ufs`/`fs`
    untouched, so the ufs/fs-level facts transfer to `SMTProgram.ctx prog` unchanged. -/
theorem encodeUnsat_encInv {P : OblProgram} (h : OblProgramWF P) {prog : SMTProgram}
    (henc : encodeUnsat P = .ok prog) :
    ∃ block goal,
      prog = block ++ [.assert goal, .checkSat] ∧
      encodeBlock P = .ok block ∧
      toSMTTerm [] P.obligation = .ok goal ∧
      EncInv (OblProgram.ctx P) (SMTProgram.ctx block) := by
  obtain ⟨block, hblock, _, hfinv⟩ :=
    encodeCmds_wf P.cmds (c := {}) (s := {}) ⟨by simp [OblCtx.names], by intro x hx; simp at hx, by intro f hf; simp at hf, by intro t ht; simp at ht⟩
      OblCtx.Good.empty h.cmdsWF
  obtain ⟨huwf, hψwf⟩ := prefix_fnameCtxWF h (rest := []) (c := P.cmds.foldl OblCtx.step {})
    ⟨P.cmds, by simp, rfl⟩
  have hΦ : (P.cmds.foldl OblCtx.step {}).Φ = P.Φ := by rw [OblProgram.Φ, OblProgram.ctx]
  have hΨ : (P.cmds.foldl OblCtx.step {}).Ψ = P.Ψ := by rw [OblProgram.Ψ, OblProgram.ctx]
  rw [hΦ] at huwf; rw [hΨ] at hψwf
  obtain ⟨goal, hgoal⟩ := toSMTTerm_closed_succeeds h.obligationWF huwf hψwf
  have hprog : prog = block ++ [.assert goal, .checkSat] := by
    have : encodeUnsat P = .ok (block ++ [.assert goal, .checkSat]) := by
      simp only [encodeUnsat, encodeBlock, hblock, hgoal, bind, Except.bind]
    rw [henc] at this; exact (Except.ok.inj this)
  exact ⟨block, goal, hprog, hblock, hgoal, hfinv⟩

/-- **`encodeIncremental` is total on well-formed input** — the block and obligation encode exactly
    as in the other directions; only the two trailing `checkSatAssuming` queries differ. -/
theorem encodeIncremental_succeeds {P : OblProgram} (h : OblProgramWF P) :
    ∃ prog, encodeIncremental P = .ok prog := by
  obtain ⟨cmds, hcmds⟩ := encodeCmds_succeeds h [] P.cmds (by simp) h.cmdsWF
  obtain ⟨huwf, hψwf⟩ := prefix_fnameCtxWF h (rest := []) (c := P.cmds.foldl OblCtx.step {})
    ⟨P.cmds, by simp, rfl⟩
  have hΦ : (P.cmds.foldl OblCtx.step {}).Φ = P.Φ := by rw [OblProgram.Φ, OblProgram.ctx]
  have hΨ : (P.cmds.foldl OblCtx.step {}).Ψ = P.Ψ := by rw [OblProgram.Ψ, OblProgram.ctx]
  rw [hΦ] at huwf; rw [hΨ] at hψwf
  obtain ⟨goal, hgoal⟩ := toSMTTerm_closed_succeeds h.obligationWF huwf hψwf
  exact ⟨cmds ++ [.checkSatAssuming [goal], .checkSatAssuming [.app (.core .not) [goal] .bool]],
    by simp only [encodeIncremental, encodeBlock, hcmds, hgoal, bind, Except.bind]⟩

/-- **The source and emitted contexts correspond, incremental shape.** `encodeIncremental P` splits
    as the SAME command `block` as the other directions, followed by the two trailing
    `checkSatAssuming` queries. The block-level `EncInv` is identical (the checks don't touch the
    contexts); the two transient literals `goal` / `not goal` are exposed via the goal-encoding. -/
theorem encodeIncremental_encInv {P : OblProgram} (h : OblProgramWF P) {prog : SMTProgram}
    (henc : encodeIncremental P = .ok prog) :
    ∃ block goal,
      prog = block ++ [.checkSatAssuming [goal],
                       .checkSatAssuming [.app (.core .not) [goal] .bool]] ∧
      encodeBlock P = .ok block ∧
      toSMTTerm [] P.obligation = .ok goal ∧
      EncInv (OblProgram.ctx P) (SMTProgram.ctx block) := by
  obtain ⟨block, hblock, _, hfinv⟩ :=
    encodeCmds_wf P.cmds (c := {}) (s := {}) ⟨by simp [OblCtx.names], by intro x hx; simp at hx, by intro f hf; simp at hf, by intro t ht; simp at ht⟩
      OblCtx.Good.empty h.cmdsWF
  obtain ⟨huwf, hψwf⟩ := prefix_fnameCtxWF h (rest := []) (c := P.cmds.foldl OblCtx.step {})
    ⟨P.cmds, by simp, rfl⟩
  have hΦ : (P.cmds.foldl OblCtx.step {}).Φ = P.Φ := by rw [OblProgram.Φ, OblProgram.ctx]
  have hΨ : (P.cmds.foldl OblCtx.step {}).Ψ = P.Ψ := by rw [OblProgram.Ψ, OblProgram.ctx]
  rw [hΦ] at huwf; rw [hΨ] at hψwf
  obtain ⟨goal, hgoal⟩ := toSMTTerm_closed_succeeds h.obligationWF huwf hψwf
  have hprog : prog = block ++ [.checkSatAssuming [goal],
                                .checkSatAssuming [.app (.core .not) [goal] .bool]] := by
    have : encodeIncremental P = .ok (block ++ [.checkSatAssuming [goal],
                                    .checkSatAssuming [.app (.core .not) [goal] .bool]]) := by
      simp only [encodeIncremental, encodeBlock, hblock, hgoal, bind, Except.bind]
    rw [henc] at this; exact (Except.ok.inj this)
  exact ⟨block, goal, hprog, hblock, hgoal, hfinv⟩

end Core.Construct
