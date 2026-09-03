/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

import all Strata.Languages.Core.PrototypeSMTGen.FunDef

/-!
# Decidability of `LExpr.HasSimpType` via syntax-directed inference

This file decides the SMT-encodable typing judgment `LExpr.HasSimpType` (and its mutual companion
`LExpr.AppSpine`). The judgment is deterministic — each expression has at most one type, since
annotations pin the free-variable/UDF heads and the predefined-operator table is functional — so it
is decided by an inference function (`inferSimpType`/`inferSpine`/`inferHead`) proven to agree with
the relation, via soundness and completeness. The `Decidable (LExpr.HasSimpType …)` instance falls
out of the resulting `inferSimpType_iff`.

Decidability is the prerequisite for discharging concrete typing facts by `native_decide` (closed
terms reduce once `HasSimpType` is `Decidable`). The file depends only on the judgment (from
`FunDef`), so the inference machinery is reusable and importable anywhere.

Key definitions: `isBaseMonoTy`, `coreOpSig`, `inferHead`, `inferSimpType`, `inferSpine`.
Key results: `inferSimpType_sound`, `inferSimpType_complete`, `inferSimpType_iff`, and the
`Decidable (LExpr.HasSimpType …)` instance.
-/

open Core Lambda Imperative Strata.SMT Std

/-! ## Leaf deciders

`MonoTyIsBase` and `CoreOpHasType` are the two finite/table-driven side conditions of the judgment.
Each gets a computable recognizer and an iff, so the inference function can consult them and the
soundness/completeness proofs can round-trip through them. -/

/-- Computable recognizer for `MonoTyIsBase`: `true` on exactly the four base monotypes. -/
def isBaseMonoTy : LMonoTy → Bool
  | .tcons "bool" []   => true
  | .tcons "int" []    => true
  | .tcons "string" [] => true
  | .bitvec _          => true
  | _                  => false

theorem isBaseMonoTy_iff {τ : LMonoTy} : LExpr.MonoTyIsBase τ ↔ isBaseMonoTy τ = true := by
  constructor
  · intro h; cases h <;> rfl
  · intro h
    unfold isBaseMonoTy at h
    split at h
    · exact .bool
    · exact .int
    · exact .string
    · exact .bitvec
    · exact absurd h (by simp)

instance (τ : LMonoTy) : Decidable (LExpr.MonoTyIsBase τ) :=
  decidable_of_iff _ isBaseMonoTy_iff.symm

/-- The `(argTys, retTy)` signature of a predefined Core operator — `some` on exactly the
    operators that head a `CoreOpHasType` constructor, mirroring that table. The computable
    twin of `CoreOpHasType`; `none` marks a UDF symbol. -/
def coreOpSig : CoreOp → Option (List LMonoTy × LMonoTy)
  | .numeric ⟨.int, .Neg⟩ => some ([.tcons "int" []], .tcons "int" [])
  | .bool .Not            => some ([.tcons "bool" []], .tcons "bool" [])
  | .numeric ⟨.int, .Add⟩ | .numeric ⟨.int, .Sub⟩ | .numeric ⟨.int, .Mul⟩
  | .numeric ⟨.int, .Div⟩ | .numeric ⟨.int, .Mod⟩ =>
      some ([.tcons "int" [], .tcons "int" []], .tcons "int" [])
  | .numeric ⟨.int, .Lt⟩ | .numeric ⟨.int, .Le⟩ | .numeric ⟨.int, .Gt⟩ | .numeric ⟨.int, .Ge⟩ =>
      some ([.tcons "int" [], .tcons "int" []], .tcons "bool" [])
  | .bool .And | .bool .Or | .bool .Implies | .bool .Equiv =>
      some ([.tcons "bool" [], .tcons "bool" []], .tcons "bool" [])
  | _ => none

theorem coreOpSig_iff {op : CoreOp} {acc : List LMonoTy} {rty : LMonoTy} :
    LExpr.CoreOpHasType op acc rty ↔ coreOpSig op = some (acc, rty) := by
  constructor
  · intro h; cases h <;> rfl
  · intro h
    cases op with
    | numeric nop =>
      obtain ⟨ty, kind⟩ := nop
      cases ty <;> cases kind <;>
        simp only [coreOpSig, Option.some.injEq, Prod.mk.injEq] at h <;>
        first
          | (obtain ⟨rfl, rfl⟩ := h; constructor)
          | exact absurd h (by simp)
    | bool kind =>
      cases kind <;>
        simp only [coreOpSig, Option.some.injEq, Prod.mk.injEq] at h <;>
        first
          | (obtain ⟨rfl, rfl⟩ := h; constructor)
          | exact absurd h (by simp)
    | _ => simp only [coreOpSig] at h; exact absurd h (by simp)

/-- `coreOpSig` and `IsPredefinedOp` agree: a symbol is predefined iff its signature resolves. -/
theorem coreOpSig_isSome_iff_predefined {name : String} :
    IsPredefinedOp name ↔ (coreOpSig (CoreOp.ofString name)).isSome := by
  rw [IsPredefinedOp]
  constructor
  · rintro ⟨acc, rty, h⟩; rw [coreOpSig_iff.mp h]; rfl
  · intro h
    obtain ⟨⟨acc, rty⟩, hsig⟩ := Option.isSome_iff_exists.mp h
    exact ⟨acc, rty, coreOpSig_iff.mpr hsig⟩

theorem coreOpSig_none_of_not_predefined {name : String} (h : ¬ IsPredefinedOp name) :
    coreOpSig (CoreOp.ofString name) = none := by
  match hsig : coreOpSig (CoreOp.ofString name) with
  | none => rfl
  | some (acc, rty) => exact absurd (⟨acc, rty, coreOpSig_iff.mpr hsig⟩) h

/-! ## The inference function

`inferSimpType` returns the (unique) type of a `HasSimpType`-typeable expression, `none` otherwise.
`inferSpine` types an application head applied to pending argument types `acc` (the `AppSpine`
companion). `inferHead` handles the non-recursive spine heads (`.fvar`, `.op`), split out so the
mutual recursion is structural. -/

/-- The non-recursive spine heads: a free variable (resolved through `Φ`) or an operator
    (predefined via `coreOpSig`, else a UDF resolved through `Ψ`). Returns the head's return
    type when its declared signature decomposes into exactly the pending args `acc`. -/
def inferHead (Φ : FVarCtx) (Ψ : FnCtx) : Expression.Expr → List LMonoTy → Option LMonoTy
  | .fvar () f (some τ), acc =>
      if (f.name, τ) ∈ Φ then
        match collectArrowTy τ with
        | (acc', rty) => if acc' = acc ∧ isBaseMonoTy rty then some rty else none
      else none
  | .op () o (some oty), acc =>
      match coreOpSig (CoreOp.ofString o.name) with
      | some (sigAcc, sigRty) =>
          if sigAcc = acc ∧ collectArrowTy oty = (acc, sigRty) then some sigRty else none
      | none =>
          if (o.name, oty) ∈ Ψ then
            match collectArrowTy oty with
            | (acc', rty) => if acc' = acc ∧ isBaseMonoTy rty then some rty else none
          else none
  | _, _ => none

/-- A symbol with no `coreOpSig` is not predefined. -/
theorem not_predefined_of_coreOpSig_none {name : String}
    (h : coreOpSig (CoreOp.ofString name) = none) : ¬ IsPredefinedOp name := by
  intro hpre
  rw [coreOpSig_isSome_iff_predefined, h] at hpre
  exact absurd hpre (by simp)

/-- **`inferHead` soundness.** A successful head inference witnesses an `AppSpine` derivation
    (a single non-recursive head constructor: `.fvar`, `.op`, or `.fnOp`). -/
theorem inferHead_sound {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {head : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (h : inferHead Φ Ψ head acc = some rty) : LExpr.AppSpine Φ Ψ Δ head acc rty := by
  unfold inferHead at h
  split at h
  · -- `.fvar () f (some τ)`
    rename_i f τ
    split at h
    · rename_i hmem
      split at h
      rename_i acc' rty' hcol
      split at h
      · rename_i hcond
        obtain ⟨hacc, hbase⟩ := hcond
        subst hacc
        simp only [Option.some.injEq] at h; subst h
        exact .fvar _ _ _ _ hmem hcol (isBaseMonoTy_iff.mpr hbase)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `.op () o (some oty)`
    rename_i o oty
    split at h
    · -- predefined
      rename_i sigAcc sigRty hsig
      split at h
      · rename_i hcond
        obtain ⟨hacc, hcol⟩ := hcond
        subst hacc
        simp only [Option.some.injEq] at h; subst h
        exact .op _ _ _ _ (coreOpSig_iff.mpr hsig) hcol
      · exact absurd h (by simp)
    · -- UDF
      rename_i hsig
      split at h
      · rename_i hmem
        split at h
        rename_i acc' rty' hcol
        split at h
        · rename_i hcond
          obtain ⟨hacc, hbase⟩ := hcond
          subst hacc
          simp only [Option.some.injEq] at h; subst h
          exact .fnOp _ _ _ _ hmem (not_predefined_of_coreOpSig_none hsig) hcol
            (isBaseMonoTy_iff.mpr hbase)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **`inferHead` completeness.** Every `AppSpine` head derivation is found by `inferHead`. -/
theorem inferHead_complete {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {head : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (h : LExpr.AppSpine Φ Ψ Δ head acc rty)
    (hnotapp : ∀ fn arg, head ≠ .app () fn arg) : inferHead Φ Ψ head acc = some rty := by
  cases h with
  | app fn arg aty acc' rty' harg hrest => exact absurd rfl (hnotapp fn arg)
  | fvar f τ acc rty hmem hcol hbase =>
      simp only [inferHead, hcol, hmem, isBaseMonoTy_iff.mp hbase, and_self, ↓reduceIte]
  | op o oty acc rty hop hcol =>
      simp only [inferHead, coreOpSig_iff.mp hop, hcol, and_self, ↓reduceIte]
  | fnOp o oty acc rty hmem hnpre hcol hbase =>
      simp only [inferHead, coreOpSig_none_of_not_predefined hnpre, hmem, hcol,
        isBaseMonoTy_iff.mp hbase, and_self, ↓reduceIte]

mutual
/-- Infer the SMT-encodable type of `e` in contexts `(Φ, Ψ)` and bvar context `Δ`; `none` if
    `e` is not `HasSimpType`-typeable. -/
def inferSimpType (Φ : FVarCtx) (Ψ : FnCtx) (Δ : BVarCtx) (e : Expression.Expr) : Option LMonoTy :=
  match e with
  | .const () c => if isBaseMonoTy c.ty then some c.ty else none
  | .bvar () i =>
      match Δ[i]? with
      | some τ => if isBaseMonoTy τ then some τ else none
      | none   => none
  | .ite () c t e_ =>
      match inferSimpType Φ Ψ Δ c, inferSimpType Φ Ψ Δ t, inferSimpType Φ Ψ Δ e_ with
      | some (.tcons "bool" []), some τt, some τe => if τt = τe then some τt else none
      | _, _, _ => none
  | .eq () e1 e2 =>
      match inferSimpType Φ Ψ Δ e1, inferSimpType Φ Ψ Δ e2 with
      | some τ1, some τ2 => if τ1 = τ2 ∧ isBaseMonoTy τ1 then some (.tcons "bool" []) else none
      | _, _ => none
  | .quant () _ _ (some qty) trigger body =>
      -- The trigger is semantically inert: it need only SMT-type to some base type, so we
      -- infer it.
      if isBaseMonoTy qty then
        match inferSimpType Φ Ψ (qty :: Δ) trigger, inferSimpType Φ Ψ (qty :: Δ) body with
        | some _, some (.tcons "bool" []) => some (.tcons "bool" [])
        | _, _ => none
      else none
  | .fvar () f (some τ) => inferHead Φ Ψ (.fvar () f (some τ)) []
  | .app () fn arg =>
      match inferSimpType Φ Ψ Δ arg with
      | some aty => inferSpine Φ Ψ Δ fn [aty]
      | none     => none
  | _ => none

/-- Type an application head `e` applied to the pending argument types `acc` (rightmost last),
    yielding the base return type; the computable companion of `AppSpine`. -/
def inferSpine (Φ : FVarCtx) (Ψ : FnCtx) (Δ : BVarCtx)
    (e : Expression.Expr) (acc : List LMonoTy) : Option LMonoTy :=
  match e with
  | .app () fn arg =>
      match inferSimpType Φ Ψ Δ arg with
      | some aty => inferSpine Φ Ψ Δ fn (aty :: acc)
      | none     => none
  | head => inferHead Φ Ψ head acc
end

/-! ## Soundness (inference ⇒ judgment) -/

mutual
theorem inferSimpType_sound {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy}
    (h : inferSimpType Φ Ψ Δ e = some τ) : LExpr.HasSimpType Φ Ψ Δ e τ := by
  unfold inferSimpType at h
  split at h
  · -- `.const () c`
    rename_i c
    split at h
    · rename_i hbase
      simp only [Option.some.injEq] at h; subst h
      exact .const c (isBaseMonoTy_iff.mpr hbase)
    · exact absurd h (by simp)
  · -- `.bvar () i`
    rename_i i
    split at h
    · rename_i τ' hlook
      split at h
      · rename_i hbase
        simp only [Option.some.injEq] at h; subst h
        exact .bvar i τ' hlook (isBaseMonoTy_iff.mpr hbase)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `.ite () c t e_`
    rename_i c t e_
    split at h
    · rename_i τt τe hc ht he_
      -- `hc : infer c = some (bool)`, `ht : infer t = some τt`, `he_ : infer e_ = some τe`
      split at h
      · rename_i heq; subst heq
        simp only [Option.some.injEq] at h; subst h
        exact .ite c t τt e_ (inferSimpType_sound hc) (inferSimpType_sound ht)
          (inferSimpType_sound he_)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `.eq () e1 e2`
    rename_i e1 e2
    split at h
    · rename_i τ1 τ2 he1 he2
      split at h
      · rename_i hcond
        obtain ⟨heq, hbase⟩ := hcond; subst heq
        simp only [Option.some.injEq] at h; subst h
        exact .eq e1 e2 τ1 (isBaseMonoTy_iff.mpr hbase) (inferSimpType_sound he1)
          (inferSimpType_sound he2)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `.quant () k _ (some qty) trigger body`
    rename_i k _ qty trigger body
    split at h
    · rename_i hbase
      -- inner match on `(inferSimpType trigger, inferSimpType body)`
      split at h
      · rename_i τtr hbtr hbody
        simp only [Option.some.injEq] at h; subst h
        exact .quant qty body k _ trigger τtr (isBaseMonoTy_iff.mpr hbase)
          (inferSimpType_sound hbtr) (inferSimpType_sound hbody)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `.fvar () f (some τ)` — nullary head
    rename_i f τ'
    exact .fvarNullary f τ' τ (inferHead_sound h)
  · -- `.app () fn arg`
    rename_i fn arg
    split at h
    · rename_i aty harg
      exact .app fn arg τ
        (.app fn arg aty [] τ (inferSimpType_sound harg) (inferSpine_sound h))
    · exact absurd h (by simp)
  · -- unsupported forms
    exact absurd h (by simp)

theorem inferSpine_sound {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (h : inferSpine Φ Ψ Δ e acc = some rty) : LExpr.AppSpine Φ Ψ Δ e acc rty := by
  unfold inferSpine at h
  split at h
  · -- `.app () fn arg`
    rename_i fn arg
    split at h
    · rename_i aty harg
      exact .app fn arg aty acc rty (inferSimpType_sound harg) (inferSpine_sound h)
    · exact absurd h (by simp)
  · -- non-`.app` head
    exact inferHead_sound h
end

/-! ## Completeness (judgment ⇒ inference) -/

mutual
theorem inferSimpType_complete {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy}
    (h : LExpr.HasSimpType Φ Ψ Δ e τ) : inferSimpType Φ Ψ Δ e = some τ := by
  match h with
  | .const c hbase =>
      simp only [inferSimpType, isBaseMonoTy_iff.mp hbase, ↓reduceIte]
  | .bvar i τ hlook hbase =>
      simp only [inferSimpType, hlook, isBaseMonoTy_iff.mp hbase, ↓reduceIte]
  | .app fn arg rty hspine =>
      -- `inferSimpType (.app fn arg) = inferSpine (.app fn arg) []` by definition.
      show inferSpine Φ Ψ Δ (.app () fn arg) [] = some rty
      exact inferSpine_complete hspine
  | .fvarNullary f τ rty hspine =>
      simp only [inferSimpType]
      exact inferHead_complete hspine (by intro fn arg hc; nomatch hc)
  | .ite c t τ e_ hc ht he_ =>
      simp only [inferSimpType, inferSimpType_complete hc, inferSimpType_complete ht,
        inferSimpType_complete he_, ↓reduceIte]
  | .eq e1 e2 τ hbase he1 he2 =>
      simp only [inferSimpType, inferSimpType_complete he1, inferSimpType_complete he2,
        isBaseMonoTy_iff.mp hbase, and_self, ↓reduceIte]
  | .quant qty body k name tr τtr hbase htr hbody =>
      -- both trigger and body infer to `some` (trigger to `τtr`, body to `bool`); guard is `isBaseMonoTy qty`
      simp only [inferSimpType, isBaseMonoTy_iff.mp hbase, ↓reduceIte,
        inferSimpType_complete htr, inferSimpType_complete hbody]

theorem inferSpine_complete {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (h : LExpr.AppSpine Φ Ψ Δ e acc rty) : inferSpine Φ Ψ Δ e acc = some rty := by
  match h with
  | .app fn arg aty acc' rty' harg hrest =>
      simp only [inferSpine, inferSimpType_complete harg]
      exact inferSpine_complete hrest
  | .fvar f τ acc rty hmem hcol hbase =>
      simp only [inferSpine]
      exact inferHead_complete (LExpr.AppSpine.fvar (Δ := Δ) _ _ _ _ hmem hcol hbase)
        (by intro fn arg hc; nomatch hc)
  | .op o oty acc rty hop hcol =>
      simp only [inferSpine]
      exact inferHead_complete (LExpr.AppSpine.op (Δ := Δ) _ _ _ _ hop hcol)
        (by intro fn arg hc; nomatch hc)
  | .fnOp o oty acc rty hmem hnpre hcol hbase =>
      simp only [inferSpine]
      exact inferHead_complete (LExpr.AppSpine.fnOp (Δ := Δ) _ _ _ _ hmem hnpre hcol hbase)
        (by intro fn arg hc; nomatch hc)
end

/-! ## The `Decidable` instance -/

theorem inferSimpType_iff {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy} :
    LExpr.HasSimpType Φ Ψ Δ e τ ↔ inferSimpType Φ Ψ Δ e = some τ :=
  ⟨inferSimpType_complete, inferSimpType_sound⟩

instance {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr} {τ : LMonoTy} :
    Decidable (LExpr.HasSimpType Φ Ψ Δ e τ) :=
  decidable_of_iff _ inferSimpType_iff.symm
