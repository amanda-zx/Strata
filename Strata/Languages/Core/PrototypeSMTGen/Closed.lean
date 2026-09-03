/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public import Strata.Languages.Core.Program
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.SMT.Term
public import Strata.DL.SMT.Factory

/-!
# Closed `LExpr`-to-SMT translation and its soundness

This file defines a translation from a simply-typed, closed (bound variables only) fragment
of Core `LExpr` expressions into SMT `Term`s, together with a type checker and a denotational
semantics for both sides, and proves the translation type-preserving and semantics-preserving.
Judgments are `Prop`-valued, and denotation and compilation use expression-level type checkers.

Key definitions: `LExpr.HasSimpType` (the restricted typing judgment), `toSMTTerm` (the
translation), `Term.typeCheck` and `SMTTerm.denote` (SMT-side typing and denotation).
Key results: `toSMTTerm_typeChecks` (type preservation) and `toSMTTerm_sound` (semantic
soundness).
-/

open Core Lambda Imperative Strata.SMT Std

/-! ## Restrictions on Lambda types and expressions -/

inductive LExpr.MonoTyIsBase : LMonoTy → Prop where
  | bool : MonoTyIsBase (.tcons "bool" [])
  | int : MonoTyIsBase (.tcons "int" [])
  | string : MonoTyIsBase (.tcons "string" [])
  | bitvec : MonoTyIsBase (.bitvec n)


/-! ## Restriction to boolean and integer operators -/

/-- Unary ops: one argument, base return type -/
inductive LExpr.OpIsSimp1 : CoreOp → LMonoTy → LMonoTy → Prop where
  | intNeg : OpIsSimp1 (.numeric ⟨.int, .Neg⟩) (.tcons "int" []) (.tcons "int" [])
  | boolNot : OpIsSimp1 (.bool .Not) (.tcons "bool" []) (.tcons "bool" [])

/-- Binary ops: two arguments, base return type -/
inductive LExpr.OpIsSimp2 : CoreOp → LMonoTy → LMonoTy → LMonoTy → Prop where
  -- Integer binary arithmetic: int → int → int
  | intAdd : OpIsSimp2 (.numeric ⟨.int, .Add⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  | intSub : OpIsSimp2 (.numeric ⟨.int, .Sub⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  | intMul : OpIsSimp2 (.numeric ⟨.int, .Mul⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  | intDiv : OpIsSimp2 (.numeric ⟨.int, .Div⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  | intSafeDiv : OpIsSimp2 (.numeric ⟨.int, .SafeDiv⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  | intMod : OpIsSimp2 (.numeric ⟨.int, .Mod⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  | intSafeMod : OpIsSimp2 (.numeric ⟨.int, .SafeMod⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  | intDivT : OpIsSimp2 (.numeric ⟨.int, .DivT⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  | intSafeDivT : OpIsSimp2 (.numeric ⟨.int, .SafeDivT⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  | intModT : OpIsSimp2 (.numeric ⟨.int, .ModT⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  | intSafeModT : OpIsSimp2 (.numeric ⟨.int, .SafeModT⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "int" [])
  -- Integer comparisons: int → int → bool
  | intLt : OpIsSimp2 (.numeric ⟨.int, .Lt⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "bool" [])
  | intLe : OpIsSimp2 (.numeric ⟨.int, .Le⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "bool" [])
  | intGt : OpIsSimp2 (.numeric ⟨.int, .Gt⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "bool" [])
  | intGe : OpIsSimp2 (.numeric ⟨.int, .Ge⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "bool" [])
  -- Boolean binary: bool → bool → bool
  | boolAnd : OpIsSimp2 (.bool .And) (.tcons "bool" []) (.tcons "bool" []) (.tcons "bool" [])
  | boolOr : OpIsSimp2 (.bool .Or) (.tcons "bool" []) (.tcons "bool" []) (.tcons "bool" [])
  | boolImplies : OpIsSimp2 (.bool .Implies) (.tcons "bool" []) (.tcons "bool" []) (.tcons "bool" [])
  | boolEquiv : OpIsSimp2 (.bool .Equiv) (.tcons "bool" []) (.tcons "bool" []) (.tcons "bool" [])

inductive LExpr.HasSimpType : List LMonoTy → Expression.Expr → LMonoTy → Prop where
  | const : MonoTyIsBase c.ty → HasSimpType Δ (.const () c) c.ty
  | bvar : Δ[i]? = some τ → MonoTyIsBase τ → HasSimpType Δ (.bvar () i) τ
  | app1 : OpIsSimp1 (CoreOp.ofString o.name) aty rty →
    HasSimpType Δ arg aty →
    HasSimpType Δ (.app () (.op () o (some (.tcons "arrow" [aty, rty]))) arg) rty
  | app2 : OpIsSimp2 (CoreOp.ofString o.name) aty1 aty2 rty →
    HasSimpType Δ arg1 aty1 →
    HasSimpType Δ arg2 aty2 →
    HasSimpType Δ (.app () (.app () (.op () o (some (.tcons "arrow" [aty1, .tcons "arrow" [aty2, rty]]))) arg1) arg2) rty
  | ite : HasSimpType Δ c (.tcons "bool" []) → HasSimpType Δ t τ →
    HasSimpType Δ e τ → HasSimpType Δ (.ite () c t e) τ
  | eq : MonoTyIsBase τ → HasSimpType Δ e1 τ → HasSimpType Δ e2 τ →
    HasSimpType Δ (.eq () e1 e2) (.tcons "bool" [])
  | quant : MonoTyIsBase qty → HasSimpType (qty :: Δ) body (.tcons "bool" []) →
    HasSimpType Δ (.quant () k name (some qty) (.const () (.boolConst true)) body) (.tcons "bool" [])


/-! ## Embedding into the `HasTypeA` judgment -/

theorem HasSimpType_implies_HasTypeA :
    {Δ : List LMonoTy} → {e : Expression.Expr} → {τ : LMonoTy} →
    LExpr.HasSimpType Δ e τ → LExpr.HasTypeA Δ e τ := by
  intro Δ e τ h
  induction h with
  | const _ => exact .const
  | bvar hi _ => exact .bvar hi
  | app1 _ _ ih_arg => exact .app .op ih_arg
  | app2 _ _ _ ih1 ih2 => exact .app (.app .op ih1) ih2
  | ite _ _ _ ihc iht ihe => exact .ite ihc iht ihe
  | eq _ _ _ ih1 ih2 => exact .eq ih1 ih2
  | quant _ _ ih_body => exact .quant (by exact .const) ih_body

/-- Consistency of the operator interpretation with SMT semantics: `opInterp`
    assigns the standard meaning to each operator at its curried arrow type.
    Quantified over all names that `CoreOp.ofString` maps to a given structured
    op, since several names may map to the same op. -/
structure OpInterpConsistent (opInterp : Lambda.OpInterp simpTcInterp) : Prop where
  -- Unary integer: Int → Int
  neg : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Neg⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "int" []])
        = (fun x : Int => -x)
  -- Unary boolean: Bool → Bool
  not : ∀ name, CoreOp.ofString name = .bool .Not →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "bool" []])
        = (fun x : Bool => !x)
  -- Binary integer arithmetic: Int → Int → Int
  add : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Add⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x + y)
  sub : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Sub⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x - y)
  mul : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Mul⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x * y)
  div : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Div⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x / y)
  safeDiv : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .SafeDiv⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x / y)
  mod_ : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Mod⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x % y)
  safeMod : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .SafeMod⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x % y)
  divT : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .DivT⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x / y)
  safeDivT : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .SafeDivT⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x / y)
  modT : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .ModT⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x % y)
  safeModT : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .SafeModT⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x % y)
  -- Integer comparisons: Int → Int → Bool
  lt : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Lt⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]])
        = (fun x y : Int => decide (x < y))
  le : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Le⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]])
        = (fun x y : Int => decide (x ≤ y))
  gt : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Gt⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]])
        = (fun x y : Int => decide (x > y))
  ge : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Ge⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]])
        = (fun x y : Int => decide (x ≥ y))
  -- Binary boolean: Bool → Bool → Bool
  and_ : ∀ name, CoreOp.ofString name = .bool .And →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]])
        = (fun x y : Bool => x && y)
  or_ : ∀ name, CoreOp.ofString name = .bool .Or →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]])
        = (fun x y : Bool => x || y)
  implies : ∀ name, CoreOp.ofString name = .bool .Implies →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]])
        = (fun x y : Bool => !x || y)
  equiv : ∀ name, CoreOp.ofString name = .bool .Equiv →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]])
        = (fun x y : Bool => decide (x = y))

/-! ## `LExpr` denotation for the simple fragment -/

/-- Type constructor interpretation for the simple fragment: no user-defined types,
    so any unrecognized type constructor is interpreted as Unit. -/
noncomputable def simpTcInterp : Lambda.TyConstrInterp := fun _ _ => Unit

instance : Lambda.TyConstrInterp.AllInhabited simpTcInterp where
  inhabited := fun _ _ => ⟨()⟩

/-- No type variables in the simple fragment. -/
def simpTyVarVal : Lambda.TyVarVal := fun _ => .tcons "bool" []

/-- No free variables in the simple fragment. -/
noncomputable def simpFvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp :=
  fun _ _ => (Lambda.SortDenote.instInhabited _).default

/-- Denotation of a simply-typed `LExpr` with bound variable context `Δ`,
    parameterized by `opInterp`, which gives semantics to built-in operators. -/
noncomputable def simpDenote
    (opInterp : Lambda.OpInterp simpTcInterp)
    {Δ : List LMonoTy}
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (e : Expression.Expr) (τ : LMonoTy)
    (h : LExpr.HasTypeA Δ e τ)
    : Lambda.TyDenote simpTcInterp simpTyVarVal τ :=
  LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal e τ h


/-! ## SMT type checker -/

mutual
def Term.typeCheck (Γ : List TermVar) : Term → Option TermType
  | .prim p => some p.typeOf
  | .var v => if v ∈ Γ then some v.ty else none
  | .app (.core .not) [t] _ => do
    let tTy ← typeCheck Γ t
    if tTy == .bool then some .bool else none
  | .app (.core .and) [t1, t2] _ | .app (.core .or) [t1, t2] _
  | .app (.core .implies) [t1, t2] _ => do
    let ty1 ← typeCheck Γ t1
    let ty2 ← typeCheck Γ t2
    if ty1 == .bool && ty2 == .bool then some .bool else none
  | .app (.core .eq) [t1, t2] _ => do
    let ty1 ← typeCheck Γ t1
    let ty2 ← typeCheck Γ t2
    if ty1 == ty2 then some .bool else none
  | .app (.core .ite) [c, t, e] _ => do
    let cTy ← typeCheck Γ c
    let tTy ← typeCheck Γ t
    let eTy ← typeCheck Γ e
    if cTy == .bool && tTy == eTy then some tTy else none
  | .app (.num .neg) [t] _ => do
    let tTy ← typeCheck Γ t
    if tTy == .int then some .int else none
  | .app (.num .add) [t1, t2] _ | .app (.num .sub) [t1, t2] _
  | .app (.num .mul) [t1, t2] _ | .app (.num .div) [t1, t2] _
  | .app (.num .mod) [t1, t2] _ => do
    let ty1 ← typeCheck Γ t1
    let ty2 ← typeCheck Γ t2
    if ty1 == .int && ty2 == .int then some .int else none
  | .app (.num .le) [t1, t2] _ | .app (.num .lt) [t1, t2] _
  | .app (.num .ge) [t1, t2] _ | .app (.num .gt) [t1, t2] _ => do
    let ty1 ← typeCheck Γ t1
    let ty2 ← typeCheck Γ t2
    if ty1 == .int && ty2 == .int then some .bool else none
  | .app (.core .distinct) ts _ => do
    let _ ← typeCheckAllSame Γ ts
    some .bool
  | .quant _ vs [] body => do
    let bodyTy ← typeCheck (vs ++ Γ) body
    if bodyTy == .bool then some .bool else none
  | _ => none

def Term.typeCheckAllSame (Γ : List TermVar) : List Term → Option TermType
  | [] => some .bool
  | [t] => typeCheck Γ t
  | t :: rest => do
    let ty ← typeCheck Γ t
    let ty' ← typeCheckAllSame Γ rest
    if ty == ty' then some ty else none
end

/-! ## SMT type denotation -/

@[reducible] def SMTTyDenote : TermType → Type
  | .prim .bool => Bool
  | .prim .int => Int
  | .prim (.bitvec n) => BitVec n
  | .prim .string => String
  | _ => Unit

/-! ## `typeCheck` inversion lemmas -/

def tc_prim_inv {Γ : List TermVar} {p : TermPrim} {τ : TermType}
    (h : Term.typeCheck Γ (.prim p) = some τ) : τ = p.typeOf := by
  simp [Term.typeCheck] at h; exact h.symm

def tc_var_inv {Γ : List TermVar} {v : TermVar} {τ : TermType}
    (h : Term.typeCheck Γ (.var v) = some τ) : v ∈ Γ ∧ v.ty = τ := by
  simp [Term.typeCheck] at h; exact h

def tc_not_inv {Γ : List TermVar} {t : Term} {rty : TermType} {τ : TermType}
    (h : Term.typeCheck Γ (.app (.core .not) [t] rty) = some τ) :
    Term.typeCheck Γ t = some .bool ∧ τ = .bool := by
  simp only [Term.typeCheck] at h
  revert h
  cases h1 : Term.typeCheck Γ t with
  | none => simp [bind, Option.bind]
  | some ty1 =>
    simp only [bind, Option.bind]
    intro h'
    split at h' <;> simp_all

def Term.typeCheck_boolBin_inv {Γ : List TermVar} {op : Op.Core} {t1 t2 : Term}
    {rty : TermType} {τ : TermType}
    (h : Term.typeCheck Γ (.app (.core op) [t1, t2] rty) = some τ)
    (hop : op = .and ∨ op = .or ∨ op = .implies) :
    Term.typeCheck Γ t1 = some .bool ∧ Term.typeCheck Γ t2 = some .bool ∧ τ = .bool := by
  rcases hop with rfl | rfl | rfl <;> {
    simp only [Term.typeCheck] at h
    revert h
    cases h1 : Term.typeCheck Γ t1 with
    | none => simp [bind, Option.bind]
    | some ty1 =>
      cases h2 : Term.typeCheck Γ t2 with
      | none => simp [bind, Option.bind]
      | some ty2 =>
        simp only [bind, Option.bind]
        intro h'
        split at h' <;> simp_all
  }

def Term.typeCheck_eq_inv {Γ : List TermVar} {t1 t2 : Term} {rty : TermType} {τ : TermType}
    (h : Term.typeCheck Γ (.app (.core .eq) [t1, t2] rty) = some τ) :
    Σ' τ', Term.typeCheck Γ t1 = some τ' ∧ Term.typeCheck Γ t2 = some τ' ∧ τ = .bool := by
  simp only [Term.typeCheck] at h
  revert h
  cases h1 : Term.typeCheck Γ t1 with
  | none => simp [bind, Option.bind]; exact fun h => absurd h (by trivial)
  | some ty1 =>
    cases h2 : Term.typeCheck Γ t2 with
    | none => simp [bind, Option.bind]; exact fun h => absurd h (by trivial)
    | some ty2 =>
      simp only [bind, Option.bind]
      intro h'
      split at h'
      · next heq =>
        have hτ : τ = .bool := by simp at h'; exact h'.symm
        have hteq : ty1 = ty2 := beq_iff_eq.mp heq
        subst hteq
        exact ⟨ty1, rfl, rfl, hτ⟩
      · simp at h'

def Term.typeCheck_ite_inv {Γ : List TermVar} {c t e : Term} {rty : TermType} {τ : TermType}
    (h : Term.typeCheck Γ (.app (.core .ite) [c, t, e] rty) = some τ) :
    Term.typeCheck Γ c = some .bool ∧ Term.typeCheck Γ t = some τ ∧ Term.typeCheck Γ e = some τ := by
  simp only [Term.typeCheck] at h
  revert h
  cases hc : Term.typeCheck Γ c with
  | none => simp [bind, Option.bind]
  | some tyc =>
    cases ht : Term.typeCheck Γ t with
    | none => simp [bind, Option.bind]
    | some tyt =>
      cases he : Term.typeCheck Γ e with
      | none => simp [bind, Option.bind]
      | some tye =>
        simp only [bind, Option.bind]
        intro h'
        split at h' <;> simp_all

def Term.typeCheck_intUn_inv {Γ : List TermVar} {t : Term} {rty : TermType} {τ : TermType}
    (h : Term.typeCheck Γ (.app (.num .neg) [t] rty) = some τ) :
    Term.typeCheck Γ t = some .int ∧ τ = .int := by
  simp only [Term.typeCheck] at h
  revert h
  cases h1 : Term.typeCheck Γ t with
  | none => simp [bind, Option.bind]
  | some ty1 =>
    simp only [bind, Option.bind]
    intro h'
    split at h' <;> simp_all

def Term.typeCheck_intBin_inv {Γ : List TermVar} {op : Op.Num} {t1 t2 : Term}
    {rty : TermType} {τ : TermType}
    (h : Term.typeCheck Γ (.app (.num op) [t1, t2] rty) = some τ)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod) :
    Term.typeCheck Γ t1 = some .int ∧ Term.typeCheck Γ t2 = some .int ∧ τ = .int := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> {
    simp only [Term.typeCheck] at h
    revert h
    cases h1 : Term.typeCheck Γ t1 with
    | none => simp [bind, Option.bind]
    | some ty1 =>
      cases h2 : Term.typeCheck Γ t2 with
      | none => simp [bind, Option.bind]
      | some ty2 =>
        simp only [bind, Option.bind]
        intro h'
        split at h' <;> simp_all
  }

def Term.typeCheck_intCmp_inv {Γ : List TermVar} {op : Op.Num} {t1 t2 : Term}
    {rty : TermType} {τ : TermType}
    (h : Term.typeCheck Γ (.app (.num op) [t1, t2] rty) = some τ)
    (hop : op = .le ∨ op = .lt ∨ op = .ge ∨ op = .gt) :
    Term.typeCheck Γ t1 = some .int ∧ Term.typeCheck Γ t2 = some .int ∧ τ = .bool := by
  rcases hop with rfl | rfl | rfl | rfl <;> {
    simp only [Term.typeCheck] at h
    revert h
    cases h1 : Term.typeCheck Γ t1 with
    | none => simp [bind, Option.bind]
    | some ty1 =>
      cases h2 : Term.typeCheck Γ t2 with
      | none => simp [bind, Option.bind]
      | some ty2 =>
        simp only [bind, Option.bind]
        intro h'
        split at h' <;> simp_all
  }

def Term.typeCheck_quant_inv {Γ : List TermVar} {k : Strata.SMT.QuantifierKind}
    {vs : List TermVar} {body : Term} {τ : TermType}
    (h : Term.typeCheck Γ (.quant k vs [] body) = some τ) :
    Term.typeCheck (vs ++ Γ) body = some .bool ∧ τ = .bool := by
  simp only [Term.typeCheck] at h
  revert h
  cases hb : Term.typeCheck (vs ++ Γ) body with
  | none => simp [bind, Option.bind]
  | some tyb =>
    simp only [bind, Option.bind]
    intro h'
    split at h' <;> simp_all

def Term.typeCheck_distinct_inv {Γ : List TermVar} {ts : List Term} {rty : TermType} {τ : TermType}
    (h : Term.typeCheck Γ (.app (.core .distinct) ts rty) = some τ) :
    τ = .bool := by
  simp only [Term.typeCheck] at h
  revert h
  cases hts : Term.typeCheckAllSame Γ ts with
  | none => simp [bind, Option.bind]
  | some _ => simp [bind, Option.bind]; intro h'; exact h'.symm

/-! ## SMT term denotation -/

/-- Variable environment for SMT: maps each TermVar to a value of its type. -/
def SMTVarEnv (Γ : List TermVar) := ∀ v, v ∈ Γ → SMTTyDenote v.ty

def SMTVarEnv.empty : SMTVarEnv [] := fun _ h => nomatch h

def SMTVarEnv.cons {v : TermVar} (val : SMTTyDenote v.ty) (env : SMTVarEnv Γ) :
    SMTVarEnv (v :: Γ) :=
  fun w hmem =>
    if h : w = v then h ▸ val
    else env w (by cases hmem with | head => exact absurd rfl h | tail _ htl => exact htl)

/-- Total denotation of a type-checked SMT term. -/
noncomputable def SMTTerm.denote
    {Γ : List TermVar}
    (env : SMTVarEnv Γ)
    (tm : Term) (τ : TermType)
    (h : Term.typeCheck Γ tm = some τ)
    : SMTTyDenote τ :=
  match tm with
  | .prim p =>
    have heq := tc_prim_inv h
    heq ▸ (match p with
      | .bool b => (b : SMTTyDenote (TermPrim.bool b).typeOf)
      | .int i => (i : SMTTyDenote (TermPrim.int i).typeOf)
      | .string s => (s : SMTTyDenote (TermPrim.string s).typeOf)
      | .bitvec b => (b : SMTTyDenote (TermPrim.bitvec b).typeOf)
      | .real _ => ())
  | .var v =>
    let ⟨hmem, heq⟩ := tc_var_inv h
    cast (by rw [← heq]) (env v hmem)
  | .app (.core .not) [t] _ =>
    let ⟨ht, heq⟩ := tc_not_inv h
    cast (by rw [heq]) (!(denote env t .bool ht))
  | .app (.core .and) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_boolBin_inv h (.inl rfl)
    cast (by rw [heq]) ((denote env t1 .bool h1) && (denote env t2 .bool h2))
  | .app (.core .or) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_boolBin_inv h (.inr (.inl rfl))
    cast (by rw [heq]) ((denote env t1 .bool h1) || (denote env t2 .bool h2))
  | .app (.core .implies) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_boolBin_inv h (.inr (.inr rfl))
    cast (by rw [heq]) (!(denote env t1 .bool h1) || (denote env t2 .bool h2))
  | .app (.core .eq) [t1, t2] _ =>
    let ⟨τ', h1, h2, heq⟩ := Term.typeCheck_eq_inv h
    cast (by rw [heq]) (@decide (denote env t1 τ' h1 = denote env t2 τ' h2)
      (Classical.propDecidable _))
  | .app (.core .ite) [c, t, e] _ =>
    let ⟨hc, ht, he⟩ := Term.typeCheck_ite_inv h
    bif denote env c .bool hc then denote env t τ ht else denote env e τ he
  | .app (.num .neg) [t] _ =>
    let ⟨ht, heq⟩ := Term.typeCheck_intUn_inv h
    cast (by rw [heq]) (-(denote env t .int ht))
  | .app (.num .add) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intBin_inv h (.inl rfl)
    cast (by rw [heq]) ((denote env t1 .int h1) + (denote env t2 .int h2))
  | .app (.num .sub) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inl rfl))
    cast (by rw [heq]) ((denote env t1 .int h1) - (denote env t2 .int h2))
  | .app (.num .mul) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inr (.inl rfl)))
    cast (by rw [heq]) ((denote env t1 .int h1) * (denote env t2 .int h2))
  | .app (.num .div) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inr (.inr (.inl rfl))))
    cast (by rw [heq]) ((denote env t1 .int h1) / (denote env t2 .int h2))
  | .app (.num .mod) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inr (.inr (.inr rfl))))
    cast (by rw [heq]) ((denote env t1 .int h1) % (denote env t2 .int h2))
  | .app (.num .le) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intCmp_inv h (.inl rfl)
    cast (by rw [heq]) (decide ((denote env t1 .int h1) ≤ (denote env t2 .int h2)))
  | .app (.num .lt) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intCmp_inv h (.inr (.inl rfl))
    cast (by rw [heq]) (decide ((denote env t1 .int h1) < (denote env t2 .int h2)))
  | .app (.num .ge) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intCmp_inv h (.inr (.inr (.inl rfl)))
    cast (by rw [heq]) (decide ((denote env t1 .int h1) ≥ (denote env t2 .int h2)))
  | .app (.num .gt) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intCmp_inv h (.inr (.inr (.inr rfl)))
    cast (by rw [heq]) (decide ((denote env t1 .int h1) > (denote env t2 .int h2)))
  | .quant k vs [] body =>
    let ⟨hbody, heq⟩ := Term.typeCheck_quant_inv h
    let combinedEnv (ext : SMTVarEnv vs) : SMTVarEnv (vs ++ Γ) :=
      fun v hmem =>
        if hv : v ∈ vs then ext v hv
        else env v (by
          have := List.mem_append.mp hmem
          exact this.resolve_left hv)
    cast (by rw [heq]) (@decide
      (match k with
       | .all => ∀ (ext : SMTVarEnv vs), denote (combinedEnv ext) body .bool hbody = true
       | .exist => ∃ (ext : SMTVarEnv vs), denote (combinedEnv ext) body .bool hbody = true)
      (Classical.propDecidable _))
  | .app (.core .distinct) _ts _ =>
    have heq := Term.typeCheck_distinct_inv h
    cast (by rw [heq]) true
  | .none _ => False.elim (by simp only [Term.typeCheck] at h; exact absurd h nofun)
  | .some _ => False.elim (by simp only [Term.typeCheck] at h; exact absurd h nofun)

/-! ## Type translation -/

def monoTyToTermType : LMonoTy → Option TermType
  | .tcons "bool" [] => some .bool
  | .tcons "int" [] => some .int
  | .bitvec n => some (.bitvec n)
  | .tcons "string" [] => some .string
  | _ => none

/-! ## SMT translation: `LExpr` to `Term` -/

abbrev BoundVars := List TermVar


def corePredefinedOpToSMTOp (op : CoreOp) : Option ((List Term → TermType → Term) × TermType) :=
  match op with
  | .bool .And => some (.app Op.and, .bool)
  | .bool .Or => some (.app Op.or, .bool)
  | .bool .Not => some (.app Op.not, .bool)
  | .bool .Implies => some (.app Op.implies, .bool)
  | .bool .Equiv => some (.app Op.eq, .bool)
  | .numeric ⟨.int, .Add⟩ => some (.app Op.add, .int)
  | .numeric ⟨.int, .Sub⟩ => some (.app Op.sub, .int)
  | .numeric ⟨.int, .Mul⟩ => some (.app Op.mul, .int)
  | .numeric ⟨.int, .Div⟩ | .numeric ⟨.int, .SafeDiv⟩ => some (.app Op.div, .int)
  | .numeric ⟨.int, .Mod⟩ | .numeric ⟨.int, .SafeMod⟩ => some (.app Op.mod, .int)
  | .numeric ⟨.int, .Neg⟩ => some (.app Op.neg, .int)
  | .numeric ⟨.int, .Lt⟩ => some (.app Op.lt, .bool)
  | .numeric ⟨.int, .Le⟩ => some (.app Op.le, .bool)
  | .numeric ⟨.int, .Gt⟩ => some (.app Op.gt, .bool)
  | .numeric ⟨.int, .Ge⟩ => some (.app Op.ge, .bool)
  | _ => none

def toSMTTerm (bvs : BoundVars) : Expression.Expr → Except Format Term
  | .const () c =>
    match c with
    | .boolConst b => .ok (.prim (.bool b))
    | .intConst i => .ok (.prim (.int i))
    | .bitvecConst _ b => .ok (.prim (.bitvec b))
    | .strConst s => .ok (.prim (.string s))
    | .realConst _ => .error "Real constants unsupported"
  | .bvar () i =>
    if h : i < bvs.length then
      .ok (.var bvs[i])
    else .error f!"Bound variable index out of bounds: {i}"
  | .eq () e1 e2 => do
    let t1 ← toSMTTerm bvs e1
    let t2 ← toSMTTerm bvs e2
    .ok (Term.app (.core .eq) [t1, t2] .bool)
  | .ite () c t e => do
    let ct ← toSMTTerm bvs c
    let tt ← toSMTTerm bvs t
    let et ← toSMTTerm bvs e
    .ok (Term.app (.core .ite) [ct, tt, et] (Term.typeOf tt))
  | .app () (.op () fn (some _)) e1 =>
    match corePredefinedOpToSMTOp (CoreOp.ofString fn.name) with
    | some (builder, retTy) => do
      let t1 ← toSMTTerm bvs e1
      .ok (builder [t1] retTy)
    | none => .error f!"Unsupported op: {fn.name}"
  | .app () (.app () (.op () fn (some _)) e1) e2 =>
    match corePredefinedOpToSMTOp (CoreOp.ofString fn.name) with
    | some (builder, retTy) => do
      let t1 ← toSMTTerm bvs e1
      let t2 ← toSMTTerm bvs e2
      .ok (builder [t1, t2] retTy)
    | none => .error f!"Unsupported op: {fn.name}"
  | .op () fn (some _) =>
    match corePredefinedOpToSMTOp (CoreOp.ofString fn.name) with
    | some (builder, retTy) => .ok (builder [] retTy)
    | none => .error f!"Unsupported op: {fn.name}"
  | .quant () k _ (some qty) _ body => do
    let some smtTy := monoTyToTermType qty
      | .error f!"Cannot encode quantifier type: {repr qty}"
    let v : TermVar := ⟨s!"$__bv{bvs.length}", smtTy⟩
    let bvs' := v :: bvs
    let bodyTm ← toSMTTerm bvs' body
    let smtKind : Strata.SMT.QuantifierKind := match k with
      | .all => .all | .exist => .exist
    .ok (.quant smtKind [v] [] bodyTm)
  | e => .error f!"Unsupported expression: {repr e}"

/-! ## Sort-correctness: well-typed expressions produce well-sorted SMT terms -/

/-- Well-formedness: the bound variable list `bvs` correctly reflects the type context `Δ`.
    The `id_scheme` field captures that `toSMTTerm` names bound variables as `"$__bv{n-1-i}"`
    where `n = bvs.length`, ensuring freshness of newly added variables. -/
structure BVarCtxWF (Δ : List LMonoTy) (bvs : BoundVars) : Prop where
  len_eq : Δ.length = bvs.length
  ty_eq : ∀ i (hi : i < Δ.length), monoTyToTermType Δ[i] = some (bvs[i]'(by omega)).ty
  id_scheme : ∀ i (hi : i < bvs.length), (bvs[i]'hi).id = s!"$__bv{bvs.length - 1 - i}"

private theorem MonoTyIsBase_monoTyToTermType {τ : LMonoTy}
    (h : LExpr.MonoTyIsBase τ) : ∃ sty, monoTyToTermType τ = some sty := by
  cases h with
  | bool => exact ⟨.bool, rfl⟩
  | int => exact ⟨.int, rfl⟩
  | string => exact ⟨.string, rfl⟩
  | bitvec => exact ⟨_, rfl⟩

private theorem monoTyToTermType_bool :
    monoTyToTermType (.tcons "bool" []) = some .bool := rfl

private theorem monoTyToTermType_int :
    monoTyToTermType (.tcons "int" []) = some .int := rfl

private theorem monoTyToTermType_string :
    monoTyToTermType (.tcons "string" []) = some .string := rfl

private theorem monoTyToTermType_bitvec :
    monoTyToTermType (.bitvec n) = some (.bitvec n) := rfl

theorem toSMTTerm_typeChecks
    {Δ : List LMonoTy} {bvs : BoundVars}
    (hwf : BVarCtxWF Δ bvs)
    (e : Expression.Expr) (τ : LMonoTy) (smtTy : TermType)
    (he : LExpr.HasSimpType Δ e τ)
    (tm : Term) (h_ok : toSMTTerm bvs e = .ok tm)
    (hτ : monoTyToTermType τ = some smtTy)
    : Term.typeCheck bvs tm = some smtTy := by
  induction he generalizing bvs tm smtTy with
  | @const Δ' c hsimp =>
    cases c with
    | boolConst b =>
      simp [toSMTTerm, LConst.ty, monoTyToTermType, LMonoTy.bool] at h_ok hτ
      subst_vars; simp [Term.typeCheck, TermPrim.typeOf]
    | intConst i =>
      simp [toSMTTerm, LConst.ty, monoTyToTermType, LMonoTy.int] at h_ok hτ
      subst_vars; simp [Term.typeCheck, TermPrim.typeOf]
    | strConst s =>
      simp [toSMTTerm, LConst.ty, monoTyToTermType, LMonoTy.string] at h_ok hτ
      subst_vars; simp [Term.typeCheck, TermPrim.typeOf]
    | bitvecConst n b =>
      simp [toSMTTerm, LConst.ty, monoTyToTermType] at h_ok hτ
      subst_vars; simp [Term.typeCheck, TermPrim.typeOf]
    | realConst _ => simp [toSMTTerm] at h_ok
  | @bvar Δ' i τ' hlook hsimp =>
    simp [toSMTTerm] at h_ok
    split at h_ok
    · next hi =>
      simp at h_ok; subst h_ok
      simp only [Term.typeCheck]
      have hmem : bvs[i] ∈ bvs := List.getElem_mem hi
      simp [hmem]
      have hleni : i < Δ'.length := (List.getElem?_eq_some_iff.mp hlook).1
      have hwfty := hwf.ty_eq i hleni
      have hget : Δ'[i] = τ' := (List.getElem?_eq_some_iff.mp hlook).2
      rw [hget] at hwfty
      rw [hwfty] at hτ; simp at hτ; exact hτ
    · simp at h_ok
  | app1 hop _ ih_arg =>
    simp only [toSMTTerm] at h_ok
    generalize hcop : CoreOp.ofString _ = cop at hop h_ok
    cases hop with
    | intNeg =>
      simp [corePredefinedOpToSMTOp] at h_ok
      simp [monoTyToTermType] at hτ; subst hτ
      revert h_ok
      cases h_arg : toSMTTerm bvs _ with
      | error _ => simp [bind, Except.bind]
      | ok t_arg =>
        simp [bind, Except.bind]
        intro h_tm; subst h_tm
        simp only [Term.typeCheck]
        have ih := ih_arg hwf .int t_arg h_arg (by simp [monoTyToTermType])
        simp [ih, bind, Option.bind]
    | boolNot =>
      simp [corePredefinedOpToSMTOp] at h_ok
      simp [monoTyToTermType] at hτ; subst hτ
      revert h_ok
      cases h_arg : toSMTTerm bvs _ with
      | error _ => simp [bind, Except.bind]
      | ok t_arg =>
        simp [bind, Except.bind]
        intro h_tm; subst h_tm
        simp only [Term.typeCheck]
        have ih := ih_arg hwf .bool t_arg h_arg (by simp [monoTyToTermType])
        simp [ih, bind, Option.bind]
  | app2 hop _ _ ih_arg1 ih_arg2 =>
    simp only [toSMTTerm] at h_ok
    generalize hcop : CoreOp.ofString _ = cop at hop h_ok
    cases hop with
    | intDivT | intSafeDivT | intModT | intSafeModT =>
      simp only [corePredefinedOpToSMTOp] at h_ok; exact absurd h_ok nofun
    | intAdd | intSub | intMul | intDiv | intSafeDiv | intMod | intSafeMod
    | intLt | intLe | intGt | intGe
    | boolAnd | boolOr | boolImplies | boolEquiv =>
      simp only [corePredefinedOpToSMTOp, monoTyToTermType] at h_ok hτ
      simp only [Option.some.injEq] at hτ; subst hτ; revert h_ok
      cases h1 : toSMTTerm bvs _ with
      | error _ => simp [bind, Except.bind]
      | ok t1 =>
        cases h2 : toSMTTerm bvs _ with
        | error _ => simp [bind, Except.bind]
        | ok t2 =>
          simp [bind, Except.bind]
          intro h_tm; subst h_tm; simp only [Term.typeCheck]
          simp [ih_arg1 hwf _ _ h1 rfl, ih_arg2 hwf _ _ h2 rfl, bind, Option.bind]
  | ite _ _ _ ihc iht ihe =>
    simp only [toSMTTerm] at h_ok
    revert h_ok
    cases hc : toSMTTerm bvs _ with
    | error _ => simp [bind, Except.bind]
    | ok ct =>
      cases ht : toSMTTerm bvs _ with
      | error _ => simp [bind, Except.bind]
      | ok tt_tm =>
        cases he : toSMTTerm bvs _ with
        | error _ => simp [bind, Except.bind]
        | ok et =>
          simp [bind, Except.bind]
          intro h_tm; subst h_tm
          simp only [Term.typeCheck]
          have ih_c := ihc hwf .bool ct hc (by simp [monoTyToTermType])
          have ih_t := iht hwf smtTy tt_tm ht hτ
          have ih_e := ihe hwf smtTy et he hτ
          simp [ih_c, ih_t, ih_e, bind, Option.bind, beq_iff_eq]
  | eq hbase _ _ ih1 ih2 =>
    simp [monoTyToTermType] at hτ; subst hτ
    simp only [toSMTTerm, bind, Except.bind] at h_ok
    revert h_ok
    cases ha : toSMTTerm bvs _ with
    | error _ => simp
    | ok t1 =>
      cases hb : toSMTTerm bvs _ with
      | error _ => simp
      | ok t2 =>
        simp
        intro h_tm; subst h_tm
        simp only [Term.typeCheck]
        cases hbase with
        | bool =>
          have htc1 := ih1 hwf .bool t1 ha (by rfl)
          have htc2 := ih2 hwf .bool t2 hb (by rfl)
          rw [htc1, htc2]; simp [bind, Option.bind]
        | int =>
          have htc1 := ih1 hwf .int t1 ha (by rfl)
          have htc2 := ih2 hwf .int t2 hb (by rfl)
          rw [htc1, htc2]; simp [bind, Option.bind]
        | string =>
          have htc1 := ih1 hwf .string t1 ha (by rfl)
          have htc2 := ih2 hwf .string t2 hb (by rfl)
          rw [htc1, htc2]; simp [bind, Option.bind]
        | bitvec =>
          have htc1 := ih1 hwf _ t1 ha (by rfl)
          have htc2 := ih2 hwf _ t2 hb (by rfl)
          rw [htc1, htc2]; simp [bind, Option.bind]
  | quant hbase _ ih_body =>
    simp only [monoTyToTermType, Option.some.injEq] at hτ; subst hτ
    obtain ⟨smtQTy, hqty⟩ := MonoTyIsBase_monoTyToTermType hbase
    simp only [toSMTTerm] at h_ok
    rw [hqty] at h_ok; simp only at h_ok
    revert h_ok
    cases hbody : toSMTTerm (⟨s!"$__bv{bvs.length}", smtQTy⟩ :: bvs) _ with
    | error _ => simp [bind, Except.bind]
    | ok bodyTm =>
      simp [bind, Except.bind]
      intro h_tm; subst h_tm
      simp only [Term.typeCheck, List.singleton_append, bind, Option.bind]
      have hwf' : BVarCtxWF (_ :: _) (⟨s!"$__bv{bvs.length}", smtQTy⟩ :: bvs) :=
        ⟨congrArg (· + 1) hwf.len_eq, fun i hi => by
          cases i with
          | zero => exact hqty
          | succ j =>
            simp only [List.length, Nat.succ_lt_succ_iff] at hi
            simp only [List.getElem_cons_succ]
            exact hwf.ty_eq j hi,
         fun i hi => by
          cases i with
          | zero => simp [List.length]
          | succ j =>
            simp only [List.getElem_cons_succ, List.length] at hi ⊢
            have hj_lt : j < bvs.length := by omega
            have := hwf.id_scheme j hj_lt
            rw [this]; simp; congr 1; omega⟩
      have ih := ih_body hwf' _ bodyTm hbody rfl
      change Term.typeCheck (⟨s!"$__bv{bvs.length}", smtQTy⟩ :: bvs) bodyTm = some .bool at ih
      have hts : (toString "$__bv" : String) = "$__bv" := rfl
      have htn : toString (List.length bvs) = (List.length bvs).repr := rfl
      simp only [hts, htn] at *
      rw [ih]; simp

/-! ## Semantic soundness of `toSMTTerm` -/

/-- For base types with `monoTyToTermType τ = some smtTy`, the LExpr type denotation
    and the SMT type denotation are the same type. -/
theorem tyDenote_eq_smtTyDenote {τ : LMonoTy} {smtTy : TermType}
    (hbase : LExpr.MonoTyIsBase τ) (h : monoTyToTermType τ = some smtTy) :
    Lambda.TyDenote simpTcInterp simpTyVarVal τ = SMTTyDenote smtTy := by
  cases hbase with
  | bool => simp [monoTyToTermType] at h; subst h; rfl
  | int => simp [monoTyToTermType] at h; subst h; rfl
  | string => simp [monoTyToTermType] at h; subst h; rfl
  | bitvec => simp [monoTyToTermType] at h; subst h; rfl

/-- Correspondence between LExpr bound variable environment and SMT variable environment. -/
def EnvCorresponds
    {Δ : List LMonoTy} {bvs : BoundVars}
    (hwf : BVarCtxWF Δ bvs)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (smtEnv : SMTVarEnv bvs) : Prop :=
  ∀ i (τ : LMonoTy) (hbase : LExpr.MonoTyIsBase τ) (hlook : Δ[i]? = some τ),
    let hi : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
    let hbvs : i < bvs.length := hwf.len_eq ▸ hi
    let hty : monoTyToTermType τ = some (bvs[i]'hbvs).ty := by
      have := hwf.ty_eq i hi
      rw [(List.getElem?_eq_some_iff.mp hlook).2] at this
      exact this
    cast (tyDenote_eq_smtTyDenote hbase hty) (bvarVal.get i hlook)
      = smtEnv (bvs[i]'hbvs) (List.getElem_mem hbvs)

/-- Extension lemma for `EnvCorresponds`: extending both environments with corresponding
    values preserves the correspondence. The extended `SMTVarEnv` is passed directly and
    required to agree with the old one on old variables and to map the new variable to the
    new value. -/
theorem EnvCorresponds_cons
    {Δ : List LMonoTy} {bvs : BoundVars}
    {hwf : BVarCtxWF Δ bvs}
    {bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ}
    {smtEnv : SMTVarEnv bvs}
    (henv : EnvCorresponds hwf bvarVal smtEnv)
    {qty : LMonoTy} {v : TermVar}
    (hbase : LExpr.MonoTyIsBase qty)
    (hty : monoTyToTermType qty = some v.ty)
    (x : Lambda.TyDenote simpTcInterp simpTyVarVal qty)
    {smtEnv' : SMTVarEnv (v :: bvs)}
    (hnew : smtEnv' v (List.Mem.head _) = cast (tyDenote_eq_smtTyDenote hbase hty) x)
    (hold : ∀ w (hmem : w ∈ bvs), smtEnv' w (List.Mem.tail _ hmem) = smtEnv w hmem)
    (hwf' : BVarCtxWF (qty :: Δ) (v :: bvs))
    : EnvCorresponds hwf' (.cons x bvarVal) smtEnv' := by
  intro i τ hbase_i hlook
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook
    subst hlook
    simp only [HList.get_cons_zero]
    exact hnew.symm
  | succ j =>
    simp only [List.getElem?_cons_succ] at hlook
    simp only [HList.get_cons_succ]
    have henv_j := henv j τ hbase_i hlook
    have hj_lt : j < bvs.length := by
      have := hwf.len_eq; have := (List.getElem?_eq_some_iff.mp hlook).1; omega
    have hj1_lt : j + 1 < (v :: bvs).length := by simp; omega
    have hrhs : smtEnv' ((v :: bvs)[j + 1]'hj1_lt)
        (List.getElem_mem hj1_lt)
      = smtEnv (bvs[j]'hj_lt) (List.getElem_mem hj_lt) :=
      hold _ (List.getElem_mem hj_lt)
    rw [hrhs]
    exact henv_j

/-- Every result type of `HasSimpType` is a base type. -/
theorem HasSimpType_result_isBase {Δ : List LMonoTy} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Δ e τ) : LExpr.MonoTyIsBase τ := by
  induction he with
  | const hbase => exact hbase
  | bvar _ hbase => exact hbase
  | app1 hop _ _ =>
    generalize CoreOp.ofString _ = cop at hop
    cases hop with | intNeg => exact .int | boolNot => exact .bool
  | app2 hop _ _ _ _ =>
    generalize CoreOp.ofString _ = cop at hop
    cases hop <;> first | exact .int | exact .bool
  | ite _ _ _ _ iht _ => exact iht
  | eq _ _ _ _ _ => exact .bool
  | quant _ _ _ => exact .bool

private theorem subst_heq {α : Sort u} {P : α → Sort v} {a b : α}
    (h : a = b) (x : P b) : HEq (h ▸ x) x := by subst h; exact HEq.rfl

/-- SMTTerm.denote is invariant under change of type index when the types are provably equal.
    This lets us rewrite through the TermType argument. -/
private theorem SMTTerm_denote_cast {Γ : List TermVar} (env : SMTVarEnv Γ)
    (tm : Term) (τ τ' : TermType) (h : Term.typeCheck Γ tm = some τ) (h' : Term.typeCheck Γ tm = some τ')
    (heq : τ = τ') :
    HEq (SMTTerm.denote env tm τ h) (SMTTerm.denote env tm τ' h') := by
  subst heq; exact heq_of_eq (congrArg (SMTTerm.denote env tm τ) (proof_irrel h h'))

/-- SMTTerm.denote for a variable is HEq to the environment lookup. -/
private theorem SMTTerm_denote_var_heq {Γ : List TermVar} (env : SMTVarEnv Γ)
    (v : TermVar) (τ : TermType) (htc : Term.typeCheck Γ (.var v) = some τ) :
    HEq (SMTTerm.denote env (.var v) τ htc) (env v (tc_var_inv htc).1) := by
  unfold SMTTerm.denote
  -- After unfold, the goal involves `match tc_var_inv htc with | ⟨hmem, heq⟩ => cast ... (env v hmem)`
  -- We need to show this match result is HEq to `env v (tc_var_inv htc).1`
  -- Destructure tc_var_inv htc
  obtain ⟨hmem, heq⟩ := tc_var_inv htc
  simp only
  exact cast_heq _ _

/-- Cast distributes over Bool.cond (bif). -/
private theorem cast_bif {α β : Type} (h : α = β) (b : Bool) (x y : α) :
    cast h (bif b then x else y) = bif b then cast h x else cast h y := by
  subst h; rfl

/-- Cast distributes over if-then-else on Bool. -/
private theorem cast_ite_bool {α β : Type} (h : α = β) (b : Bool) (x y : α) :
    cast h (if b = true then x else y) = if b = true then cast h x else cast h y := by
  subst h; rfl

/-- The choose from MonoTyIsBase_monoTyToTermType applied to HasSimpType_result_isBase
    gives back the same smtTy as monoTyToTermType. -/
private theorem choose_eq_of_hτ {τ : LMonoTy} {smtTy : TermType}
    (hbase : LExpr.MonoTyIsBase τ) (hτ : monoTyToTermType τ = some smtTy) :
    (MonoTyIsBase_monoTyToTermType hbase).choose = smtTy := by
  have h := (MonoTyIsBase_monoTyToTermType hbase).choose_spec
  rw [h] at hτ; exact Option.some.inj hτ

/-- Helper: if cast-wrapped bif on one side equals bif on the other side,
    given the conditions and branches correspond via HEq. -/
private theorem bif_heq_of_cond_branches {α β : Type} {b1 : Bool} {b2 : Bool}
    {t1 e1 : α} {t2 e2 : β} (h_ty : α = β)
    (hb : b1 = b2) (ht : HEq t1 t2) (he : HEq e1 e2) :
    cast h_ty (bif b1 then t1 else e1) = (bif b2 then t2 else e2) := by
  subst h_ty; subst hb; cases ht; cases he; cases b1 <;> rfl

/-- Congruence for bif with HEq branches (same result type). -/
private theorem bif_eq_of_heq {α : Type} {b1 b2 : Bool} {t1 e1 t2 e2 : α}
    (hb : b1 = b2) (ht : t1 = t2) (he : e1 = e2) :
    (bif b1 then t1 else e1) = (bif b2 then t2 else e2) := by
  subst hb; subst ht; subst he; rfl

/-- Convert an IH with opaque `choose` smtTy to one with explicit `smtTy`,
    given a proof that `choose` equals `smtTy`. -/
private theorem ih_convert_smtTy {Γ : List TermVar} {env : SMTVarEnv Γ}
    {tm : Term} {smtTy1 smtTy2 : TermType}
    (h_eq : smtTy1 = smtTy2)
    {x : SMTTyDenote smtTy1} {htc1 : Term.typeCheck Γ tm = some smtTy1}
    (ih : x = SMTTerm.denote env tm smtTy1 htc1)
    : HEq x (SMTTerm.denote env tm smtTy2 (h_eq ▸ htc1)) := by
  subst h_eq; exact heq_of_eq ih

/-- Unfolding lemma for SMTTerm.denote on ite. -/
private noncomputable def SMTTerm_denote_ite {Γ : List TermVar} (env : SMTVarEnv Γ)
    (c t e : Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck Γ (.app (.core .ite) [c, t, e] rty) = some τ) :
    SMTTerm.denote env (.app (.core .ite) [c, t, e] rty) τ htc =
      bif SMTTerm.denote env c .bool (Term.typeCheck_ite_inv htc).1
      then SMTTerm.denote env t τ (Term.typeCheck_ite_inv htc).2.1
      else SMTTerm.denote env e τ (Term.typeCheck_ite_inv htc).2.2 := by
  simp only [SMTTerm.denote]
  obtain ⟨hc, ht, he⟩ := Term.typeCheck_ite_inv htc
  rfl

/-- Unfolding lemma for SMTTerm.denote on eq. -/
private noncomputable def SMTTerm_denote_eq_unfold {Γ : List TermVar} (env : SMTVarEnv Γ)
    (t1 t2 : Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck Γ (.app (.core .eq) [t1, t2] rty) = some τ) :
    SMTTerm.denote env (.app (.core .eq) [t1, t2] rty) τ htc =
      cast (by rw [(Term.typeCheck_eq_inv htc).2.2.2]) (@decide
        (SMTTerm.denote env t1 (Term.typeCheck_eq_inv htc).1 (Term.typeCheck_eq_inv htc).2.1
         = SMTTerm.denote env t2 (Term.typeCheck_eq_inv htc).1 (Term.typeCheck_eq_inv htc).2.2.1)
        (Classical.propDecidable _)) := by
  simp only [SMTTerm.denote]
  obtain ⟨τ', h1, h2, heq⟩ := Term.typeCheck_eq_inv htc
  rfl

private theorem digitChar_toNat (h : n < 10) : (Nat.digitChar n).toNat = n + 48 := by
  revert h; revert n; native_decide

private theorem digitChar_inj (ha : a < 10) (hb : b < 10)
    (h : Nat.digitChar a = Nat.digitChar b) : a = b := by
  have hav := digitChar_toNat ha
  have hbv := digitChar_toNat hb
  have := congrArg Char.toNat h
  omega

private theorem nat_toDigits_10_inj :
    ∀ a b : Nat, Nat.toDigits 10 a = Nat.toDigits 10 b → a = b := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b heq
    by_cases ha : a < 10
    · by_cases hb : b < 10
      · rw [Nat.toDigits_of_lt_base ha, Nat.toDigits_of_lt_base hb] at heq
        exact digitChar_inj ha hb (List.cons.inj heq).1
      · exfalso
        have hb' : 10 ≤ b := by omega
        rw [Nat.toDigits_of_lt_base ha, Nat.toDigits_of_base_le (by omega) hb'] at heq
        have hlen := congrArg List.length heq
        simp only [List.length_append, List.length] at hlen
        have := Nat.length_toDigits_pos (b := 10) (n := b / 10)
        omega
    · by_cases hb : b < 10
      · exfalso
        have ha' : 10 ≤ a := by omega
        rw [Nat.toDigits_of_base_le (by omega) ha', Nat.toDigits_of_lt_base hb] at heq
        have hlen := congrArg List.length heq
        simp only [List.length_append, List.length] at hlen
        have := Nat.length_toDigits_pos (b := 10) (n := a / 10)
        omega
      · have ha' : 10 ≤ a := by omega
        have hb' : 10 ≤ b := by omega
        rw [Nat.toDigits_of_base_le (by omega) ha',
            Nat.toDigits_of_base_le (by omega) hb'] at heq
        have hlen_eq :
            (Nat.toDigits 10 (a / 10)).length = (Nat.toDigits 10 (b / 10)).length := by
          have := congrArg List.length heq
          simp only [List.length_append, List.length] at this
          omega
        have hpref := List.append_inj_left heq hlen_eq
        have hsuf := List.append_inj_right heq hlen_eq
        have hmod : a % 10 = b % 10 :=
          digitChar_inj (Nat.mod_lt a (by omega)) (Nat.mod_lt b (by omega))
            (List.cons.inj hsuf).1
        have hdiv := ih (a / 10) (Nat.div_lt_self (by omega) (by omega)) (b / 10) hpref
        omega

/-- Helper for the quant case of toSMTTerm_sound: given that body denotations correspond
    for all witnesses and corresponding environments, the full quant denotations correspond. -/
private theorem toSMTTerm_sound_quant
    {Δ : List LMonoTy} {bvs : BoundVars}
    (hwf : BVarCtxWF Δ bvs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (smtEnv : SMTVarEnv bvs)
    (henv : EnvCorresponds hwf bvarVal smtEnv)
    (qty : LMonoTy) (k : Lambda.QuantifierKind) (name : String)
    (body : Expression.Expr)
    (hbase : LExpr.MonoTyIsBase qty)
    (he_body : LExpr.HasSimpType (qty :: Δ) body (.tcons "bool" []))
    (smtQTy : TermType) (hqty : monoTyToTermType qty = some smtQTy)
    (bodyTm : Term)
    (v : TermVar) (hv : v = ⟨s!"$__bv{bvs.length}", smtQTy⟩)
    (hwf' : BVarCtxWF (qty :: Δ) (v :: bvs))
    (hbody_tc : Term.typeCheck (v :: bvs) bodyTm = some .bool)
    (body_eq : ∀ x : Lambda.TyDenote simpTcInterp simpTyVarVal qty,
        ∀ (smtEnv' : SMTVarEnv (v :: bvs)),
        EnvCorresponds hwf' (.cons x bvarVal) smtEnv' →
        (LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal
          (.cons x bvarVal) body (.tcons "bool" [])
          (HasSimpType_implies_HasTypeA he_body) : Bool) =
        SMTTerm.denote smtEnv' bodyTm .bool hbody_tc)
    (h_ok : toSMTTerm bvs (.quant () k name (some qty) (.const () (.boolConst true)) body) =
      .ok (.quant (match k with | .all => .all | .exist => .exist)
        [v] [] bodyTm))
    : let he := LExpr.HasSimpType.quant hbase he_body
      let smtTy := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase he)).choose
      let hτ := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase he)).choose_spec
      let htc := toSMTTerm_typeChecks hwf _ _ smtTy he _ h_ok hτ
      cast (tyDenote_eq_smtTyDenote (HasSimpType_result_isBase he) hτ)
        (simpDenote opInterp bvarVal
          (.quant () k name (some qty) (.const () (.boolConst true)) body)
          (.tcons "bool" []) (HasSimpType_implies_HasTypeA he))
      = SMTTerm.denote smtEnv
          (.quant (match k with | .all => .all | .exist => .exist)
            [v] [] bodyTm) smtTy htc := by
  subst hv
  cases k <;> {
    intro he smtTy hτ htc
    simp only [simpDenote]
    -- Both sides are Bool (definitionally).
    -- Strip outer cast via HEq, unfold denotations
    apply eq_of_heq
    apply HEq.trans (cast_heq _ _)
    unfold LExpr.denote SMTTerm.denote
    -- Use dsimp to reduce the match expressions (k is concrete after cases)
    dsimp only []
    -- Both sides are HEq. LHS type: TyDenote (.tcons "bool" []) = Bool.
    -- RHS type: SMTTyDenote smtTy (also = Bool definitionally).
    -- The match destructuring on proof terms (PSigma/And) reduces definitionally.
    -- The cast on RHS is Bool = Bool (identity).
    -- Strategy: both sides are definitionally equal to decide(P) and decide(Q)
    -- where P ↔ Q. Prove by constructing the equivalence.
    -- Step 1: Show both sides are HEq to explicit decide expressions
    -- by pattern-matching on the proof terms ourselves.
    obtain ⟨_, _, _, h_body_inv⟩ := HasTypeA.quant_inv (HasSimpType_implies_HasTypeA he)
    obtain ⟨hbody_inv, heq_inv⟩ := Term.typeCheck_quant_inv htc
    -- After obtaining, the matches in the goal should reduce
    dsimp only []
    -- Now should be: decide(P) ≍ cast heq_inv (decide(Q))
    -- Strip the cast via HEq
    apply HEq.trans _ (cast_heq _ _).symm
    -- Both sides now at type Bool
    apply heq_of_eq
    -- decide(P) = decide(Q) where P and Q are the quantified propositions
    -- connected via body_eq
    congr 1
    apply propext
    -- Goal: (∀/∃ x, LExpr.denote ... body .bool h_body_inv = true) ↔
    --       (∀/∃ ext, SMTTerm.denote (combinedEnv ext) bodyTm .bool hbody_inv = true)
    -- Use body_eq with proof_irrel to bridge proof witnesses
    let v : TermVar := ⟨s!"$__bv{bvs.length}", smtQTy⟩
    -- Proof irrelevance: the typing proofs in the goal match those in body_eq
    have h_pi1 : h_body_inv = HasSimpType_implies_HasTypeA he_body := proof_irrel _ _
    have h_pi2 : hbody_inv = hbody_tc := proof_irrel _ _
    subst h_pi1; subst h_pi2
    -- Bridge: for any x and corresponding ext, body denotations match
    let v : TermVar := ⟨s!"$__bv{bvs.length}", smtQTy⟩
    have nat_toString_inj : ∀ a b : Nat, toString a = toString b → a = b := by
      intro a b h
      have h1 : ("$__bv" ++ toString a).toList = ("$__bv" ++ toString b).toList := by
        simp [String.toList_append]; exact congrArg String.toList h
      rw [String.toList_append, String.toList_append] at h1
      have h2 := List.append_cancel_left h1
      -- h2 : (toString a).toList = (toString b).toList
      have hstr : toString a = toString b := String.ext_iff.mpr h2
      have hdigits : Nat.toDigits 10 a = Nat.toDigits 10 b :=
        String.ofList_injective (by rw [← Nat.toString_eq_ofList_toDigits,
          ← Nat.toString_eq_ofList_toDigits]; exact hstr)
      exact nat_toDigits_10_inj a b hdigits
    have bv_str_inj : ∀ a b : Nat, s!"$__bv{a}" = s!"$__bv{b}" → a = b := by
      intro a b h
      have h1 : ("$__bv" ++ toString a).toList = ("$__bv" ++ toString b).toList :=
        congrArg String.toList h
      rw [String.toList_append, String.toList_append] at h1
      exact nat_toString_inj a b (String.ext_iff.mpr (List.append_cancel_left h1))
    have hv_notin : v ∉ bvs := by
      intro hmem
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
      have hid := hwf.id_scheme i hi
      have hveq : (bvs[i]'hi).id = v.id := congrArg TermVar.id hget
      rw [hid] at hveq
      have := bv_str_inj _ _ hveq
      omega
    have h_ty_eq := tyDenote_eq_smtTyDenote hbase hqty
    -- Helper: given x, build the combined SMTVarEnv and show body correspondence
    have bridge : ∀ (x : Lambda.TyDenote simpTcInterp simpTyVarVal qty)
        (ext : SMTVarEnv [v])
        (hxy : ext v (List.Mem.head _) = cast h_ty_eq x),
        (LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal
          (.cons x bvarVal) body (.tcons "bool" [])
          (HasSimpType_implies_HasTypeA he_body) : Bool) = true ↔
        SMTTerm.denote (fun w hmem => if hv : w ∈ [v] then ext w hv
          else smtEnv w (by have := List.mem_append.mp hmem; exact this.resolve_left hv))
          bodyTm .bool hbody_inv = true := by
      intro x ext hxy
      let smtEnv' : SMTVarEnv (v :: bvs) := fun w hmem =>
        if hv : w ∈ [v] then ext w hv
        else smtEnv w (by cases hmem; exact absurd (List.Mem.head _) hv; assumption)
      have hcorr : EnvCorresponds hwf' (.cons x bvarVal) smtEnv' :=
        EnvCorresponds_cons henv hbase hqty x
          (show smtEnv' v (List.Mem.head _) = cast h_ty_eq x by
            simp only [smtEnv', show (v ∈ [v]) = True from by simp, dite_true]
            exact hxy)
          (show ∀ w (hmem : w ∈ bvs), smtEnv' w (List.Mem.tail _ hmem) = smtEnv w hmem by
            intro w hmem; simp only [smtEnv']
            have : ¬(w ∈ [v]) := by
              simp []
              intro heq; exact absurd (heq ▸ hmem) hv_notin
            simp [this])
          hwf'
      have hbody := body_eq x smtEnv' hcorr
      constructor
      · intro hlhs
        change SMTTerm.denote smtEnv' bodyTm .bool hbody_inv = true
        rw [← hbody]; exact hlhs
      · intro hrhs
        rw [hbody]; exact hrhs
    -- Now use bridge to close the Iff for ∀/∃
    constructor
    · -- Forward: from LExpr quantifier to SMT quantifier
      first
      | (-- ∀ case
        intro hx ext
        let y := ext v (List.Mem.head _)
        let x : Lambda.TyDenote simpTcInterp simpTyVarVal qty := cast h_ty_eq.symm y
        exact (bridge x ext (by simp [x, y, cast_cast])).mp (hx x))
      | (-- ∃ case
        intro ⟨x, hx⟩
        let y : SMTTyDenote smtQTy := cast h_ty_eq x
        let ext : SMTVarEnv [v] := fun w hmem =>
          cast (by have := List.eq_of_mem_singleton hmem; subst this; rfl) y
        exact ⟨ext, (bridge x ext (by simp [ext, y])).mp hx⟩)
    · -- Backward: from SMT quantifier to LExpr quantifier
      first
      | (-- ∀ case
        intro hext x
        let y : SMTTyDenote smtQTy := cast h_ty_eq x
        let ext : SMTVarEnv [v] := fun w hmem =>
          cast (by have := List.eq_of_mem_singleton hmem; subst this; rfl) y
        exact (bridge x ext (by simp [ext, y])).mpr (hext ext))
      | (-- ∃ case
        intro ⟨ext, hext⟩
        let y := ext v (List.Mem.head _)
        let x : Lambda.TyDenote simpTcInterp simpTyVarVal qty := cast h_ty_eq.symm y
        exact ⟨x, (bridge x ext (by simp [x, y, cast_cast])).mpr hext⟩)
  }

/-- Helper for the app1 case of `toSMTTerm_sound`, with `smtTy` as an explicit parameter. -/
private theorem toSMTTerm_sound_app1
    {Δ : List LMonoTy} {bvs : BoundVars}
    (hwf : BVarCtxWF Δ bvs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (hop : OpInterpConsistent opInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (smtEnv : SMTVarEnv bvs)
    (henv : EnvCorresponds hwf bvarVal smtEnv)
    {o : CoreLParams.Identifier} {arg : Expression.Expr} {aty rty : LMonoTy}
    (hop_ty : LExpr.OpIsSimp1 (CoreOp.ofString o.name) aty rty)
    (h_arg_ty : LExpr.HasSimpType Δ arg aty)
    (ih_arg : ∀ {bvs : BoundVars} (hwf : BVarCtxWF Δ bvs)
      (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
      (smtEnv : SMTVarEnv bvs),
      EnvCorresponds hwf bvarVal smtEnv →
      ∀ (tm : Term) (h_ok : toSMTTerm bvs arg = .ok tm),
        let smtTy := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg_ty)).choose
        let hτ := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg_ty)).choose_spec
        let htc := toSMTTerm_typeChecks hwf arg aty smtTy h_arg_ty tm h_ok hτ
        cast (tyDenote_eq_smtTyDenote (HasSimpType_result_isBase h_arg_ty) hτ)
          (simpDenote opInterp bvarVal arg aty (HasSimpType_implies_HasTypeA h_arg_ty))
        = SMTTerm.denote smtEnv tm smtTy htc)
    (tm : Term)
    (h_ok : toSMTTerm bvs (.app () (.op () o (some (.tcons "arrow" [aty, rty]))) arg) = .ok tm)
    -- Explicit smtTy and proofs (not computed from hop_ty)
    (hbase_rty : LExpr.MonoTyIsBase rty)
    (smtTy : TermType)
    (hτ : monoTyToTermType rty = some smtTy)
    (htc : Term.typeCheck bvs tm = some smtTy)
    -- Abstract typing proof for the expression (proof-irrelevant)
    (h_typing : LExpr.HasTypeA Δ (.app () (.op () o (some (.tcons "arrow" [aty, rty]))) arg) rty)
    : cast (tyDenote_eq_smtTyDenote hbase_rty hτ)
        (simpDenote opInterp bvarVal _ rty h_typing)
      = SMTTerm.denote smtEnv tm smtTy htc := by
  -- Now we can freely generalize and cases on hop_ty since h_typing is abstract
  simp only [toSMTTerm] at h_ok
  revert h_ok htc
  generalize hcop : CoreOp.ofString o.name = cop at hop_ty ⊢
  intro h_ok htc
  cases hop_ty with
  | intNeg =>
    simp [corePredefinedOpToSMTOp] at h_ok
    revert h_ok
    cases h_arg_ok : toSMTTerm bvs arg with
    | error _ => simp [bind, Except.bind]
    | ok t_arg =>
      simp [bind, Except.bind]
      intro h_tm; subst h_tm
      have hchoose_arg : (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg_ty)).choose = .int :=
        choose_eq_of_hτ (HasSimpType_result_isBase h_arg_ty) rfl
      specialize ih_arg hwf bvarVal smtEnv henv t_arg h_arg_ok
      simp only at ih_arg
      have hop_neg := hop.neg o.name hcop
      -- LHS: cast tyEq (simpDenote opInterp bvarVal (.app (.op o arrowTy) arg) rty h_typing)
      -- simpDenote = LExpr.denote. For .app (.op o ty) arg, denote gives:
      --   (opInterp o.name (ty.substTyVars vt)) applied to (denote arg aty h_arg)
      -- Use denote_app and denote_op to rewrite
      simp only [simpDenote]
      have h_app := HasTypeA.app_inv h_typing
      rw [Lambda.denote_app bvarVal h_app.2.1 h_app.2.2 h_typing]
      rw [Lambda.denote_op simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal h_app.2.1]
      -- Goal: cast tyEq ((op_inv ▸ opInterp ...) (denote arg h_app.fst ...))
      --       = SMTTerm.denote smtEnv (.app Op.neg [t_arg] .int) smtTy htc
      -- Strategy: obtain h_app fields, use set/generalize to make h_app.fst a variable,
      -- then subst via op_inv to make everything concrete.
      obtain ⟨aty, h_fn_ty, h_arg_ty'⟩ := h_app
      simp only at *
      -- h_fn_ty : HasTypeA Δ (.op () o (some arrowTy)) (.arrow aty (.tcons "int" []))
      -- op_inv h_fn_ty : .arrow aty (.tcons "int" []) = .tcons "arrow" [.tcons "int" [], .tcons "int" []]
      have h_opi := HasTypeA.op_inv h_fn_ty
      -- Since .arrow aty rty = .tcons "arrow" [aty, rty], this gives aty = .tcons "int" []
      simp only [LMonoTy.arrow] at h_opi
      have h_aty : aty = .tcons "int" [] := (LMonoTy.tcons.inj h_opi).2 |> List.cons.inj |>.1
      subst h_aty
      -- Now op_inv h_fn_ty : .tcons "arrow" [.tcons "int" [], .tcons "int" []] = .tcons "arrow" [...]
      -- which is rfl, so ▸ is identity
      have h_opi_rfl : HasTypeA.op_inv h_fn_ty = rfl := rfl
      rw [h_opi_rfl]
      -- Now: cast tyEq (opInterp o.name (substTyVars simpTyVarVal arrowTy) (denote arg .int h_arg_ty'))
      --      = SMTTerm.denote smtEnv (.app Op.neg [t_arg] .int) smtTy htc
      simp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map] at hop_neg ⊢
      rw [hop_neg]
      -- LHS: cast tyEq ((fun x => -x) (denote arg .int h_arg_ty'))
      -- RHS: SMTTerm.denote smtEnv (.app Op.neg [t_arg] .int) smtTy htc
      -- Obtain smtTy = .int from htc
      have h_intUn := Term.typeCheck_intUn_inv htc
      have h_smtTy_eq : smtTy = .int := h_intUn.2
      subst h_smtTy_eq
      -- Both sides are Int. Use eq_of_heq + cast_heq to strip the cast on LHS.
      apply eq_of_heq
      refine HEq.trans (cast_heq _ _) ?_
      -- LHS: (fun x => -x) (denote arg .int h_arg_ty') ≍ SMTTerm.denote smtEnv (.app Op.neg [t_arg] .int) .int htc
      -- SMTTerm.denote for .app Op.neg [t_arg] .int is HEq to -(SMTTerm.denote t_arg .int ...)
      -- by definition (it produces cast heq (-(denote t_arg .int ht)))
      -- SMTTerm.denote for neg: use the same pattern as SMTTerm_denote_ite
      have h_rhs_eq : SMTTerm.denote smtEnv (.app Op.neg [t_arg] .int) .int htc =
          cast (by rw [(Term.typeCheck_intUn_inv htc).2])
            (-(SMTTerm.denote smtEnv t_arg .int (Term.typeCheck_intUn_inv htc).1)) := by
        simp only [SMTTerm.denote]
        obtain ⟨ht, heq⟩ := Term.typeCheck_intUn_inv htc
        rfl
      have h_rhs_heq : HEq (SMTTerm.denote smtEnv (.app Op.neg [t_arg] .int) .int htc)
          (-(SMTTerm.denote smtEnv t_arg .int (Term.typeCheck_intUn_inv htc).1)) := by
        rw [h_rhs_eq]; exact cast_heq _ _
      refine HEq.trans ?_ h_rhs_heq.symm
      -- LHS: (fun x => -x) (denote arg .int h_arg_ty') ≍ -(SMTTerm.denote t_arg .int h_intUn.1)
      -- Both sides are: negate applied to an Int value
      -- ih_arg connects denote arg to SMTTerm.denote t_arg
      simp only [simpDenote] at ih_arg
      have h_arg_heq : HEq (LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal arg
          (.tcons "int" []) h_arg_ty') (SMTTerm.denote smtEnv t_arg .int h_intUn.1) :=
        (cast_heq _ _).symm.trans (ih_convert_smtTy hchoose_arg ih_arg)
      exact congrArg (fun x : Int => -x) (eq_of_heq h_arg_heq) |> heq_of_eq
  | boolNot =>
    simp [corePredefinedOpToSMTOp] at h_ok
    revert h_ok
    cases h_arg_ok : toSMTTerm bvs arg with
    | error _ => simp [bind, Except.bind]
    | ok t_arg =>
      simp [bind, Except.bind]
      intro h_tm; subst h_tm
      have hchoose_arg : (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg_ty)).choose = .bool :=
        choose_eq_of_hτ (HasSimpType_result_isBase h_arg_ty) rfl
      specialize ih_arg hwf bvarVal smtEnv henv t_arg h_arg_ok
      simp only at ih_arg
      have hop_not := hop.not o.name hcop
      simp only [simpDenote]
      have h_app := HasTypeA.app_inv h_typing
      rw [Lambda.denote_app bvarVal h_app.2.1 h_app.2.2 h_typing]
      rw [Lambda.denote_op simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal h_app.2.1]
      -- Same pattern as intNeg: obtain aty from app_inv, subst via op_inv, rewrite with hop_not
      obtain ⟨aty, h_fn_ty, h_arg_ty'⟩ := h_app
      simp only at *
      have h_opi := HasTypeA.op_inv h_fn_ty
      simp only [LMonoTy.arrow] at h_opi
      have h_aty : aty = .tcons "bool" [] := (LMonoTy.tcons.inj h_opi).2 |> List.cons.inj |>.1
      subst h_aty
      have h_opi_rfl : HasTypeA.op_inv h_fn_ty = rfl := rfl
      rw [h_opi_rfl]
      simp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map] at hop_not ⊢
      rw [hop_not]
      -- LHS: cast tyEq ((fun x => !x) (denote arg .bool h_arg_ty'))
      -- RHS: SMTTerm.denote smtEnv (.app (.core .not) [t_arg] .bool) smtTy htc
      have h_not_inv := tc_not_inv htc
      have h_smtTy_eq : smtTy = .bool := h_not_inv.2
      subst h_smtTy_eq
      -- Unfold SMTTerm.denote for not
      have h_rhs_eq : SMTTerm.denote smtEnv (.app (.core .not) [t_arg] .bool) .bool htc =
          cast (by rw [(tc_not_inv htc).2])
            (!(SMTTerm.denote smtEnv t_arg .bool (tc_not_inv htc).1)) := by
        simp only [SMTTerm.denote]
        obtain ⟨ht, heq⟩ := tc_not_inv htc
        rfl
      have h_rhs_heq : HEq (SMTTerm.denote smtEnv (.app (.core .not) [t_arg] .bool) .bool htc)
          (!(SMTTerm.denote smtEnv t_arg .bool (tc_not_inv htc).1)) := by
        rw [h_rhs_eq]; exact cast_heq _ _
      apply eq_of_heq
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans ?_ h_rhs_heq.symm
      simp only [simpDenote] at ih_arg
      have h_arg_heq : HEq (LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal arg
          (.tcons "bool" []) h_arg_ty') (SMTTerm.denote smtEnv t_arg .bool (tc_not_inv htc).1) :=
        (cast_heq _ _).symm.trans (ih_convert_smtTy hchoose_arg ih_arg)
      exact congrArg (fun x : Bool => !x) (eq_of_heq h_arg_heq) |> heq_of_eq

/-- Helper for the app2 case of toSMTTerm_sound. -/
private theorem toSMTTerm_sound_app2
    {Δ : List LMonoTy} {bvs : BoundVars}
    (hwf : BVarCtxWF Δ bvs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (hop : OpInterpConsistent opInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (smtEnv : SMTVarEnv bvs)
    (henv : EnvCorresponds hwf bvarVal smtEnv)
    {o : CoreLParams.Identifier} {arg1 arg2 : Expression.Expr} {aty1 aty2 rty : LMonoTy}
    (hop_ty : LExpr.OpIsSimp2 (CoreOp.ofString o.name) aty1 aty2 rty)
    (h_arg1_ty : LExpr.HasSimpType Δ arg1 aty1)
    (h_arg2_ty : LExpr.HasSimpType Δ arg2 aty2)
    (ih_arg1 : ∀ {bvs : BoundVars} (hwf : BVarCtxWF Δ bvs)
      (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
      (smtEnv : SMTVarEnv bvs),
      EnvCorresponds hwf bvarVal smtEnv →
      ∀ (tm : Term) (h_ok : toSMTTerm bvs arg1 = .ok tm),
        let smtTy := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg1_ty)).choose
        let hτ := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg1_ty)).choose_spec
        let htc := toSMTTerm_typeChecks hwf arg1 aty1 smtTy h_arg1_ty tm h_ok hτ
        cast (tyDenote_eq_smtTyDenote (HasSimpType_result_isBase h_arg1_ty) hτ)
          (simpDenote opInterp bvarVal arg1 aty1 (HasSimpType_implies_HasTypeA h_arg1_ty))
        = SMTTerm.denote smtEnv tm smtTy htc)
    (ih_arg2 : ∀ {bvs : BoundVars} (hwf : BVarCtxWF Δ bvs)
      (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
      (smtEnv : SMTVarEnv bvs),
      EnvCorresponds hwf bvarVal smtEnv →
      ∀ (tm : Term) (h_ok : toSMTTerm bvs arg2 = .ok tm),
        let smtTy := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg2_ty)).choose
        let hτ := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg2_ty)).choose_spec
        let htc := toSMTTerm_typeChecks hwf arg2 aty2 smtTy h_arg2_ty tm h_ok hτ
        cast (tyDenote_eq_smtTyDenote (HasSimpType_result_isBase h_arg2_ty) hτ)
          (simpDenote opInterp bvarVal arg2 aty2 (HasSimpType_implies_HasTypeA h_arg2_ty))
        = SMTTerm.denote smtEnv tm smtTy htc)
    (tm : Term)
    (h_ok : toSMTTerm bvs (.app () (.app () (.op () o (some (.tcons "arrow" [aty1, .tcons "arrow" [aty2, rty]]))) arg1) arg2) = .ok tm)
    -- Explicit smtTy and proofs (not computed from hop_ty)
    (hbase_rty : LExpr.MonoTyIsBase rty)
    (smtTy : TermType)
    (hτ : monoTyToTermType rty = some smtTy)
    (htc : Term.typeCheck bvs tm = some smtTy)
    (h_typing : LExpr.HasTypeA Δ (.app () (.app () (.op () o (some (.tcons "arrow" [aty1, .tcons "arrow" [aty2, rty]]))) arg1) arg2) rty)
    : cast (tyDenote_eq_smtTyDenote hbase_rty hτ)
        (simpDenote opInterp bvarVal _ rty h_typing)
      = SMTTerm.denote smtEnv tm smtTy htc := by
  simp only [toSMTTerm] at h_ok
  revert h_ok htc
  generalize hcop : CoreOp.ofString o.name = cop at hop_ty
  intro h_ok htc
  cases hop_ty with
  | intDivT | intSafeDivT | intModT | intSafeModT =>
    simp [corePredefinedOpToSMTOp] at h_ok
  | intAdd | intSub | intMul | intDiv | intSafeDiv | intMod | intSafeMod
  | intLt | intLe | intGt | intGe
  | boolAnd | boolOr | boolImplies | boolEquiv =>
    simp [corePredefinedOpToSMTOp] at h_ok
    revert h_ok
    cases h1_ok : toSMTTerm bvs arg1 with
    | error _ => simp [bind, Except.bind]
    | ok t1 =>
      cases h2_ok : toSMTTerm bvs arg2 with
      | error _ => simp [bind, Except.bind]
      | ok t2 =>
        simp [bind, Except.bind]
        intro h_tm; subst h_tm
        specialize ih_arg1 hwf bvarVal smtEnv henv t1 h1_ok
        specialize ih_arg2 hwf bvarVal smtEnv henv t2 h2_ok
        simp only at ih_arg1 ih_arg2
        simp only [simpDenote]
        apply eq_of_heq
        refine HEq.trans (cast_heq _ _) ?_
        -- Unfold the double application using denote_app
        have h_app_outer := HasTypeA.app_inv h_typing
        rw [Lambda.denote_app bvarVal h_app_outer.2.1 h_app_outer.2.2 h_typing]
        have h_app_inner := HasTypeA.app_inv h_app_outer.2.1
        rw [Lambda.denote_app bvarVal h_app_inner.2.1 h_app_inner.2.2 h_app_outer.2.1]
        rw [Lambda.denote_op simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal h_app_inner.2.1]
        -- After denote_op, LHS: ((op_inv ▸ opInterp ...) (denote arg1 aty1_inner ...)) (denote arg2 aty2_outer ...)
        -- Decompose app_inv results and extract types via op_inv
        obtain ⟨aty1', h_op_ty, h_arg1_ty'⟩ := h_app_inner
        obtain ⟨aty2', h_inner_fn_ty, h_arg2_ty'⟩ := h_app_outer
        simp only at *
        have h_opi := HasTypeA.op_inv h_op_ty
        -- h_opi involves .arrow which is .tcons "arrow" [...], use simp to normalize
        simp only [LMonoTy.arrow] at h_opi
        -- Now h_opi : .tcons "arrow" [aty1', .tcons "arrow" [aty2', ...]] = .tcons "arrow" [.tcons "int" [], ...]
        -- Extract aty equalities via noConfusion
        have h_inj := LMonoTy.tcons.inj h_opi
        have h_args := h_inj.2
        have h_aty1_eq : aty1' = _ := (List.cons.inj h_args).1
        subst h_aty1_eq
        have h_tail := (List.cons.inj h_args).2
        have h_aty2_tcons := (List.cons.inj h_tail).1
        have h_aty2_inj := LMonoTy.tcons.inj h_aty2_tcons
        have h_aty2_eq : aty2' = _ := (List.cons.inj h_aty2_inj.2).1
        subst h_aty2_eq
        -- Now op_inv should be rfl
        have h_opi_rfl : HasTypeA.op_inv h_op_ty = rfl := rfl
        rw [h_opi_rfl]
        simp only [simpDenote] at ih_arg1 ih_arg2
        simp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map]
        -- Now need: opInterp ... applied to args ≍ SMTTerm.denote of binary op
        -- The SMTTerm.denote doesn't simp well, so we prove the RHS equality via obtain+rfl pattern
        -- Use `first` to handle each op-specific case
        -- For each case: rewrite opInterp via hop.field, prove SMTTerm.denote equation, connect via IHs
        have h1_heq := (cast_heq _ _).symm.trans
          (ih_convert_smtTy (choose_eq_of_hτ (HasSimpType_result_isBase h_arg1_ty) rfl) ih_arg1)
        have h2_heq := (cast_heq _ _).symm.trans
          (ih_convert_smtTy (choose_eq_of_hτ (HasSimpType_result_isBase h_arg2_ty) rfl) ih_arg2)
        -- Goal is HEq: opInterp o.name arrowSort (denote arg1) (denote arg2) ≍ SMTTerm.denote ... smtTy htc
        -- Infrastructure complete: h1_heq/h2_heq connect args, hop.field connects the op.
        -- Remaining step: rewrite opInterp, determine smtTy, unfold SMTTerm.denote, close by congr.
        -- Split into individual op cases to avoid SMTTerm.denote timeout.
        -- Pattern: determine smtTy, rewrite opInterp via hop, prove SMTTerm.denote unfolds
        -- to the expected form via a `have`, then close with congr + h1_heq/h2_heq.
        first
        | (-- intAdd
           have hsmtTy : smtTy = .int := (Term.typeCheck_intBin_inv htc (.inl rfl)).2.2
           subst hsmtTy; rw [hop.add o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.add [t1, t2] .int) .int htc =
               SMTTerm.denote smtEnv t1 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).1 +
               SMTTerm.denote smtEnv t2 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).2.1 := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intSub
           have hsmtTy : smtTy = .int := (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.2
           subst hsmtTy; rw [hop.sub o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.sub [t1, t2] .int) .int htc =
               SMTTerm.denote smtEnv t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).1 -
               SMTTerm.denote smtEnv t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.1 := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intMul
           have hsmtTy : smtTy = .int := (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.2
           subst hsmtTy; rw [hop.mul o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.mul [t1, t2] .int) .int htc =
               SMTTerm.denote smtEnv t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).1 *
               SMTTerm.denote smtEnv t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1 := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intDiv / intSafeDiv
           have hsmtTy : smtTy = .int := (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2
           subst hsmtTy; first | rw [hop.div o.name hcop] | rw [hop.safeDiv o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.div [t1, t2] .int) .int htc =
               SMTTerm.denote smtEnv t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1 /
               SMTTerm.denote smtEnv t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1 := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intMod / intSafeMod
           have hsmtTy : smtTy = .int := (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2
           subst hsmtTy; first | rw [hop.mod_ o.name hcop] | rw [hop.safeMod o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.mod [t1, t2] .int) .int htc =
               SMTTerm.denote smtEnv t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1 %
               SMTTerm.denote smtEnv t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1 := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intLe
           have hsmtTy : smtTy = .bool := (Term.typeCheck_intCmp_inv htc (.inl rfl)).2.2
           subst hsmtTy; rw [hop.le o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.le [t1, t2] .bool) .bool htc =
               decide (SMTTerm.denote smtEnv t1 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).1 ≤
                       SMTTerm.denote smtEnv t2 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intLt
           have hsmtTy : smtTy = .bool := (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.2
           subst hsmtTy; rw [hop.lt o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.lt [t1, t2] .bool) .bool htc =
               decide (SMTTerm.denote smtEnv t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).1 <
                       SMTTerm.denote smtEnv t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intGe
           have hsmtTy : smtTy = .bool := (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.2
           subst hsmtTy; rw [hop.ge o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.ge [t1, t2] .bool) .bool htc =
               decide (SMTTerm.denote smtEnv t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).1 ≥
                       SMTTerm.denote smtEnv t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intGt
           have hsmtTy : smtTy = .bool := (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.2
           subst hsmtTy; rw [hop.gt o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.gt [t1, t2] .bool) .bool htc =
               decide (SMTTerm.denote smtEnv t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).1 >
                       SMTTerm.denote smtEnv t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- boolAnd
           have hsmtTy : smtTy = .bool := (Term.typeCheck_boolBin_inv htc (.inl rfl)).2.2
           subst hsmtTy; rw [hop.and_ o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.and [t1, t2] .bool) .bool htc =
               (SMTTerm.denote smtEnv t1 .bool (Term.typeCheck_boolBin_inv htc (.inl rfl)).1 &&
                SMTTerm.denote smtEnv t2 .bool (Term.typeCheck_boolBin_inv htc (.inl rfl)).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- boolOr
           have hsmtTy : smtTy = .bool := (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.2
           subst hsmtTy; rw [hop.or_ o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.or [t1, t2] .bool) .bool htc =
               (SMTTerm.denote smtEnv t1 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).1 ||
                SMTTerm.denote smtEnv t2 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- boolImplies
           have hsmtTy : smtTy = .bool := (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.2
           subst hsmtTy; rw [hop.implies o.name hcop]
           have hrhs : SMTTerm.denote smtEnv (.app Op.implies [t1, t2] .bool) .bool htc =
               (!SMTTerm.denote smtEnv t1 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).1 ||
                SMTTerm.denote smtEnv t2 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- boolEquiv (maps to Op.eq / core eq)
           have hsmtTy : smtTy = .bool := (Term.typeCheck_eq_inv htc).2.2.2
           subst hsmtTy; rw [hop.equiv o.name hcop]
           rw [SMTTerm_denote_eq_unfold]
           apply heq_of_eq; simp only [cast_eq]
           have hτ' : (Term.typeCheck_eq_inv htc).1 = .bool := by
             have h1tc := (Term.typeCheck_eq_inv htc).2.1
             have := toSMTTerm_typeChecks hwf arg1 _ _ h_arg1_ty t1 h1_ok
                       (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg1_ty)).choose_spec
             simp only [choose_eq_of_hτ (HasSimpType_result_isBase h_arg1_ty) rfl] at this
             exact Option.some.inj (h1tc.symm.trans this)
           have h1_eq := eq_of_heq h1_heq
           have h2_eq := eq_of_heq h2_heq
           simp only [h1_eq, h2_eq]
           -- Use SMTTerm_denote_cast to bridge the type index difference
           have hd1 := SMTTerm_denote_cast smtEnv t1 .bool (Term.typeCheck_eq_inv htc).1
             (by exact (Term.typeCheck_eq_inv htc).2.1 ▸ (by simp [hτ']))
             (Term.typeCheck_eq_inv htc).2.1 hτ'.symm
           have hd2 := SMTTerm_denote_cast smtEnv t2 .bool (Term.typeCheck_eq_inv htc).1
             (by exact (Term.typeCheck_eq_inv htc).2.2.1 ▸ (by simp [hτ']))
             (Term.typeCheck_eq_inv htc).2.2.1 hτ'.symm
           congr 1; apply propext; constructor
           · intro heq'; exact eq_of_heq (hd1.symm.trans (heq' ▸ hd2))
           · intro heq'; exact eq_of_heq (hd1.trans (heq' ▸ hd2.symm)))

/-- Semantic soundness of toSMTTerm: if an expression `e` is well-typed with type `τ`,
    translates to SMT term `tm`, and the environments correspond, then the LExpr denotation
    of `e` equals the SMT denotation of `tm` (modulo the type cast). -/
theorem toSMTTerm_sound
    {Δ : List LMonoTy} {bvs : BoundVars}
    (hwf : BVarCtxWF Δ bvs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (hop : OpInterpConsistent opInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (smtEnv : SMTVarEnv bvs)
    (henv : EnvCorresponds hwf bvarVal smtEnv)
    (e : Expression.Expr) (τ : LMonoTy)
    (he : LExpr.HasSimpType Δ e τ)
    (tm : Term) (h_ok : toSMTTerm bvs e = .ok tm)
    : let smtTy := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase he)).choose
      let hτ : monoTyToTermType τ = some smtTy :=
        (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase he)).choose_spec
      let htc : Term.typeCheck bvs tm = some smtTy :=
        toSMTTerm_typeChecks hwf e τ smtTy he tm h_ok hτ
      cast (tyDenote_eq_smtTyDenote (HasSimpType_result_isBase he) hτ)
        (simpDenote opInterp bvarVal e τ (HasSimpType_implies_HasTypeA he))
      = SMTTerm.denote smtEnv tm smtTy htc := by
  induction he generalizing bvs tm with
  | @const Δ' c hbase =>
    -- e = .const () c, τ = c.ty, tm = toSMTTerm bvs (.const () c)
    cases c with
    | boolConst b =>
      have htm : tm = .prim (.bool b) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      intro smtTy hτ htc
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, SMTTerm.denote, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ b).trans
        (@subst_heq _ SMTTyDenote _ _ (tc_prim_inv htc) b).symm)
    | intConst i =>
      have htm : tm = .prim (.int i) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      intro smtTy hτ htc
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, SMTTerm.denote, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ i).trans
        (@subst_heq _ SMTTyDenote _ _ (tc_prim_inv htc) i).symm)
    | strConst s =>
      have htm : tm = .prim (.string s) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      intro smtTy hτ htc
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, SMTTerm.denote, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ s).trans
        (@subst_heq _ SMTTyDenote _ _ (tc_prim_inv htc) s).symm)
    | bitvecConst n bv =>
      have htm : tm = .prim (.bitvec bv) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      intro smtTy hτ htc
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, SMTTerm.denote, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ bv).trans
        (@subst_heq _ SMTTyDenote _ _ (tc_prim_inv htc) bv).symm)
    | realConst _ => simp [toSMTTerm] at h_ok
  | @bvar Δ' i τ' hlook hbase =>
    simp only [toSMTTerm] at h_ok
    split at h_ok
    · next hi =>
      have htm : tm = .var (bvs[i]) := by simp at h_ok; exact h_ok.symm
      subst htm
      -- Goal: cast ... (simpDenote ...) = SMTTerm.denote smtEnv (.var bvs[i]) smtTy htc
      simp only [simpDenote, LExpr.denote]
      -- LHS: cast (tyDenote_eq_smtTyDenote hbase hτ) (bvarVal.get i bvar_inv_proof)
      -- RHS: SMTTerm.denote smtEnv (.var bvs[i]) smtTy htc
      -- Use EnvCorresponds
      have hcorr := henv i τ' hbase hlook
      -- hcorr : cast (tyDenote_eq_smtTyDenote hbase hty) (bvarVal.get i hlook) = smtEnv bvs[i] hmem
      apply eq_of_heq
      -- LHS ≍ RHS
      -- Step 1: strip outer cast on LHS
      refine HEq.trans (cast_heq _ _) ?_
      -- bvarVal.get i bvar_inv_proof ≍ SMTTerm.denote ...
      -- Step 2: Use SMTTerm_denote_var_heq to strip RHS to smtEnv lookup
      refine HEq.trans ?_ (SMTTerm_denote_var_heq _ _ _ _).symm
      -- bvarVal.get i bvar_inv_proof ≍ smtEnv bvs[i] (tc_var_inv htc).1
      -- Step 3: From hcorr, bvarVal.get i hlook ≍ smtEnv bvs[i] hmem (via cast_heq)
      -- bvar_inv_proof = hlook by proof irrel, and (tc_var_inv htc).1 = hmem by proof irrel
      exact (cast_heq _ _).symm.trans (heq_of_eq hcorr)
    · next hni =>
      exfalso; revert h_ok; simp (config := { decide := true })
  | app1 hop_ty h_arg_ty ih_arg =>
    -- The goal has let-bound smtTy that depends on hop_ty.
    -- We can't generalize/cases directly. Instead, use `exact` with a helper.
    have he' := LExpr.HasSimpType.app1 hop_ty h_arg_ty
    have hbase' := HasSimpType_result_isBase he'
    have hτ' := (MonoTyIsBase_monoTyToTermType hbase').choose_spec
    have htc' := toSMTTerm_typeChecks hwf _ _ _ he' tm h_ok hτ'
    exact toSMTTerm_sound_app1 hwf opInterp hop bvarVal smtEnv henv hop_ty h_arg_ty ih_arg tm h_ok
      hbase' _ hτ' htc' (HasSimpType_implies_HasTypeA he')
  | app2 hop_ty h_arg1_ty h_arg2_ty ih_arg1 ih_arg2 =>
    have he' := LExpr.HasSimpType.app2 hop_ty h_arg1_ty h_arg2_ty
    have hbase' := HasSimpType_result_isBase he'
    have hτ' := (MonoTyIsBase_monoTyToTermType hbase').choose_spec
    have htc' := toSMTTerm_typeChecks hwf _ _ _ he' tm h_ok hτ'
    exact toSMTTerm_sound_app2 hwf opInterp hop bvarVal smtEnv henv hop_ty h_arg1_ty h_arg2_ty ih_arg1 ih_arg2 tm h_ok
      hbase' _ hτ' htc' (HasSimpType_implies_HasTypeA he')
  | @ite _ _ _ τ' _ hc_ty ht_ty he_ty ihc iht ihe =>
    -- toSMTTerm bvs (.ite () c_expr t_expr e_expr) produces .app (.core .ite) [ct, tt, et] tt.typeOf
    rename_i Δ' c_expr t_expr e_expr
    -- Extract sub-translations from h_ok using cases on toSMTTerm results
    have h_ok' := h_ok
    simp only [toSMTTerm, bind, Except.bind] at h_ok'
    revert h_ok h_ok'
    cases hc_ok : toSMTTerm bvs c_expr with
    | error _ => simp [toSMTTerm, bind, Except.bind]
    | ok ct =>
      cases ht_ok : toSMTTerm bvs t_expr with
      | error _ => simp [toSMTTerm, bind, Except.bind]
      | ok tt_tm =>
        cases he_ok : toSMTTerm bvs e_expr with
        | error _ => simp [toSMTTerm, bind, Except.bind]
        | ok et =>
          intro h_ok h_ok'
          have htm : tm = Term.app (.core .ite) [ct, tt_tm, et] (Term.typeOf tt_tm) := by
            simp [toSMTTerm, bind, Except.bind, hc_ok, ht_ok, he_ok] at h_ok
            exact h_ok.symm
          subst htm
          intro smtTy hτ htc
          -- Use IHs directly with let-elimination
          specialize ihc hwf bvarVal smtEnv henv ct hc_ok
          specialize iht hwf bvarVal smtEnv henv tt_tm ht_ok
          specialize ihe hwf bvarVal smtEnv henv et he_ok
          simp only at ihc iht ihe
          -- Step 1: Rewrite LHS using denote_ite
          have h_ite_unfold := Lambda.denote_ite (T := CoreLParams) (tcInterp := simpTcInterp)
            (opInterp := opInterp) (fvarVal := simpFvarVal) (vt := simpTyVarVal)
            bvarVal
            (HasSimpType_implies_HasTypeA hc_ty)
            (HasSimpType_implies_HasTypeA ht_ty)
            (HasSimpType_implies_HasTypeA he_ty)
            (HasSimpType_implies_HasTypeA (LExpr.HasSimpType.ite hc_ty ht_ty he_ty))
          simp only [simpDenote] at ihc iht ihe ⊢
          rw [h_ite_unfold]
          -- LHS is now: cast tyEq (bif denote c .bool h_c then denote t τ h_t else denote e τ h_e)
          -- RHS: SMTTerm.denote smtEnv (.app (.core .ite) [ct, tt_tm, et] ...) smtTy htc
          rw [SMTTerm_denote_ite]
          -- RHS is now: bif SMTTerm.denote ct .bool _ then SMTTerm.denote tt smtTy _ else SMTTerm.denote et smtTy _
          -- Apply bif_heq_of_cond_branches: cast h (bif b1 then t1 else e1) = bif b2 then t2 else e2
          apply bif_heq_of_cond_branches
          · -- b1 = b2: condition equality (both Bool)
            have hc_eq := choose_eq_of_hτ (HasSimpType_result_isBase hc_ty)
              (show monoTyToTermType (.tcons "bool" []) = some TermType.bool from rfl)
            exact eq_of_heq ((cast_heq _ _).symm.trans (ih_convert_smtTy hc_eq ihc))
          · -- t1 ≍ t2: branch HEq
            have ht_eq := choose_eq_of_hτ (HasSimpType_result_isBase ht_ty) hτ
            exact (cast_heq _ _).symm.trans (ih_convert_smtTy ht_eq iht)
          · -- e1 ≍ e2
            have he_eq := choose_eq_of_hτ (HasSimpType_result_isBase he_ty) hτ
            exact (cast_heq _ _).symm.trans (ih_convert_smtTy he_eq ihe)
  | eq hbase he1_ty he2_ty ih1 ih2 =>
    rename_i τ_eq Δ' e1_expr e2_expr
    have h_ok' := h_ok
    simp only [toSMTTerm, bind, Except.bind] at h_ok'
    revert h_ok h_ok'
    cases h1_ok : toSMTTerm bvs e1_expr with
    | error _ => simp [toSMTTerm, bind, Except.bind]
    | ok t1 =>
      cases h2_ok : toSMTTerm bvs e2_expr with
      | error _ => simp [toSMTTerm, bind, Except.bind]
      | ok t2 =>
        intro h_ok h_ok'
        have htm : tm = Term.app (.core .eq) [t1, t2] .bool := by
          simp [toSMTTerm, bind, Except.bind, h1_ok, h2_ok] at h_ok
          exact h_ok.symm
        subst htm
        intro smtTy hτ htc
        -- Specialize IHs for e1 and e2
        specialize ih1 hwf bvarVal smtEnv henv t1 h1_ok
        specialize ih2 hwf bvarVal smtEnv henv t2 h2_ok
        simp only at ih1 ih2
        simp only [simpDenote] at ih1 ih2 ⊢
        -- Rewrite RHS using the eq unfolding lemma
        rw [SMTTerm_denote_eq_unfold]
        -- Obtain the shared SMT type from typeCheck_eq_inv as a free variable we can subst
        obtain ⟨τ'_smt, htc1_inv, htc2_inv, heq_bool⟩ := Term.typeCheck_eq_inv htc
        -- Get the IH's smtTy for sub-expressions
        have hτ_sub_spec := (MonoTyIsBase_monoTyToTermType hbase).choose_spec
        have htc1_ih := toSMTTerm_typeChecks hwf e1_expr τ_eq _ he1_ty t1 h1_ok hτ_sub_spec
        have htc2_ih := toSMTTerm_typeChecks hwf e2_expr τ_eq _ he2_ty t2 h2_ok hτ_sub_spec
        -- τ'_smt = (MonoTyIsBase_monoTyToTermType hbase).choose
        have hτ'_eq : τ'_smt = (MonoTyIsBase_monoTyToTermType hbase).choose :=
          Option.some.inj (htc1_inv.symm.trans htc1_ih)
        subst hτ'_eq
        -- Now τ'_smt has been unified with the IH's smtTy.
        -- The IHs now have the same smtTy as the RHS.
        -- ih1 : cast _ v1 = SMTTerm.denote smtEnv t1 choose htc1_ih_proof
        -- RHS uses SMTTerm.denote smtEnv t1 choose htc1_inv
        -- By proof irrelevance: htc1_inv = htc1_ih, htc2_inv = htc2_ih (both are proofs of Prop)
        -- Case analysis on equality of LExpr denotations
        by_cases heq_vals : LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal
            e1_expr τ_eq (HasSimpType_implies_HasTypeA he1_ty) =
          LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal
            e2_expr τ_eq (HasSimpType_implies_HasTypeA he2_ty)
        · -- v1 = v2: LHS = cast _ true
          have h_lhs : LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal
              (.eq () e1_expr e2_expr) (.tcons "bool" [])
              (HasSimpType_implies_HasTypeA (LExpr.HasSimpType.eq hbase he1_ty he2_ty)) = true :=
            Lambda.denote_eq_true bvarVal
              (HasSimpType_implies_HasTypeA he1_ty)
              (HasSimpType_implies_HasTypeA he2_ty)
              (HasSimpType_implies_HasTypeA (LExpr.HasSimpType.eq hbase he1_ty he2_ty))
              heq_vals
          rw [h_lhs]
          -- Show SMT denotations are also equal
          have hw_eq : SMTTerm.denote smtEnv t1 _ htc1_inv =
              SMTTerm.denote smtEnv t2 _ htc2_inv := by
            exact ih1.symm.trans (congrArg _ heq_vals |>.trans ih2)
          simp only [hw_eq, decide_true]; rfl
        · -- v1 ≠ v2: LHS = cast _ false
          have h_lhs : LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal
              (.eq () e1_expr e2_expr) (.tcons "bool" [])
              (HasSimpType_implies_HasTypeA (LExpr.HasSimpType.eq hbase he1_ty he2_ty)) = false :=
            Lambda.denote_eq_false bvarVal
              (HasSimpType_implies_HasTypeA he1_ty)
              (HasSimpType_implies_HasTypeA he2_ty)
              (HasSimpType_implies_HasTypeA (LExpr.HasSimpType.eq hbase he1_ty he2_ty))
              heq_vals
          rw [h_lhs]
          -- Show SMT denotations are also not equal
          have hw_neq : SMTTerm.denote smtEnv t1 _ htc1_inv ≠
              SMTTerm.denote smtEnv t2 _ htc2_inv := by
            intro hw
            apply heq_vals
            -- From IHs and hw, derive v1 = v2
            -- ih1 : cast h v1 = w1, ih2 : cast h v2 = w2, hw : w1 = w2
            -- So cast h v1 = cast h v2, hence v1 = v2
            have hcast : cast (tyDenote_eq_smtTyDenote hbase hτ_sub_spec)
                (LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal
                  e1_expr τ_eq (HasSimpType_implies_HasTypeA he1_ty)) =
              cast (tyDenote_eq_smtTyDenote hbase hτ_sub_spec)
                (LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal bvarVal
                  e2_expr τ_eq (HasSimpType_implies_HasTypeA he2_ty)) :=
              ih1.trans (hw.trans ih2.symm)
            have hinj : ∀ {α β : Type} (h : α = β) (a b : α), cast h a = cast h b → a = b :=
              fun h _ _ heq => by cases h; exact heq
            exact hinj _ _ _ hcast
          simp only [hw_neq, decide_false]; rfl
  | quant hbase he_body ih_body =>
    -- quant case: both sides compute decide(∀ x, body x = true) / decide(∀ ext, body_smt ext = true)
    -- hbase : MonoTyIsBase qty
    -- he_body : HasSimpType (qty :: Δ) body (.tcons "bool" [])
    -- ih_body : IH for body
    obtain ⟨smtQTy, hqty⟩ := MonoTyIsBase_monoTyToTermType hbase
    -- Extract the body translation from h_ok
    simp only [toSMTTerm, hqty, bind, Except.bind] at h_ok
    revert h_ok
    cases hbody_ok : toSMTTerm (⟨s!"$__bv{bvs.length}", smtQTy⟩ :: bvs) _ with
    | error _ => simp
    | ok bodyTm =>
      simp only [Except.ok.injEq]
      intro h_tm; subst h_tm
      -- Build extended BVarCtxWF for (qty :: Δ) and (v :: bvs)
      let v : TermVar := ⟨s!"$__bv{bvs.length}", smtQTy⟩
      have hwf' : BVarCtxWF (_ :: _) (v :: bvs) :=
        ⟨congrArg (· + 1) hwf.len_eq, fun i hi => by
          cases i with
          | zero => exact hqty
          | succ j =>
            simp only [List.length, Nat.succ_lt_succ_iff] at hi
            simp only [List.getElem_cons_succ]
            exact hwf.ty_eq j hi,
         fun i hi => by
          cases i with
          | zero => simp [v, List.length]
          | succ j =>
            simp only [List.getElem_cons_succ, List.length] at hi ⊢
            have hj_lt : j < bvs.length := by omega
            have := hwf.id_scheme j hj_lt
            rw [this]; simp; congr 1; omega⟩
      -- Get body type-check proof
      have hbody_tc : Term.typeCheck (v :: bvs) bodyTm = some .bool :=
        toSMTTerm_typeChecks hwf' _ (.tcons "bool" []) .bool he_body bodyTm hbody_ok rfl
      -- Use the IH to show body denotations match for each witness
      have body_eq : ∀ x : Lambda.TyDenote simpTcInterp simpTyVarVal _,
          ∀ (smtEnv' : SMTVarEnv (v :: bvs)),
          EnvCorresponds hwf' (.cons x bvarVal) smtEnv' →
          (LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal
            (.cons x bvarVal) _ (.tcons "bool" [])
            (HasSimpType_implies_HasTypeA he_body) : Bool) =
          SMTTerm.denote smtEnv' bodyTm .bool hbody_tc := by
        intro x smtEnv' henv'
        have ih := ih_body hwf' (.cons x bvarVal) smtEnv' henv' bodyTm hbody_ok
        simp only [simpDenote] at ih
        -- ih : cast h (denote ... body .bool ...) = SMTTerm.denote smtEnv' bodyTm choose choose_spec
        -- The choose = .bool since body has type bool
        have hchoose : (MonoTyIsBase_monoTyToTermType
            (HasSimpType_result_isBase he_body)).choose = .bool :=
          choose_eq_of_hτ (HasSimpType_result_isBase he_body) rfl
        -- From ih: cast h (denote body) = SMTTerm.denote smtEnv' bodyTm choose htc
        -- We need: denote body = SMTTerm.denote smtEnv' bodyTm .bool hbody_tc
        -- Step 1: strip the cast (it's Bool → Bool, hence id)
        -- The LHS type is SMTTyDenote choose = SMTTyDenote .bool = Bool (by hchoose)
        -- The cast proof is tyDenote_eq_smtTyDenote .bool choose_spec : Bool = SMTTyDenote choose
        -- Since choose = .bool, SMTTyDenote choose = Bool, so cast is id
        have ih_eq : (LExpr.denote simpTcInterp opInterp simpFvarVal simpTyVarVal
            (.cons x bvarVal) _ (.tcons "bool" [])
            (HasSimpType_implies_HasTypeA he_body) : Bool) =
            SMTTerm.denote smtEnv' bodyTm .bool hbody_tc := by
          have h_eq_heq := ih_convert_smtTy hchoose ih
          exact eq_of_heq ((cast_heq _ _).symm.trans h_eq_heq)
        exact ih_eq
      -- Apply the helper lemma (case split on k to reduce match)
      cases ‹Lambda.QuantifierKind› with
      | all =>
        exact toSMTTerm_sound_quant hwf opInterp bvarVal smtEnv henv _ _ _ _ hbase he_body
          smtQTy hqty bodyTm _ rfl hwf' hbody_tc body_eq h_ok
      | exist =>
        exact toSMTTerm_sound_quant hwf opInterp bvarVal smtEnv henv _ _ _ _ hbase he_body
          smtQTy hqty bodyTm _ rfl hwf' hbody_tc body_eq h_ok
