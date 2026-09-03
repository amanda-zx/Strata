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
# Spine-aware SMT translation with user-defined function declarations

This file extends the n-ary free-variable SMT encoder with support for user-defined
function declarations: opaque functions with no body and no axioms — a pure
`declare-fun` / uninterpreted `UF`. A user-defined-function reference is an
`.op () f (some fnty)` node whose `f.name` is NOT a predefined `CoreOp`. It encodes to a
`UF` application exactly like an n-ary free variable, except that on the LExpr side an
`.op` node denotes through `opInterp`, whereas an `.fvar` node denotes through `fvarVal`.
The function interpretation is arbitrary, related to the SMT `ufInterp` only through the
hypothesised correspondence `OpEnvCorresponds`.

Concretely, the typing judgment `LExpr.HasSimpType` and its application-spine judgment
`LExpr.AppSpine` carry a user-defined-function context `Ψ : FnCtx`, and `AppSpine` gains a
`.fnOp` head — an `.op` node whose symbol is not predefined, keyed on `Ψ` and denoting
through `opInterp`, the op-world analog of the `.fvar` head. The encoder `toSMTTerm`
(via `buildAppHead`) falls back to a `UF` application for such heads. Correctness is
stated against the SMT-side type checker `Term.typeCheck` and denotation `SMTTerm.denote`.

Key definitions: `LExpr.HasSimpType`, `LExpr.AppSpine`, `FnCtx`, `toSMTTerm`,
`Term.typeCheck`, `SMTTerm.denote`, `FVarCtxWF`, `UFEnvCorresponds`, `OpEnvCorresponds`.
Key results: `toSMTTerm_type_correct`, `toSMTTerm_correct`, and their mutual cores
`toSMTTerm_typeChecks` and `toSMTTerm_sound`.
-/

open Core Lambda Imperative Strata.SMT Std


/-! ## LExpr type restrictions -/

inductive LExpr.MonoTyIsBase : LMonoTy → Prop where
  | bool : MonoTyIsBase (.tcons "bool" [])
  | int : MonoTyIsBase (.tcons "int" [])
  | string : MonoTyIsBase (.tcons "string" [])
  | bitvec : MonoTyIsBase (.bitvec n)

/- Free variables can have arrow types -/
inductive LExpr.MonoTyIsSimp : LMonoTy → Prop where
  | base : LExpr.MonoTyIsBase t → LExpr.MonoTyIsSimp t
  | arrow : LExpr.MonoTyIsBase aty →
    LExpr.MonoTyIsSimp rty →
    LExpr.MonoTyIsSimp (.tcons "arrow" [aty, rty])

inductive LExpr.CoreOpHasType : CoreOp → List LMonoTy → LMonoTy → Prop where
  -- Unary int
  | intNeg : CoreOpHasType (.numeric ⟨.int, .Neg⟩) [.tcons "int" []] (.tcons "int" [])
  -- Unary bool
  | boolNot : CoreOpHasType (.bool .Not) [.tcons "bool" []] (.tcons "bool" [])
  -- Binary int → int
  | intAdd : CoreOpHasType (.numeric ⟨.int, .Add⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intSub : CoreOpHasType (.numeric ⟨.int, .Sub⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intMul : CoreOpHasType (.numeric ⟨.int, .Mul⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intDiv : CoreOpHasType (.numeric ⟨.int, .Div⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intSafeDiv : CoreOpHasType (.numeric ⟨.int, .SafeDiv⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intMod : CoreOpHasType (.numeric ⟨.int, .Mod⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intSafeMod : CoreOpHasType (.numeric ⟨.int, .SafeMod⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intDivT : CoreOpHasType (.numeric ⟨.int, .DivT⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intSafeDivT : CoreOpHasType (.numeric ⟨.int, .SafeDivT⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intModT : CoreOpHasType (.numeric ⟨.int, .ModT⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intSafeModT : CoreOpHasType (.numeric ⟨.int, .SafeModT⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  -- Binary int → bool (comparisons)
  | intLt : CoreOpHasType (.numeric ⟨.int, .Lt⟩) [.tcons "int" [], .tcons "int" []] (.tcons "bool" [])
  | intLe : CoreOpHasType (.numeric ⟨.int, .Le⟩) [.tcons "int" [], .tcons "int" []] (.tcons "bool" [])
  | intGt : CoreOpHasType (.numeric ⟨.int, .Gt⟩) [.tcons "int" [], .tcons "int" []] (.tcons "bool" [])
  | intGe : CoreOpHasType (.numeric ⟨.int, .Ge⟩) [.tcons "int" [], .tcons "int" []] (.tcons "bool" [])
  -- Binary bool → bool
  | boolAnd : CoreOpHasType (.bool .And) [.tcons "bool" [], .tcons "bool" []] (.tcons "bool" [])
  | boolOr : CoreOpHasType (.bool .Or) [.tcons "bool" [], .tcons "bool" []] (.tcons "bool" [])
  | boolImplies : CoreOpHasType (.bool .Implies) [.tcons "bool" [], .tcons "bool" []] (.tcons "bool" [])
  | boolEquiv : CoreOpHasType (.bool .Equiv) [.tcons "bool" [], .tcons "bool" []] (.tcons "bool" [])

/-! ## Free-variable context and arrow-type helper

`collectArrowTy` relates a free variable's declared type to its argument/return
decomposition for function application. -/

def collectArrowTy : LMonoTy → List LMonoTy × LMonoTy
  | .tcons "arrow" [ty1, ty2] =>
    let (atys, rty) := collectArrowTy ty2
    (ty1 :: atys, rty)
  | ty => ([], ty)

-- Defined here because the `.fnOp` head of `AppSpine` guards on
-- `corePredefinedOpToSMTOp … = none`.
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
  | .numeric ⟨.int, .Div⟩ | .numeric ⟨.int, .SafeDiv⟩
  | .numeric ⟨.int, .DivT⟩ | .numeric ⟨.int, .SafeDivT⟩ => some (.app Op.div, .int)
  | .numeric ⟨.int, .Mod⟩ | .numeric ⟨.int, .SafeMod⟩
  | .numeric ⟨.int, .ModT⟩ | .numeric ⟨.int, .SafeModT⟩ => some (.app Op.mod, .int)
  | .numeric ⟨.int, .Neg⟩ => some (.app Op.neg, .int)
  | .numeric ⟨.int, .Lt⟩ => some (.app Op.lt, .bool)
  | .numeric ⟨.int, .Le⟩ => some (.app Op.le, .bool)
  | .numeric ⟨.int, .Gt⟩ => some (.app Op.gt, .bool)
  | .numeric ⟨.int, .Ge⟩ => some (.app Op.ge, .bool)
  | _ => none

/-! ## Typing judgment on `Expression.Expr` with n-ary free-variable application -/

abbrev FVarCtx := List (String × LMonoTy)

/-- A user-defined-function context: declared (name, full arrow type). Keyed
    for `.op` heads, structurally identical to `FVarCtx`. -/
abbrev FnCtx := List (String × LMonoTy)

mutual
inductive LExpr.HasSimpType (Φ : FVarCtx) (Ψ : FnCtx) : List LMonoTy → Expression.Expr → LMonoTy → Prop where
  | const c : MonoTyIsBase c.ty → HasSimpType Φ Ψ Δ (.const () c) c.ty
  | bvar i τ : Δ[i]? = some τ → MonoTyIsBase τ → HasSimpType Φ Ψ Δ (.bvar () i) τ
  -- An application node is typed by the application-spine judgment with no extra
  -- pending arguments; this subject is the *real* `.app` tree the encoder peels.
  | app fn arg rty : LExpr.AppSpine Φ Ψ Δ (.app () fn arg) [] rty →
    HasSimpType Φ Ψ Δ (.app () fn arg) rty
  -- A bare free variable is a nullary application head.
  | fvarNullary f τ rty : LExpr.AppSpine Φ Ψ Δ (.fvar () f (some τ)) [] rty →
    HasSimpType Φ Ψ Δ (.fvar () f (some τ)) rty
  | ite c t τ e : HasSimpType Φ Ψ Δ c (.tcons "bool" []) → HasSimpType Φ Ψ Δ t τ →
    HasSimpType Φ Ψ Δ e τ → HasSimpType Φ Ψ Δ (.ite () c t e) τ
  | eq e1 e2 τ : MonoTyIsBase τ → HasSimpType Φ Ψ Δ e1 τ → HasSimpType Φ Ψ Δ e2 τ →
    HasSimpType Φ Ψ Δ (.eq () e1 e2) (.tcons "bool" [])
  | quant qty body k name : MonoTyIsBase qty → HasSimpType Φ Ψ (qty :: Δ) body (.tcons "bool" []) →
    HasSimpType Φ Ψ Δ (.quant () k name (some qty) (.const () (.boolConst true)) body) (.tcons "bool" [])

/-- Application-spine judgment. `AppSpine Φ Ψ Δ e acc rty` types the head-spine `e`
    applied to `e`'s own arguments followed by `acc` more arguments (whose types
    are the elements of `acc`, appearing to the right), yielding base type `rty`. -/
inductive LExpr.AppSpine (Φ : FVarCtx) (Ψ : FnCtx) : List LMonoTy → Expression.Expr → List LMonoTy → LMonoTy → Prop where
  | app fn arg aty acc rty : LExpr.HasSimpType Φ Ψ Δ arg aty →
    LExpr.AppSpine Φ Ψ Δ fn (aty :: acc) rty →
    LExpr.AppSpine Φ Ψ Δ (.app () fn arg) acc rty
  -- Free-variable head: its declared type decomposes into exactly the pending
  -- argument types `acc` and a base return type.
  | fvar f τ acc rty : (f.name, τ) ∈ Φ → collectArrowTy τ = (acc, rty) →
    MonoTyIsBase rty → LExpr.AppSpine Φ Ψ Δ (.fvar () f (some τ)) acc rty
  -- Operator head: the pending argument types `acc` are exactly the op's argument
  -- types, and the annotation `oty` must decompose into exactly those argument
  -- types and the return type — the op-world analog of `(f.name, τ) ∈ Φ` for fvars.
  | op o oty acc rty : CoreOpHasType (CoreOp.ofString o.name) acc rty →
    collectArrowTy oty = (acc, rty) →
    LExpr.AppSpine Φ Ψ Δ (.op () o (some oty)) acc rty
  -- User-defined-function head: an `.op` node whose symbol is NOT predefined.
  -- Its declared type decomposes into the pending argument types `acc` and a
  -- base return type, exactly like the `.fvar` head; the difference is only
  -- that it denotes through `opInterp` rather than `fvarVal`.
  | fnOp o oty acc rty : (o.name, oty) ∈ Ψ →
      corePredefinedOpToSMTOp (CoreOp.ofString o.name) = none →
      collectArrowTy oty = (acc, rty) →
      MonoTyIsBase rty →
      LExpr.AppSpine Φ Ψ Δ (.op () o (some oty)) acc rty
end

/-! ## LExpr denotation -/

noncomputable def simpTcInterp : Lambda.TyConstrInterp := fun _ _ => Unit

instance : Lambda.TyConstrInterp.AllInhabited simpTcInterp where
  inhabited := fun _ _ => ⟨()⟩

def simpTyVarVal : Lambda.TyVarVal := fun _ => .tcons "bool" []

noncomputable def simpDenote
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {Δ : List LMonoTy}
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (e : Expression.Expr) (τ : LMonoTy)
    (h : LExpr.HasTypeA Δ e τ)
    : Lambda.TyDenote simpTcInterp simpTyVarVal τ :=
  LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal e τ h


/-! ## SMT type checker -/

abbrev UFCtx := List UF
abbrev TermVarCtx := List TermVar

mutual
-- Each `.app` branch additionally checks that the stored return annotation `rty`
-- equals the operator's computed result type. `Term.typeOf` reads that annotation
-- directly, so validating it keeps `typeOf` and the type at which the term
-- type-checks (hence denotes) in agreement — the SMT-side analog of the fidelity
-- condition on `.op` annotations in `AppSpine`.
def Term.typeCheck (ufs : UFCtx) (Γ : List TermVar) : Term → Option TermType
  | .prim p => some p.typeOf
  -- A variable resolves to the *innermost* enclosing binder of its printed name.
  -- The context is kept innermost-first (each binder group is `reverse`d when
  -- pushed, see the `.quant` case), so `Γ.find?`'s leftmost match is the innermost
  -- binder — matching SMT-LIB 2.7 lexical scoping, where within a single binder
  -- list the *last* occurrence of a name shadows earlier ones. Requiring that
  -- innermost binder to be `v` itself means a same-named binder of a different sort
  -- shadows `v`, so a reference carrying the wrong sort fails to type-check. This is
  -- the value-world analog of the anti-shadowing side condition on the `.uf` case below.
  | .var v => if Γ.find? (fun w => w.id == v.id) = some v then some v.ty else none
  -- A UF application additionally requires that the function symbol's name is not
  -- captured by an enclosing bound variable. UFs and `TermVar`s occupy separate
  -- namespaces in this AST, but SMT-LIB resolves the printed name by lexical
  -- scope, where a bound variable shadows a same-named function symbol. Rejecting
  -- the collision keeps our denotation faithful to solver semantics.
  | .app (.core (.uf uf)) args rty =>
    let sig := uf
    if sig ∈ ufs ∧ sig.id ∉ Γ.map (·.id) then
      if rty == sig.out && typeCheckArgs ufs Γ args sig.args then some sig.out
      else none
    else none
  | .app (.core .not) [t] rty => do
    let tTy ← typeCheck ufs Γ t
    if tTy == .bool && rty == .bool then some .bool else none
  | .app (.core .and) [t1, t2] rty | .app (.core .or) [t1, t2] rty
  | .app (.core .implies) [t1, t2] rty => do
    let ty1 ← typeCheck ufs Γ t1
    let ty2 ← typeCheck ufs Γ t2
    if ty1 == .bool && ty2 == .bool && rty == .bool then some .bool else none
  | .app (.core .eq) [t1, t2] rty => do
    let ty1 ← typeCheck ufs Γ t1
    let ty2 ← typeCheck ufs Γ t2
    if ty1 == ty2 && rty == .bool then some .bool else none
  | .app (.core .ite) [c, t, e] rty => do
    let cTy ← typeCheck ufs Γ c
    let tTy ← typeCheck ufs Γ t
    let eTy ← typeCheck ufs Γ e
    if cTy == .bool && tTy == eTy && rty == tTy then some tTy else none
  | .app (.num .neg) [t] rty => do
    let tTy ← typeCheck ufs Γ t
    if tTy == .int && rty == .int then some .int else none
  | .app (.num .add) [t1, t2] rty | .app (.num .sub) [t1, t2] rty
  | .app (.num .mul) [t1, t2] rty | .app (.num .div) [t1, t2] rty
  | .app (.num .mod) [t1, t2] rty => do
    let ty1 ← typeCheck ufs Γ t1
    let ty2 ← typeCheck ufs Γ t2
    if ty1 == .int && ty2 == .int && rty == .int then some .int else none
  | .app (.num .le) [t1, t2] rty | .app (.num .lt) [t1, t2] rty
  | .app (.num .ge) [t1, t2] rty | .app (.num .gt) [t1, t2] rty => do
    let ty1 ← typeCheck ufs Γ t1
    let ty2 ← typeCheck ufs Γ t2
    if ty1 == .int && ty2 == .int && rty == .bool then some .bool else none
  -- `distinct` is variadic but, per the SMT-LIB spec, requires at least two
  -- arguments — hence the `t1 :: t2 :: ts` pattern (fewer than two args falls
  -- through to `none`). Every argument must share the first argument's type,
  -- checked by reusing `typeCheckArgs` against a `replicate` of that type, which
  -- exercises the arbitrary-length argument path.
  | .app (.core .distinct) (t1 :: t2 :: ts) rty => do
    let ty ← typeCheck ufs Γ t1
    if typeCheckArgs ufs Γ (t2 :: ts) (List.replicate (t2 :: ts).length ty) && rty == .bool
    then some .bool else none
  | .quant _ vs _ body => do
    -- Push the binder group innermost-first (`vs.reverse`): per SMT-LIB 2.7 the
    -- *last* variable in `vs` is the innermost binder, so reversing makes the
    -- flattened context uniformly innermost-first for the `.var` lookup.
    let bodyTy ← typeCheck ufs (vs.reverse ++ Γ) body
    if bodyTy == .bool then some .bool else none
  | _ => none

def Term.typeCheckArgs (ufs : UFCtx) (Γ : List TermVar) :
    List Term → List TermType → Bool
  | [], [] => true
  | t :: ts, expectedTy :: rest =>
    match typeCheck ufs Γ t with
    | some ty => ty == expectedTy && typeCheckArgs ufs Γ ts rest
    | none => false
  | _, _ => false
end

/-- Because every `.app` branch of `typeCheck` validates the stored return
    annotation against the computed result type, the syntactic `Term.typeOf`
    always agrees with the type at which a term type-checks. -/
theorem Term.typeOf_of_typeCheck {ufs : UFCtx} {Γ : List TermVar} {tm : Term} {τ : TermType}
    (h : Term.typeCheck ufs Γ tm = some τ) : Term.typeOf tm = τ := by
  match tm with
  | .prim p => simp only [Term.typeCheck, Option.some.injEq] at h; simp [Term.typeOf, h]
  | .var v =>
    simp only [Term.typeCheck] at h; split at h <;> simp_all [Term.typeOf]
  | .quant k vs tr body =>
    simp only [Term.typeCheck] at h; revert h
    cases Term.typeCheck ufs (vs.reverse ++ Γ) body with
    | none => simp [bind, Option.bind]
    | some tyb =>
      simp only [bind, Option.bind]; intro h'; split at h' <;> simp_all [Term.typeOf]
  | .app op args rty =>
    -- In every case `typeCheck` succeeds, it returns exactly the annotation `rty`
    -- (guarded by `rty == …`); `Term.typeOf (.app _ _ rty) = rty`.
    simp only [Term.typeOf]
    -- One split over the compiled match yields one goal per operator/arity arm.
    -- Each arm returns `some τ` only behind a guard that includes `rty == τ`.
    -- We rewrite the option-bind/`ite` chains into existentials/conjunctions
    -- (rather than `split`, which cannot peel the `Option.bind` match whose motive
    -- mentions the continuation), exposing `rty = τ`, which `grind` then derives
    -- (also using the injectivity of the `.app` discriminant equation).
    unfold Term.typeCheck at h
    split at h <;>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
        Bool.and_eq_true, beq_iff_eq, Option.some.injEq, reduceCtorEq] at h <;>
      grind
  | .none _ => simp only [Term.typeCheck] at h; exact absurd h nofun
  | .some _ => simp only [Term.typeCheck] at h; exact absurd h nofun

/-! ## SMT Term denotation -/

/-- Well-formedness of SMT types: restricts to primitive base types that have
meaningful denotations. Analogous to `MonoTyIsBase` on the LExpr side. -/
inductive SMTTyIsBase : TermType → Prop where
  | bool : SMTTyIsBase .bool
  | int : SMTTyIsBase .int
  | string : SMTTyIsBase .string
  | bitvec : SMTTyIsBase (.bitvec n)

@[reducible] def SMTTyDenote : TermType → Type
  | .prim .bool => Bool
  | .prim .int => Int
  | .prim (.bitvec n) => BitVec n
  | .prim .string => String
  | _ => Unit

/--
Every sort denotes an inhabited type, given that the type constructor
interpretation produces inhabited types.
-/
instance SMTTyDenote.inhabited (τ : TermType) : Inhabited (SMTTyDenote τ) := by
  cases τ with
  | prim p => cases p with
    | bool => exact ⟨false⟩
    | int => exact ⟨0⟩
    | bitvec n => exact ⟨0⟩
    | string => exact ⟨""⟩
    | _ => exact ⟨()⟩
  | _ => exact ⟨()⟩


/-- Curried function type for n-ary UF denotation.
    `UFDenote [.int, .bool] .int = Int → Bool → Int` -/
def UFDenote' : List TermType → TermType → Type
  | [], out => SMTTyDenote out
  | arg :: rest, out => SMTTyDenote arg → UFDenote' rest out

def UFDenote (uf : UF) : Type :=
  UFDenote' uf.args uf.out

/-- Apply a curried UF denotation to an HList of argument values. -/
noncomputable def applyUFDenote :
    (argTys : List TermType) → (out : TermType) →
    UFDenote' argTys out → HList SMTTyDenote argTys → SMTTyDenote out
  | [], _, val, .nil => val
  | _ :: rest, out, f, .cons v vs => applyUFDenote rest out (f v) vs

/-- N-ary UF interpretation: maps each declared UF signature to a curried
    function from argument types to output type. -/
def UFInterp := (uf : UF) → UFDenote uf

/-- Variable environment for SMT: maps bound variables to values of their types. -/
def SMTVarEnv := (x : TermVar) → (SMTTyDenote x.ty)


/-! ## Type-checking inversion lemmas -/

private def tc_prim_inv {Γ : List TermVar} {ufs : UFCtx} {p : TermPrim} {τ : TermType}
    (h : Term.typeCheck ufs Γ (.prim p) = some τ) : τ = p.typeOf := by
  simp [Term.typeCheck] at h; exact h.symm

private def tc_var_inv {Γ : List TermVar} {ufs : UFCtx} {v : TermVar} {τ : TermType}
    (h : Term.typeCheck ufs Γ (.var v) = some τ) :
    Γ.find? (fun w => w.id == v.id) = some v ∧ v.ty = τ := by
  simp only [Term.typeCheck] at h
  split at h
  · rename_i hfind; simp only [Option.some.injEq] at h; exact ⟨hfind, h⟩
  · exact absurd h (by simp)

/-- The innermost same-named binder found by `tc_var_inv` is in fact in `Γ`. -/
private theorem tc_var_inv_mem {Γ : List TermVar} {ufs : UFCtx} {v : TermVar} {τ : TermType}
    (h : Term.typeCheck ufs Γ (.var v) = some τ) : v ∈ Γ :=
  List.mem_of_find?_eq_some (tc_var_inv h).1

private def tc_not_inv {Γ : List TermVar} {ufs : UFCtx} {t : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core .not) [t] rty) = some τ) :
    Term.typeCheck ufs Γ t = some .bool ∧ τ = .bool := by
  simp only [Term.typeCheck] at h
  revert h; cases h1 : Term.typeCheck ufs Γ t with
  | none => simp [bind, Option.bind]
  | some ty1 => simp only [bind, Option.bind]; intro h'; split at h' <;> simp_all

private def tc_boolBin_inv {Γ : List TermVar} {ufs : UFCtx} {op : Op.Core}
    {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core op) [t1, t2] rty) = some τ)
    (hop : op = .and ∨ op = .or ∨ op = .implies) :
    Term.typeCheck ufs Γ t1 = some .bool ∧ Term.typeCheck ufs Γ t2 = some .bool ∧ τ = .bool := by
  rcases hop with rfl | rfl | rfl <;> {
    simp only [Term.typeCheck] at h; revert h
    cases h1 : Term.typeCheck ufs Γ t1 with
    | none => simp [bind, Option.bind]
    | some ty1 => cases h2 : Term.typeCheck ufs Γ t2 with
      | none => simp [bind, Option.bind]
      | some ty2 => simp only [bind, Option.bind]; intro h'; split at h' <;> simp_all
  }

private def tc_eq_inv {Γ : List TermVar} {ufs : UFCtx} {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core .eq) [t1, t2] rty) = some τ) :
    Σ' τ', Term.typeCheck ufs Γ t1 = some τ' ∧ Term.typeCheck ufs Γ t2 = some τ' ∧ τ = .bool := by
  simp only [Term.typeCheck] at h; revert h
  cases h1 : Term.typeCheck ufs Γ t1 with
  | none => simp [bind, Option.bind]; exact fun h => absurd h (by trivial)
  | some ty1 => cases h2 : Term.typeCheck ufs Γ t2 with
    | none => simp [bind, Option.bind]; exact fun h => absurd h (by trivial)
    | some ty2 =>
      simp only [bind, Option.bind]; intro h'
      split at h'
      · next heq =>
        have hτ : τ = .bool := by simp at h'; exact h'.symm
        rw [Bool.and_eq_true, beq_iff_eq] at heq
        exact ⟨ty1, rfl, by rw [heq.1], hτ⟩
      · simp at h'

private def tc_ite_inv {Γ : List TermVar} {ufs : UFCtx} {c t e : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core .ite) [c, t, e] rty) = some τ) :
    Term.typeCheck ufs Γ c = some .bool ∧ Term.typeCheck ufs Γ t = some τ ∧
    Term.typeCheck ufs Γ e = some τ := by
  simp only [Term.typeCheck] at h; revert h
  cases hc : Term.typeCheck ufs Γ c with
  | none => simp [bind, Option.bind]
  | some tyc => cases ht : Term.typeCheck ufs Γ t with
    | none => simp [bind, Option.bind]
    | some tyt => cases he : Term.typeCheck ufs Γ e with
      | none => simp [bind, Option.bind]
      | some tye => simp only [bind, Option.bind]; intro h'; split at h' <;> simp_all

private def tc_intUn_inv {Γ : List TermVar} {ufs : UFCtx} {t : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.num .neg) [t] rty) = some τ) :
    Term.typeCheck ufs Γ t = some .int ∧ τ = .int := by
  simp only [Term.typeCheck] at h; revert h
  cases h1 : Term.typeCheck ufs Γ t with
  | none => simp [bind, Option.bind]
  | some ty1 => simp only [bind, Option.bind]; intro h'; split at h' <;> simp_all

private def tc_intBin_inv {Γ : List TermVar} {ufs : UFCtx} {op : Op.Num}
    {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.num op) [t1, t2] rty) = some τ)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod) :
    Term.typeCheck ufs Γ t1 = some .int ∧ Term.typeCheck ufs Γ t2 = some .int ∧ τ = .int := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> {
    simp only [Term.typeCheck] at h; revert h
    cases h1 : Term.typeCheck ufs Γ t1 with
    | none => simp [bind, Option.bind]
    | some ty1 => cases h2 : Term.typeCheck ufs Γ t2 with
      | none => simp [bind, Option.bind]
      | some ty2 => simp only [bind, Option.bind]; intro h'; split at h' <;> simp_all
  }

private def tc_intCmp_inv {Γ : List TermVar} {ufs : UFCtx} {op : Op.Num}
    {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.num op) [t1, t2] rty) = some τ)
    (hop : op = .le ∨ op = .lt ∨ op = .ge ∨ op = .gt) :
    Term.typeCheck ufs Γ t1 = some .int ∧ Term.typeCheck ufs Γ t2 = some .int ∧ τ = .bool := by
  rcases hop with rfl | rfl | rfl | rfl <;> {
    simp only [Term.typeCheck] at h; revert h
    cases h1 : Term.typeCheck ufs Γ t1 with
    | none => simp [bind, Option.bind]
    | some ty1 => cases h2 : Term.typeCheck ufs Γ t2 with
      | none => simp [bind, Option.bind]
      | some ty2 => simp only [bind, Option.bind]; intro h'; split at h' <;> simp_all
  }

private def tc_quant_inv {Γ : List TermVar} {ufs : UFCtx} {tr : List (List Term)}
    {k : Strata.SMT.QuantifierKind} {vs : List TermVar} {body : Term} {τ : TermType}
    (h : Term.typeCheck ufs Γ (.quant k vs tr body) = some τ) :
    Term.typeCheck ufs (vs.reverse ++ Γ) body = some .bool ∧ τ = .bool := by
  simp only [Term.typeCheck] at h; revert h
  cases hb : Term.typeCheck ufs (vs.reverse ++ Γ) body with
  | none => simp [bind, Option.bind]
  | some tyb => simp only [bind, Option.bind]; intro h'; split at h' <;> simp_all

/-- Inversion for `distinct` on an argument list of length ≥ 2: recovers the
    shared element type `ty` and the fact that the tail type-checks homogeneously. -/
private def tc_distinct_inv {Γ : List TermVar} {ufs : UFCtx} {t1 t2 : Term} {ts : List Term}
    {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core .distinct) (t1 :: t2 :: ts) rty) = some τ) :
    Σ' ty, Term.typeCheck ufs Γ t1 = some ty ∧
      Term.typeCheckArgs ufs Γ (t2 :: ts) (List.replicate (t2 :: ts).length ty) = true ∧
      τ = .bool := by
  simp only [Term.typeCheck] at h; revert h
  cases h1 : Term.typeCheck ufs Γ t1 with
  | none => simp [bind, Option.bind]; exact fun h => absurd h (by trivial)
  | some ty =>
    simp only [bind, Option.bind]; intro h'
    refine ⟨ty, rfl, ?_, ?_⟩ <;> (revert h'; split <;> rename_i hcheck <;> intro h' <;> simp_all)

/-- Flatten a homogeneous `HList` (every element type equal to `a`) into a plain
    list. -/
def hlistReplicateToList {α : Type} {f : α → Type} {a : α} :
    (n : Nat) → HList f (List.replicate n a) → List (f a)
  | 0, _ => []
  | _ + 1, .cons x xs => x :: hlistReplicateToList _ xs


mutual
/-- Total denotation of a type-checked SMT term.
    Defined as a mutual recursion with `denoteArgs` to avoid WF recursion
    (which breaks Lean's equation compiler for `noncomputable` defs with `cast`). -/
noncomputable def SMTTerm.denote
    {ufs : UFCtx} {Γ : List TermVar}
    (ufInterp : UFInterp) (env : SMTVarEnv)
    (tm : Term) (τ : TermType)
    (h : Term.typeCheck ufs Γ tm = some τ)
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
    cast (by rw [← heq]) (env v)
  | .app (.core (.uf uf)) args _ =>
    let sig := uf
    have htc : Term.typeCheck ufs Γ (.app (.core (.uf uf)) args _) = some τ := h
    have hargs : Term.typeCheckArgs ufs Γ args sig.args = true := by
      simp only [Term.typeCheck] at htc; split at htc <;> (try split at htc) <;> simp_all [sig]
    have hout : τ = sig.out := by
      simp only [Term.typeCheck] at htc; split at htc <;> (try split at htc) <;> simp_all [sig]
    let argVals := SMTTerm.denoteArgs ufInterp env args sig.args hargs
    cast (by rw [hout]) (applyUFDenote sig.args sig.out (ufInterp sig) argVals)
  | .app (.core .not) [t] _ =>
    let ⟨ht, heq⟩ := tc_not_inv h
    cast (by rw [heq]) (!(denote ufInterp env t .bool ht))
  | .app (.core .and) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_boolBin_inv h (.inl rfl)
    cast (by rw [heq]) ((denote ufInterp env t1 .bool h1) && (denote ufInterp env t2 .bool h2))
  | .app (.core .or) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_boolBin_inv h (.inr (.inl rfl))
    cast (by rw [heq]) ((denote ufInterp env t1 .bool h1) || (denote ufInterp env t2 .bool h2))
  | .app (.core .implies) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_boolBin_inv h (.inr (.inr rfl))
    cast (by rw [heq]) (!(denote ufInterp env t1 .bool h1) || (denote ufInterp env t2 .bool h2))
  | .app (.core .eq) [t1, t2] _ =>
    let ⟨τ', h1, h2, heq⟩ := tc_eq_inv h
    cast (by rw [heq]) (@decide (denote ufInterp env t1 τ' h1 = denote ufInterp env t2 τ' h2)
      (Classical.propDecidable _))
  | .app (.core .ite) [c, t, e] _ =>
    let ⟨hc, ht, he⟩ := tc_ite_inv h
    bif denote ufInterp env c .bool hc then denote ufInterp env t τ ht
    else denote ufInterp env e τ he
  | .app (.num .neg) [t] _ =>
    let ⟨ht, heq⟩ := tc_intUn_inv h
    cast (by rw [heq]) (-(denote ufInterp env t .int ht))
  | .app (.num .add) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_intBin_inv h (.inl rfl)
    cast (by rw [heq]) ((denote ufInterp env t1 .int h1) + (denote ufInterp env t2 .int h2))
  | .app (.num .sub) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_intBin_inv h (.inr (.inl rfl))
    cast (by rw [heq]) ((denote ufInterp env t1 .int h1) - (denote ufInterp env t2 .int h2))
  | .app (.num .mul) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_intBin_inv h (.inr (.inr (.inl rfl)))
    cast (by rw [heq]) ((denote ufInterp env t1 .int h1) * (denote ufInterp env t2 .int h2))
  | .app (.num .div) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_intBin_inv h (.inr (.inr (.inr (.inl rfl))))
    cast (by rw [heq]) ((denote ufInterp env t1 .int h1) / (denote ufInterp env t2 .int h2))
  | .app (.num .mod) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_intBin_inv h (.inr (.inr (.inr (.inr rfl))))
    cast (by rw [heq]) ((denote ufInterp env t1 .int h1) % (denote ufInterp env t2 .int h2))
  | .app (.num .le) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_intCmp_inv h (.inl rfl)
    cast (by rw [heq]) (decide ((denote ufInterp env t1 .int h1) ≤ (denote ufInterp env t2 .int h2)))
  | .app (.num .lt) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_intCmp_inv h (.inr (.inl rfl))
    cast (by rw [heq]) (decide ((denote ufInterp env t1 .int h1) < (denote ufInterp env t2 .int h2)))
  | .app (.num .ge) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_intCmp_inv h (.inr (.inr (.inl rfl)))
    cast (by rw [heq]) (decide ((denote ufInterp env t1 .int h1) ≥ (denote ufInterp env t2 .int h2)))
  | .app (.num .gt) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := tc_intCmp_inv h (.inr (.inr (.inr rfl)))
    cast (by rw [heq]) (decide ((denote ufInterp env t1 .int h1) > (denote ufInterp env t2 .int h2)))
  | .quant k vs tr body =>
    let ⟨hbody, heq⟩ := tc_quant_inv h
    let combinedEnv (ext : SMTVarEnv) : SMTVarEnv :=
      fun v =>
        if hv : v ∈ vs then ext v
        else env v
    cast (by rw [heq]) (@decide
      (match k with
       | .all => ∀ (ext : SMTVarEnv), denote ufInterp (combinedEnv ext) body .bool hbody = true
       | .exist => ∃ (ext : SMTVarEnv), denote ufInterp (combinedEnv ext) body .bool hbody = true)
      (Classical.propDecidable _))
  | .app (.core .distinct) (t1 :: t2 :: ts) _ =>
    -- Variadic (≥ 2 args): all args share `ty`; denote them into a homogeneous
    -- HList, flatten to a list, and decide pairwise distinctness.
    let ⟨ty, ht, hts, heq⟩ := tc_distinct_inv h
    let args := t1 :: t2 :: ts
    let hargs : Term.typeCheckArgs ufs Γ args (List.replicate args.length ty) = true := by
      show Term.typeCheckArgs ufs Γ (t1 :: t2 :: ts)
        (ty :: List.replicate (t2 :: ts).length ty) = true
      simp only [Term.typeCheckArgs, ht, BEq.beq, decide_eq_true_eq, hts, Bool.and_true]
    let argVals := SMTTerm.denoteArgs ufInterp env args (List.replicate args.length ty) hargs
    cast (by rw [heq]) (@decide
      ((hlistReplicateToList args.length argVals).Pairwise (· ≠ ·))
      (Classical.propDecidable _))
  | .app (.core .distinct) [] _ | .app (.core .distinct) [_] _ =>
    False.elim (by unfold Term.typeCheck at h; exact absurd h nofun)
  | .none _ => False.elim (by unfold Term.typeCheck at h; exact absurd h nofun)
  | .some _ => False.elim (by unfold Term.typeCheck at h; exact absurd h nofun)

/-- Denote a list of type-checked arguments, producing an HList of values. -/
noncomputable def SMTTerm.denoteArgs
    {ufs : UFCtx} {Γ : List TermVar}
    (ufInterp : UFInterp) (env : SMTVarEnv)
    (args : List Term) (argTys : List TermType)
    (htc : Term.typeCheckArgs ufs Γ args argTys = true)
    : HList SMTTyDenote argTys :=
  match args, argTys, htc with
  | [], [], _ => .nil
  | t :: ts, ty :: tys, htc =>
    have htc_hd : Term.typeCheck ufs Γ t = some ty := by
      simp only [Term.typeCheckArgs] at htc
      split at htc <;> simp_all [BEq.beq, decide_eq_true_eq]
    have htc_rest : Term.typeCheckArgs ufs Γ ts tys = true := by
      simp only [Term.typeCheckArgs] at htc
      split at htc <;> simp_all [BEq.beq]
    .cons (SMTTerm.denote ufInterp env t ty htc_hd)
          (denoteArgs ufInterp env ts tys htc_rest)
end


/-! ## SMT encoding of restricted LExpr -/

def baseTyToTermType : LMonoTy → Option TermType
  | .tcons "bool" [] => some .bool
  | .tcons "int" [] => some .int
  | .bitvec n => some (.bitvec n)
  | .tcons "string" [] => some .string
  | _ => none

def baseTysToTermTypes : List LMonoTy → Option (List TermType)
  | [] => some []
  | ty :: rest => do
    let smtTy ← baseTyToTermType ty
    let tys ← baseTysToTermTypes rest
    some (smtTy :: tys)



/-! ## Spine-aware SMT translation -/

/-- Build the SMT application term for an operator/free-variable `head` applied
    to `acc` (a list of **already-translated** argument terms). Non-recursive. -/
def buildAppHead (head : Expression.Expr) (acc : List Term) : Except Format Term :=
  match head with
  | .fvar () f (some ty) =>
    let (argTys, rty) := collectArrowTy ty
    match baseTyToTermType rty, baseTysToTermTypes argTys with
    | some smtRty, some smtArgTys =>
      .ok (.app (.core (.uf ⟨f.name, smtArgTys, smtRty⟩)) acc smtRty)
    | _, _ => .error f!"Cannot encode free variable type: {repr ty}"
  | .op () o (some oty) =>
    match corePredefinedOpToSMTOp (CoreOp.ofString o.name) with
    | some (builder, retTy) => .ok (builder acc retTy)
    | none =>
      -- User-defined-function fallback: encode as a UF application from the
      -- annotation `oty`, exactly like the `.fvar` head above.
      let (argTys, rty) := collectArrowTy oty
      match baseTyToTermType rty, baseTysToTermTypes argTys with
      | some smtRty, some smtArgTys =>
        .ok (.app (.core (.uf ⟨o.name, smtArgTys, smtRty⟩)) acc smtRty)
      | _, _ => .error f!"Cannot encode user-defined function type: {repr oty}"
  | _ => .error "Unsupported application head"

mutual
/-- Translate an LExpr to SMT. Applications are handled structurally: each `.app`
    node translates its argument **eagerly** and pushes the resulting `Term` into
    `appToSMTTerm`'s accumulator. Every recursive call is on a strict subterm, so
    the whole mutual block is defined by structural recursion. -/
def toSMTTerm (bvs : TermVarCtx) (e : Expression.Expr) : Except Format Term :=
  match e with
  | .const () c =>
    match c with
    | .boolConst b => .ok (.prim (.bool b))
    | .intConst i => .ok (.prim (.int i))
    | .bitvecConst _ b => .ok (.prim (.bitvec b))
    | .strConst s => .ok (.prim (.string s))
    | .realConst _ => .error "Real constants unsupported"
  | .bvar () i =>
    if h : i < bvs.length then .ok (.var bvs[i])
    else .error f!"Bound variable index out of bounds: {i}"
  | .ite () c t e_ => do
    let ct ← toSMTTerm bvs c
    let tt ← toSMTTerm bvs t
    let et ← toSMTTerm bvs e_
    .ok (Term.app (.core .ite) [ct, tt, et] (Term.typeOf tt))
  | .eq () e1 e2 => do
    let t1 ← toSMTTerm bvs e1
    let t2 ← toSMTTerm bvs e2
    .ok (Term.app (.core .eq) [t1, t2] .bool)
  | .quant () k _ (some qty) _ body => do
    let some smtTy := baseTyToTermType qty
      | .error f!"Cannot encode quantifier type: {repr qty}"
    let v : TermVar := ⟨s!"$__bv{bvs.length}", smtTy⟩
    let bodyTm ← toSMTTerm (v :: bvs) body
    let smtKind : Strata.SMT.QuantifierKind := match k with
      | .all => .all | .exist => .exist
    .ok (.quant smtKind [v] [] bodyTm)
  -- A bare free variable is a nullary application head.
  | .fvar () f (some ty) => buildAppHead (.fvar () f (some ty)) []
  -- An application: translate the argument now, then descend into the head.
  | .app () fn arg => do
    let argt ← toSMTTerm bvs arg
    appToSMTTerm bvs fn [argt]
  | _ => .error "Unsupported expression form"

/-- Translate an application head applied to `acc` (already-translated args).
    `.app` nodes are peeled structurally, translating each argument eagerly. -/
def appToSMTTerm (bvs : TermVarCtx) (head : Expression.Expr)
    (acc : List Term) : Except Format Term :=
  match head with
  | .app () fn arg => do
    let argt ← toSMTTerm bvs arg
    appToSMTTerm bvs fn (argt :: acc)
  | _ => buildAppHead head acc
termination_by structural head
end

/-! ## Main sort-correctness theorem -/

/-! ### Injectivity of the `$__bv{n}` naming scheme

Used by both the bound-variable lookup and the quantifier case. -/

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

private theorem nat_toString_inj : ∀ a b : Nat, toString a = toString b → a = b := by
  intro a b h
  have h1 : ("$__bv" ++ toString a).toList = ("$__bv" ++ toString b).toList := by
    simp [String.toList_append]; exact congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h1
  have h2 := List.append_cancel_left h1
  have hstr : toString a = toString b := String.ext_iff.mpr h2
  have hdigits : Nat.toDigits 10 a = Nat.toDigits 10 b :=
    String.ofList_injective (by rw [← Nat.toString_eq_ofList_toDigits,
      ← Nat.toString_eq_ofList_toDigits]; exact hstr)
  exact nat_toDigits_10_inj a b hdigits

private theorem bv_str_inj : ∀ a b : Nat, s!"$__bv{a}" = s!"$__bv{b}" → a = b := by
  intro a b h
  have h1 : ("$__bv" ++ toString a).toList = ("$__bv" ++ toString b).toList :=
    congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h1
  exact nat_toString_inj a b (String.ext_iff.mpr (List.append_cancel_left h1))

structure BVarCtxWF (Δ : List LMonoTy) (bvs : TermVarCtx) (ufs : UFCtx) : Prop where
  len_eq : Δ.length = bvs.length
  ty_eq : ∀ i (hi : i < Δ.length), baseTyToTermType Δ[i] = some (bvs[i]'(by omega)).ty
  id_scheme : ∀ i (hi : i < bvs.length), (bvs[i]'hi).id = s!"$__bv{bvs.length - 1 - i}"
  no_shadow : ∀ n : Nat, s!"$__bv{n}" ∉ ufs.map (·.id)

/-- Any UF-symbol id is free of capture by the bound-variable context: `bvs` ids
    all follow the `$__bv{…}` scheme (`id_scheme`), which no `ufs` id matches
    (`no_shadow`). This is what discharges the anti-shadowing side condition of
    `Term.typeCheck` on the encoder's UF applications. -/
theorem BVarCtxWF.uf_id_not_captured {Δ : List LMonoTy} {bvs : TermVarCtx} {ufs : UFCtx}
    (hbwf : BVarCtxWF Δ bvs ufs) {name : String} (h_mem : name ∈ ufs.map (·.id)) :
    name ∉ bvs.map (·.id) := by
  intro hbv
  rw [List.mem_map] at hbv
  obtain ⟨v, hv_mem, hv_id⟩ := hbv
  rw [List.mem_iff_getElem] at hv_mem
  obtain ⟨i, hi, hvi⟩ := hv_mem
  have hid := hbwf.id_scheme i hi
  rw [hvi] at hid
  -- `name = v.id = "$__bv{bvs.length - 1 - i}"`, contradicting `no_shadow`.
  rw [← hv_id, hid] at h_mem
  exact hbwf.no_shadow _ h_mem

/-- The bound-variable ids follow the position-determined `$__bv{…}` scheme, so
    they are pairwise distinct; hence looking up `bvs[i]` by its name returns
    `bvs[i]` itself (it is the unique — hence innermost — binder of that name).
    This is what the `.var` type-check rule needs on the encoder's output. -/
theorem BVarCtxWF.find?_id_self {Δ : List LMonoTy} {bvs : TermVarCtx} {ufs : UFCtx}
    (hbwf : BVarCtxWF Δ bvs ufs) (i : Nat) (hi : i < bvs.length) :
    bvs.find? (fun w => w.id == (bvs[i]'hi).id) = some (bvs[i]'hi) := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, i, hi, rfl, ?_⟩
  intro j hj
  -- `bvs[j].id = $__bv{len-1-j}` and `bvs[i].id = $__bv{len-1-i}`; distinct since
  -- `j < i` gives `len-1-j ≠ len-1-i`.
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
  intro hcontra
  have hidj := hbwf.id_scheme j (by omega)
  have hidi := hbwf.id_scheme i hi
  rw [hidj, hidi] at hcontra
  have := bv_str_inj _ _ hcontra
  omega

/-- Look up a UF signature in `ufs` by its printed name (`id`). This is the
    op-world analog of `bvs[i]` in `BVarCtxWF`: the SMT signature is read out of
    the `ufs` **data**, so its argument/return types are available as data and can
    be used to build a `cast`. -/
def lookupUF (ufs : UFCtx) (name : String) : Option UF :=
  ufs.find? (·.id == name)

theorem lookupUF_mem {ufs : UFCtx} {name : String} {uf : UF}
    (h : lookupUF ufs name = some uf) : uf ∈ ufs :=
  List.mem_of_find?_eq_some h

theorem lookupUF_id {ufs : UFCtx} {name : String} {uf : UF}
    (h : lookupUF ufs name = some uf) : uf.id = name := by
  have := List.find?_some h; simpa using this

/-- Well-formedness of a free-variable context against a UF context. Every
    declared name resolves — via `lookupUF` — to a *specific* UF whose signature
    is the SMT encoding of the fvar's collected arrow type. The signature is
    therefore available as data, mirroring how `BVarCtxWF` exposes `bvs[i].ty`.
    Uniqueness of the `Φ` names and of the `ufs` ids keeps that resolution
    unambiguous. -/
structure FVarCtxWF (Φ : FVarCtx) (ufs : UFCtx) : Prop where
  /-- Names declared in `Φ` are unique. -/
  fvar_nodup : (Φ.map (·.1)).Nodup
  /-- UF ids are unique, so `lookupUF` picks out a canonical signature. -/
  uf_nodup : (ufs.map (·.id)).Nodup
  /-- Every declared fvar resolves to a UF. -/
  fvar_resolves : ∀ (name : String) (τ : LMonoTy), (name, τ) ∈ Φ →
    (lookupUF ufs name).isSome = true
  /-- The resolved UF's argument types are the SMT encoding of the fvar's
      collected argument types. -/
  args_eq : ∀ (name : String) (τ : LMonoTy) (uf : UF), (name, τ) ∈ Φ →
    lookupUF ufs name = some uf →
    baseTysToTermTypes (collectArrowTy τ).1 = some uf.args
  /-- The resolved UF's return type is the SMT encoding of the fvar's collected
      return type. -/
  out_eq : ∀ (name : String) (τ : LMonoTy) (uf : UF), (name, τ) ∈ Φ →
    lookupUF ufs name = some uf →
    baseTyToTermType (collectArrowTy τ).2 = some uf.out

/-- Existential view of `FVarCtxWF`: recovers the encoded signature and its
    membership in `ufs` from the lookup-based fields, for consumers that only
    need "some matching UF exists". -/
theorem FVarCtxWF.fvar_has_uf {Φ : FVarCtx} {ufs : UFCtx} (hwf : FVarCtxWF Φ ufs)
    (name : String) (ty : LMonoTy) (hmem : (name, ty) ∈ Φ) :
    let (argTys, rty) := collectArrowTy ty
    ∃ smtArgTys smtRty,
      baseTysToTermTypes argTys = some smtArgTys ∧
      baseTyToTermType rty = some smtRty ∧
      (⟨name, smtArgTys, smtRty⟩ : UF) ∈ ufs := by
  obtain ⟨uf, hlk⟩ := Option.isSome_iff_exists.mp (hwf.fvar_resolves name ty hmem)
  have hargs := hwf.args_eq name ty uf hmem hlk
  have hout := hwf.out_eq name ty uf hmem hlk
  have hid : uf.id = name := lookupUF_id hlk
  have hmem_uf : uf ∈ ufs := lookupUF_mem hlk
  obtain ⟨argTys, rty, hcol⟩ : ∃ a r, collectArrowTy ty = (a, r) := ⟨_, _, rfl⟩
  rw [hcol] at hargs hout ⊢
  simp only at hargs hout ⊢
  refine ⟨uf.args, uf.out, hargs, hout, ?_⟩
  have huf_eq : (⟨name, uf.args, uf.out⟩ : UF) = uf := by rw [← hid]
  rw [huf_eq]; exact hmem_uf

/-- `typeCheckArgs` forces the argument list and the expected-type list to have
    equal length. -/
private theorem typeCheckArgs_length {ufs : UFCtx} {Γ : List TermVar}
    {smtArgs : List Term} {smtTys : List TermType}
    (h : Term.typeCheckArgs ufs Γ smtArgs smtTys = true) : smtArgs.length = smtTys.length := by
  induction smtArgs generalizing smtTys with
  | nil => cases smtTys with
    | nil => rfl
    | cons _ _ => simp [Term.typeCheckArgs] at h
  | cons t ts ih => cases smtTys with
    | nil => simp [Term.typeCheckArgs] at h
    | cons ty tys =>
      simp only [Term.typeCheckArgs] at h
      split at h
      · rename_i hty
        simp only [Bool.and_eq_true] at h
        simp only [List.length_cons, Nat.add_right_cancel_iff]
        exact ih h.2
      · exact absurd h (by simp)

/-- Inversion for a two-element expected-type list: recovers the concrete
    argument terms and their individual type-check facts. -/
private theorem typeCheckArgs_two_inv {ufs : UFCtx} {Γ : List TermVar}
    {smtArgs : List Term} {ty1 ty2 : TermType}
    (h : Term.typeCheckArgs ufs Γ smtArgs [ty1, ty2] = true) :
    ∃ t1 t2, smtArgs = [t1, t2] ∧
      Term.typeCheck ufs Γ t1 = some ty1 ∧ Term.typeCheck ufs Γ t2 = some ty2 := by
  have hlen := typeCheckArgs_length h
  match smtArgs, hlen with
  | [t1, t2], _ =>
    refine ⟨t1, t2, rfl, ?_, ?_⟩
    · simp only [Term.typeCheckArgs] at h
      split at h <;> rename_i hty <;> simp_all [BEq.beq, decide_eq_true_eq]
    · simp only [Term.typeCheckArgs] at h
      split at h <;> rename_i hty1
      · simp only [Bool.and_eq_true] at h
        obtain ⟨_, h2⟩ := h
        revert h2; split <;> rename_i hty2 <;>
          simp_all [BEq.beq, decide_eq_true_eq]
      · exact absurd h (by simp)

/-- Inversion for a one-element expected-type list. -/
private theorem typeCheckArgs_one_inv {ufs : UFCtx} {Γ : List TermVar}
    {smtArgs : List Term} {ty1 : TermType}
    (h : Term.typeCheckArgs ufs Γ smtArgs [ty1] = true) :
    ∃ t1, smtArgs = [t1] ∧ Term.typeCheck ufs Γ t1 = some ty1 := by
  have hlen := typeCheckArgs_length h
  match smtArgs, hlen with
  | [t1], _ =>
    refine ⟨t1, rfl, ?_⟩
    simp only [Term.typeCheckArgs] at h
    split at h <;> rename_i hty <;> simp_all [BEq.beq, decide_eq_true_eq]

/-- `buildAppHead` on a free-variable head produces a UF application that type-checks,
    given the SMT signature is in `ufs` and the (already-translated) args type-check. -/
private theorem buildAppHead_fvar_typeChecks
    {ufs : UFCtx} {bvs : TermVarCtx} {f : CoreLParams.Identifier} {fty : LMonoTy}
    {argTys : List LMonoTy} {rty : LMonoTy} (hcollect : collectArrowTy fty = (argTys, rty))
    {smtArgTys : List TermType} {smtRty : TermType}
    (h_smtArgTys : baseTysToTermTypes argTys = some smtArgTys)
    (h_smtRty : baseTyToTermType rty = some smtRty)
    (h_uf_mem : (⟨f.name, smtArgTys, smtRty⟩ : UF) ∈ ufs)
    (h_no_capture : f.name ∉ bvs.map (·.id))
    {sargs : List Term} {tm : Term}
    (h_tc_args : Term.typeCheckArgs ufs bvs sargs smtArgTys = true)
    (h_build : buildAppHead (.fvar () f (some fty)) sargs = .ok tm) :
    Term.typeCheck ufs bvs tm = some smtRty := by
  simp only [buildAppHead, hcollect, h_smtRty, h_smtArgTys] at h_build
  injection h_build with h_build; subst h_build
  simp only [Term.typeCheck, h_uf_mem, h_no_capture, h_tc_args,
    beq_self_eq_true, Bool.and_true, true_and, not_false_iff, if_true]

/-- `buildAppHead` on a user-defined-function `.op` head (whose symbol is NOT
    predefined) produces a UF application that type-checks — the op-world analog of
    `buildAppHead_fvar_typeChecks`. The `h_not_pre` guard forces `buildAppHead`'s
    `.op` branch into the UF fallback. -/
private theorem buildAppHead_op_typeChecks
    {ufs : UFCtx} {bvs : TermVarCtx} {o : CoreLParams.Identifier} {oty : LMonoTy}
    {argTys : List LMonoTy} {rty : LMonoTy} (hcollect : collectArrowTy oty = (argTys, rty))
    (h_not_pre : corePredefinedOpToSMTOp (CoreOp.ofString o.name) = none)
    {smtArgTys : List TermType} {smtRty : TermType}
    (h_smtArgTys : baseTysToTermTypes argTys = some smtArgTys)
    (h_smtRty : baseTyToTermType rty = some smtRty)
    (h_uf_mem : (⟨o.name, smtArgTys, smtRty⟩ : UF) ∈ ufs)
    (h_no_capture : o.name ∉ bvs.map (·.id))
    {sargs : List Term} {tm : Term}
    (h_tc_args : Term.typeCheckArgs ufs bvs sargs smtArgTys = true)
    (h_build : buildAppHead (.op () o (some oty)) sargs = .ok tm) :
    Term.typeCheck ufs bvs tm = some smtRty := by
  simp only [buildAppHead, h_not_pre, hcollect, h_smtRty, h_smtArgTys] at h_build
  injection h_build with h_build; subst h_build
  simp only [Term.typeCheck, h_uf_mem, h_no_capture, h_tc_args,
    beq_self_eq_true, Bool.and_true, true_and, not_false_iff, if_true]

/-- Every base monotype has an SMT encoding. -/
private theorem MonoTyIsBase_baseTyToTermType {τ : LMonoTy} (h : LExpr.MonoTyIsBase τ) :
    ∃ s, baseTyToTermType τ = some s := by
  cases h with
  | bool => exact ⟨.bool, by simp [baseTyToTermType]⟩
  | int => exact ⟨.int, by simp [baseTyToTermType]⟩
  | string => exact ⟨.string, by simp [baseTyToTermType]⟩
  | @bitvec n => exact ⟨.bitvec n, by simp [baseTyToTermType]⟩

-- Every `HasSimpType`-typed expression has a base return type (mutually, every
-- `AppSpine` head yields a base type). This is what lets each application argument
-- be SMT-encoded.
mutual
private theorem HasSimpType_base {Φ : FVarCtx} {Ψ : FnCtx} {Δ : List LMonoTy} {e : Expression.Expr}
    {τ : LMonoTy} (he : LExpr.HasSimpType Φ Ψ Δ e τ) : LExpr.MonoTyIsBase τ := by
  match he with
  | .const c hbase => exact hbase
  | .bvar i _ hlook hbase => exact hbase
  | .app fn arg rty hspine => exact AppSpine_base hspine
  | .fvarNullary f τ rty hspine => exact AppSpine_base hspine
  | .ite c t _ e_ hc ht hee => exact HasSimpType_base ht
  | .eq e1 e2 τ hbase he1 he2 => exact .bool
  | .quant qty qbody qk qname hbase hbody => exact .bool
private theorem AppSpine_base {Φ : FVarCtx} {Ψ : FnCtx} {Δ : List LMonoTy} {e : Expression.Expr}
    {acc : List LMonoTy} {rty : LMonoTy} (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    LExpr.MonoTyIsBase rty := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest => exact AppSpine_base hrest
  | .fvar f τ acc' rty hmem hcollect hbase => exact hbase
  | .op o oty acc' rty hop hcollect =>
    generalize CoreOp.ofString o.name = cop at hop
    cases hop <;> first | exact .int | exact .bool
  | .fnOp o oty acc' rty hmem hnpre hcollect hbase => exact hbase
termination_by structural hspine
end

/-! ## Main sort-correctness theorem (eager translator) -/

mutual
theorem toSMTTerm_typeChecks
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (huwf : FVarCtxWF Φ ufs) (hψwf : FVarCtxWF Ψ ufs)
    {Δ : List LMonoTy} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Ψ Δ e τ)
    {bvs : TermVarCtx} (hbwf : BVarCtxWF Δ bvs ufs)
    {smtTy : TermType} {tm : Term} (h_ok : toSMTTerm bvs e = .ok tm)
    (hτ : baseTyToTermType τ = some smtTy)
    : Term.typeCheck ufs bvs tm = some smtTy := by
  match he with
  | .const c hbase =>
    cases c <;>
      simp [toSMTTerm, LConst.ty, LMonoTy.int, LMonoTy.bool, LMonoTy.string,
        baseTyToTermType] at h_ok hτ ⊢ <;>
      (try subst h_ok) <;> (try subst hτ) <;>
      simp_all [Term.typeCheck, TermPrim.typeOf]
  | .bvar i _ hlook hbase =>
    unfold toSMTTerm at h_ok
    split at h_ok <;> simp at h_ok
    rename_i hi; subst h_ok
    simp only [Term.typeCheck]
    split
    · rename_i hmem
      congr 1
      have hi_Δ : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
      have hΔi_eq : Δ[i] = τ := (List.getElem?_eq_some_iff.mp hlook).2
      have hty_eq := hbwf.ty_eq i hi_Δ
      rw [hΔi_eq] at hty_eq
      rw [hτ] at hty_eq; simp at hty_eq
      exact hty_eq.symm
    · rename_i hnotmem
      exfalso; exact hnotmem (hbwf.find?_id_self i hi)
  | .app fn arg rty hspine =>
    -- The whole application is typed by the spine judgment with no pending args;
    -- `toSMTTerm (.app ..)` folds into `appToSMTTerm (.app ..) []` (empty acc).
    have h_ok' : appToSMTTerm bvs (.app () fn arg) [] = .ok tm := by
      rw [appToSMTTerm]; rw [toSMTTerm] at h_ok; exact h_ok
    exact appSpine_typeChecks huwf hψwf hspine hbwf rfl (by simp [Term.typeCheckArgs]) hτ h_ok'
  | .fvarNullary f τ_f rty hspine =>
    have h_ok' : appToSMTTerm bvs (.fvar () f (some τ_f)) [] = .ok tm := by
      rw [toSMTTerm] at h_ok; exact h_ok
    exact appSpine_typeChecks huwf hψwf hspine hbwf rfl (by simp [Term.typeCheckArgs]) hτ h_ok'
  | .ite c t _ e_ hc ht hee =>
    cases hc_ok : toSMTTerm bvs c with
    | error e =>
      have : toSMTTerm bvs (.ite () c t e_) = .error e := by
        unfold toSMTTerm; simp [hc_ok, bind, Except.bind]
      rw [this] at h_ok; exact absurd h_ok (by simp)
    | ok ct =>
      cases ht_ok : toSMTTerm bvs t with
      | error e =>
        have : toSMTTerm bvs (.ite () c t e_) = .error e := by
          unfold toSMTTerm; simp [hc_ok, ht_ok, bind, Except.bind]
        rw [this] at h_ok; exact absurd h_ok (by simp)
      | ok tt =>
        cases he_ok : toSMTTerm bvs e_ with
        | error e =>
          have : toSMTTerm bvs (.ite () c t e_) = .error e := by
            unfold toSMTTerm; simp [hc_ok, ht_ok, he_ok, bind, Except.bind]
          rw [this] at h_ok; exact absurd h_ok (by simp)
        | ok et =>
          have h_eq : toSMTTerm bvs (.ite () c t e_) =
              .ok (Term.app (.core .ite) [ct, tt, et] (Term.typeOf tt)) := by
            unfold toSMTTerm; simp [hc_ok, ht_ok, he_ok, bind, Except.bind]
          rw [h_eq] at h_ok; simp at h_ok; subst h_ok
          simp only [Term.typeCheck]
          have ihc := toSMTTerm_typeChecks (smtTy := .bool) huwf hψwf hc hbwf hc_ok
            (by simp [baseTyToTermType])
          have iht := toSMTTerm_typeChecks huwf hψwf ht hbwf ht_ok hτ
          have ihe := toSMTTerm_typeChecks huwf hψwf hee hbwf he_ok hτ
          -- The ite annotation is `Term.typeOf tt`; the checker now requires it to
          -- equal the then-branch type, which the typeOf/typeCheck agreement supplies.
          have htt : Term.typeOf tt = smtTy := Term.typeOf_of_typeCheck iht
          rw [ihc, iht, ihe, htt]; simp
  | .eq e1 e2 τ' hbase he1 he2 =>
    cases h1_ok : toSMTTerm bvs e1 with
    | error e =>
      have : toSMTTerm bvs (.eq () e1 e2) = .error e := by
        unfold toSMTTerm; simp [h1_ok, bind, Except.bind]
      rw [this] at h_ok; exact absurd h_ok (by simp)
    | ok t1 =>
      cases h2_ok : toSMTTerm bvs e2 with
      | error e =>
        have : toSMTTerm bvs (.eq () e1 e2) = .error e := by
          unfold toSMTTerm; simp [h1_ok, h2_ok, bind, Except.bind]
        rw [this] at h_ok; exact absurd h_ok (by simp)
      | ok t2 =>
        have h_eq : toSMTTerm bvs (.eq () e1 e2) =
            .ok (Term.app (.core .eq) [t1, t2] .bool) := by
          unfold toSMTTerm; simp [h1_ok, h2_ok, bind, Except.bind]
        rw [h_eq] at h_ok; simp at h_ok; subst h_ok
        have hτ_bool : smtTy = .bool := by
          simp [baseTyToTermType] at hτ; exact hτ.symm
        subst hτ_bool
        have key1 : ∀ sty, baseTyToTermType τ' = some sty →
            Term.typeCheck ufs bvs t1 = some sty :=
          fun _ h => toSMTTerm_typeChecks huwf hψwf he1 hbwf h1_ok h
        have key2 : ∀ sty, baseTyToTermType τ' = some sty →
            Term.typeCheck ufs bvs t2 = some sty :=
          fun _ h => toSMTTerm_typeChecks huwf hψwf he2 hbwf h2_ok h
        simp only [Term.typeCheck]
        cases hbase with
        | bool => rw [key1 .bool (by simp [baseTyToTermType]), key2 .bool (by simp [baseTyToTermType])]; simp
        | int => rw [key1 .int (by simp [baseTyToTermType]), key2 .int (by simp [baseTyToTermType])]; simp
        | string =>
          rw [key1 .string (by simp [baseTyToTermType]), key2 .string (by simp [baseTyToTermType])]; simp
        | bitvec =>
          rename_i n
          rw [key1 (.bitvec n) (by simp [baseTyToTermType]), key2 (.bitvec n) (by simp [baseTyToTermType])]
          simp
  | .quant qty qbody qk qname hbase hbody =>
    have hτ_bool : smtTy = .bool := by
      simp [baseTyToTermType] at hτ; exact hτ.symm
    subst hτ_bool
    have hqty : ∃ smtQTy, baseTyToTermType qty = some smtQTy := by
      cases hbase with
      | bool => exact ⟨.bool, by simp [baseTyToTermType]⟩
      | int => exact ⟨.int, by simp [baseTyToTermType]⟩
      | string => exact ⟨.string, by simp [baseTyToTermType]⟩
      | @bitvec n => exact ⟨.bitvec n, by simp [baseTyToTermType]⟩
    obtain ⟨smtQTy, hqty_eq⟩ := hqty
    unfold toSMTTerm at h_ok
    simp only [hqty_eq, bind, Except.bind] at h_ok
    have hstr : toString "$__bv" = "$__bv" := rfl
    have hstr2 : ∀ n : Nat, toString n = Nat.repr n := fun _ => rfl
    revert h_ok
    cases hbody_ok : toSMTTerm (⟨"$__bv" ++ (bvs.length).repr, smtQTy⟩ :: bvs) qbody with
    | error e => simp
    | ok bodyTm =>
      simp
      intro h_ok; subst h_ok
      simp only [Term.typeCheck]
      have hbwf' : BVarCtxWF (qty :: Δ)
          (⟨"$__bv" ++ (bvs.length).repr, smtQTy⟩ :: bvs) ufs := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [hbwf.len_eq]
        · intro i hi
          cases i with
          | zero => simp [hqty_eq]
          | succ j =>
            simp only [List.length_cons] at hi
            simp only [List.getElem_cons_succ]
            exact hbwf.ty_eq j (by omega)
        · intro i hi
          cases i with
          | zero =>
            simp only [List.getElem_cons_zero, List.length_cons, hstr, hstr2]
            congr 1
          | succ j =>
            simp only [List.getElem_cons_succ, List.length_cons] at hi ⊢
            have hj : j < bvs.length := by omega
            have hid := hbwf.id_scheme j hj
            rw [hid]; simp only [hstr, hstr2]
            have : bvs.length + 1 - 1 - (j + 1) = bvs.length - 1 - j := by omega
            rw [this]
        · intro n
          have := hbwf.no_shadow n
          simp only [hstr, hstr2] at this
          exact this
      have ihbody := toSMTTerm_typeChecks (smtTy := .bool) huwf hψwf hbody hbwf'
        hbody_ok (by simp [baseTyToTermType])
      simp only [hstr, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append]
      rw [ihbody]; simp
  termination_by structural he

/-- Spine correctness. If `AppSpine Φ Ψ Δ e acc rty` and the already-translated
    accumulator `accTms` type-checks against the SMT encoding `accSmt` of `acc`,
    then `appToSMTTerm bvs e accTms` produces a term of sort `smtRty`.

    Structural on the `AppSpine` derivation — its `app` constructor recurses on the
    function position exactly as `appToSMTTerm` does, so the invariant about the
    accumulator threads through. -/
theorem appSpine_typeChecks
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (huwf : FVarCtxWF Φ ufs) (hψwf : FVarCtxWF Ψ ufs)
    {Δ : List LMonoTy} {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty)
    {bvs : TermVarCtx} (hbwf : BVarCtxWF Δ bvs ufs)
    {accSmt : List TermType} (hacc : baseTysToTermTypes acc = some accSmt)
    {accTms : List Term} (h_acc_tc : Term.typeCheckArgs ufs bvs accTms accSmt = true)
    {smtRty : TermType} (hrty : baseTyToTermType rty = some smtRty)
    {tm : Term} (h_ok : appToSMTTerm bvs e accTms = .ok tm)
    : Term.typeCheck ufs bvs tm = some smtRty := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    -- appToSMTTerm on `.app fn arg`: translate `arg`, recurse on `fn` with it prepended.
    rw [appToSMTTerm] at h_ok
    cases h_arg_ok : toSMTTerm bvs arg with
    | error e => rw [h_arg_ok] at h_ok; simp [bind, Except.bind] at h_ok
    | ok argt =>
      rw [h_arg_ok] at h_ok; simp only [bind, Except.bind] at h_ok
      -- The argument's type is base (it is a `HasSimpType` output), so it encodes;
      -- prepending it to the accumulator preserves the args-typecheck invariant.
      obtain ⟨saty, h_saty⟩ := MonoTyIsBase_baseTyToTermType (HasSimpType_base harg)
      have h_argt := toSMTTerm_typeChecks huwf hψwf harg hbwf h_arg_ok h_saty
      have hacc' : baseTysToTermTypes (aty :: acc') = some (saty :: accSmt) := by
        simp only [baseTysToTermTypes, h_saty, hacc, bind, Option.bind]
      have h_acc_tc' : Term.typeCheckArgs ufs bvs (argt :: accTms) (saty :: accSmt) = true := by
        simp only [Term.typeCheckArgs, h_argt]
        simp [h_acc_tc, BEq.beq]
      exact appSpine_typeChecks huwf hψwf hrest hbwf hacc' h_acc_tc' hrty h_ok
  | .fvar f τ acc' rty hmem hcollect hbase =>
    -- Nullary/saturated fvar head: buildAppHead builds the UF application.
    have huwf_info := huwf.fvar_has_uf f.name τ hmem
    rw [hcollect] at huwf_info
    obtain ⟨smtArgTys, smtRty', h_smtArgTys, h_smtRty', h_uf_mem⟩ := huwf_info
    -- accSmt = smtArgTys since both encode acc'; and smtRty = smtRty'.
    rw [h_smtArgTys] at hacc; injection hacc with hacc; subst hacc
    rw [h_smtRty'] at hrty; injection hrty with hrty; subst hrty
    have h_ok' : buildAppHead (.fvar () f (some τ)) accTms = .ok tm := by
      rw [← h_ok, appToSMTTerm]; intro fn arg h; nomatch h
    have h_no_capture : f.name ∉ bvs.map (·.id) :=
      hbwf.uf_id_not_captured (List.mem_map_of_mem h_uf_mem)
    exact buildAppHead_fvar_typeChecks hcollect h_smtArgTys h_smtRty' h_uf_mem
      h_no_capture h_acc_tc h_ok'
  | .fnOp o oty acc' rty hmem hnpre hcollect hbase =>
    -- User-defined-function head: identical to the `.fvar` head, but resolving the
    -- signature out of `ufs` via `Ψ`'s well-formedness (`hψwf`) and building the
    -- UF application through `buildAppHead`'s `.op`-fallback branch.
    have hψwf_info := hψwf.fvar_has_uf o.name oty hmem
    rw [hcollect] at hψwf_info
    obtain ⟨smtArgTys, smtRty', h_smtArgTys, h_smtRty', h_uf_mem⟩ := hψwf_info
    -- accSmt = smtArgTys since both encode acc'; and smtRty = smtRty'.
    rw [h_smtArgTys] at hacc; injection hacc with hacc; subst hacc
    rw [h_smtRty'] at hrty; injection hrty with hrty; subst hrty
    have h_ok' : buildAppHead (.op () o (some oty)) accTms = .ok tm := by
      rw [← h_ok, appToSMTTerm]; intro fn arg h; nomatch h
    have h_no_capture : o.name ∉ bvs.map (·.id) :=
      hbwf.uf_id_not_captured (List.mem_map_of_mem h_uf_mem)
    exact buildAppHead_op_typeChecks hcollect hnpre h_smtArgTys h_smtRty' h_uf_mem
      h_no_capture h_acc_tc h_ok'
  | .op o oty acc' rty hop hcollect =>
    -- Operator head: `buildAppHead (.op ..) accTms = builder accTms retTy`.
    have h_ok : buildAppHead (.op () o (some oty)) accTms = .ok tm := by
      rw [← h_ok, appToSMTTerm]; intro fn arg h; nomatch h
    generalize hcop : CoreOp.ofString o.name = cop at hop
    cases hop
    case intNeg | boolNot =>
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      obtain ⟨t1, hst, h1⟩ := typeCheckArgs_one_inv h_acc_tc; subst hst
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok
      injection h_ok with h_ok; subst h_ok
      simp [Term.typeCheck, h1]
    case intAdd | intSub | intMul | intDiv | intSafeDiv | intMod | intSafeMod
       | intDivT | intSafeDivT | intModT | intSafeModT | intLt | intLe | intGt
       | intGe | boolAnd | boolOr | boolImplies | boolEquiv =>
        simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
        injection hacc with hacc; subst hacc
        obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
        simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
        simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok
        injection h_ok with h_ok; subst h_ok
        simp [Term.typeCheck, h1, h2]
  termination_by structural hspine
end

/-! ## Bridge: `HasSimpType` → `HasTypeA` (needed for `simpDenote`) -/

/-- `collectArrowTy` inverts `List.foldr LMonoTy.arrow`: if it returns `(args, ret)` then
    the original type equals the right-nested arrow `args → ret`. -/
private theorem collectArrowTy_foldr (τ : LMonoTy) :
    let (args, ret) := collectArrowTy τ
    τ = List.foldr LMonoTy.arrow ret args := by
  fun_induction collectArrowTy τ with
  | case1 ty1 ty2 atys rty hc ih =>
    rw [hc] at ih
    simp only at ih
    simp only [List.foldr, LMonoTy.arrow]
    rw [← ih]
  | _ => rfl

mutual
theorem HasSimpType_implies_HasTypeA {Φ : FVarCtx} {Ψ : FnCtx} {Δ : List LMonoTy}
    {e : Expression.Expr} {τ : LMonoTy}
    (h : LExpr.HasSimpType Φ Ψ Δ e τ) : LExpr.HasTypeA Δ e τ := by
  match h with
  | .const c hbase => exact .const
  | .bvar i _ hlook hbase => exact .bvar hlook
  | .app fn arg rty hspine => exact AppSpine_implies_HasTypeA hspine
  | .fvarNullary f _ rty hspine => exact AppSpine_implies_HasTypeA hspine
  | .ite c t _ e_ hc ht hee =>
    exact .ite (HasSimpType_implies_HasTypeA hc) (HasSimpType_implies_HasTypeA ht)
      (HasSimpType_implies_HasTypeA hee)
  | .eq e1 e2 _ hbase he1 he2 =>
    exact .eq (HasSimpType_implies_HasTypeA he1) (HasSimpType_implies_HasTypeA he2)
  | .quant qty qbody qk qname hbase hbody =>
    exact .quant (by exact .const) (HasSimpType_implies_HasTypeA hbody)

theorem AppSpine_implies_HasTypeA {Φ : FVarCtx} {Ψ : FnCtx} {Δ : List LMonoTy}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    LExpr.HasTypeA Δ e (List.foldr LMonoTy.arrow rty acc) := by
  match hspine with
  | .app fn arg aty acc' rty' harg hrest =>
    have h_fn := AppSpine_implies_HasTypeA hrest
    have h_arg := HasSimpType_implies_HasTypeA harg
    -- fn : foldr arrow rty' (aty :: acc') = .tcons "arrow" [aty, foldr arrow rty' acc']
    -- arg : aty → result: foldr arrow rty' acc'
    exact .app h_fn h_arg
  | .fvar f τ acc' rty' hmem hcollect hbase =>
    -- `collectArrowTy τ = (acc', rty')` implies `τ = foldr arrow rty' acc'`
    have h_eq : τ = List.foldr LMonoTy.arrow rty' acc' := by
      have := collectArrowTy_foldr τ; rw [hcollect] at this; exact this
    exact h_eq ▸ .fvar
  | .op o oty acc' rty' hop hcollect =>
    have h_eq : oty = List.foldr LMonoTy.arrow rty' acc' := by
      have := collectArrowTy_foldr oty; rw [hcollect] at this; exact this
    exact h_eq ▸ .op
  | .fnOp o oty acc' rty' hmem hnpre hcollect hbase =>
    -- The node IS `.op`, so `HasTypeA` types it via `.op` at the annotation `oty`;
    -- rewrite `oty = foldr arrow rty' acc'` exactly as the predefined `.op` arm.
    have h_eq : oty = List.foldr LMonoTy.arrow rty' acc' := by
      have := collectArrowTy_foldr oty; rw [hcollect] at this; exact this
    exact h_eq ▸ .op
termination_by structural hspine
end

/-! ## Semantic soundness infrastructure -/

/-- The LExpr-side `TyDenote` and the SMT-side `SMTTyDenote` agree on base types. -/
theorem tyDenote_eq_smtTyDenote {τ : LMonoTy} {smtTy : TermType}
    (hbase : LExpr.MonoTyIsBase τ) (h : baseTyToTermType τ = some smtTy) :
    Lambda.TyDenote simpTcInterp simpTyVarVal τ = SMTTyDenote smtTy := by
  cases hbase with
  | bool => simp [baseTyToTermType] at h; subst h; rfl
  | int => simp [baseTyToTermType] at h; subst h; rfl
  | string => simp [baseTyToTermType] at h; subst h; rfl
  | bitvec => simp [baseTyToTermType] at h; subst h; rfl

/-- Consistency of the operator interpretation with SMT semantics.
    Each primitive Core operator, when applied in the `simpDenote` world, computes
    the same function as the corresponding SMT operator node's `SMTTerm.denote`. -/
structure OpInterpConsistent (opInterp : Lambda.OpInterp simpTcInterp) : Prop where
  neg : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Neg⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "int" []])
        = (fun x : Int => -x)
  not : ∀ name, CoreOp.ofString name = .bool .Not →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "bool" []])
        = (fun x : Bool => !x)
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

/-- Correspondence between LExpr bound variable environment and SMT variable environment.
    For each position `i` in the typing context `Δ`, the LExpr-side value (via `bvarVal`)
    equals (under cast) the SMT-side value (via `smtEnv`) at the bound variable `bvs[i]`. -/
def BVarEnvCorresponds
    {Δ : List LMonoTy} {bvs : TermVarCtx} {ufs : UFCtx}
    (hwf : BVarCtxWF Δ bvs ufs)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (smtEnv : SMTVarEnv) : Prop :=
  ∀ i (τ : LMonoTy) (hbase : LExpr.MonoTyIsBase τ) (hlook : Δ[i]? = some τ),
    let hi : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
    let hbvs : i < bvs.length := hwf.len_eq ▸ hi
    let hty : baseTyToTermType τ = some (bvs[i]'hbvs).ty := by
      have := hwf.ty_eq i hi
      rw [(List.getElem?_eq_some_iff.mp hlook).2] at this
      exact this
    cast (tyDenote_eq_smtTyDenote hbase hty) (bvarVal.get i hlook)
      = smtEnv (bvs[i]'hbvs)

/-- Extension lemma for `BVarEnvCorresponds`: extending both the LExpr bound-var
    valuation (with a fresh value `x`) and the SMT environment (agreeing with `x`
    on the new variable `v` and with the old env elsewhere) preserves the
    correspondence. Because `v` follows the `$__bv{bvs.length}` scheme it never
    collides with an existing `bvs` entry, so the "elsewhere" clause is total. -/
theorem BVarEnvCorresponds_cons
    {Δ : List LMonoTy} {bvs : TermVarCtx} {ufs : UFCtx}
    {hbwf : BVarCtxWF Δ bvs ufs}
    {bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ}
    {smtEnv : SMTVarEnv}
    (henv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    {qty : LMonoTy} {v : TermVar}
    (hbase : LExpr.MonoTyIsBase qty)
    (hty : baseTyToTermType qty = some v.ty)
    (x : Lambda.TyDenote simpTcInterp simpTyVarVal qty)
    {smtEnv' : SMTVarEnv}
    (hnew : smtEnv' v = cast (tyDenote_eq_smtTyDenote hbase hty) x)
    (hold : ∀ w, w ≠ v → smtEnv' w = smtEnv w)
    (hbwf' : BVarCtxWF (qty :: Δ) (v :: bvs) ufs)
    : BVarEnvCorresponds hbwf' (.cons x bvarVal) smtEnv' := by
  intro i τ hbase_i hlook
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook
    subst hlook
    simp only [HList.get_cons_zero, List.getElem_cons_zero]
    rw [hnew]
  | succ j =>
    simp only [List.getElem?_cons_succ] at hlook
    have hj_lt : j < bvs.length := by
      have := (List.getElem?_eq_some_iff.mp hlook).1; rw [hbwf.len_eq] at this; exact this
    have henv_j := henv j τ hbase_i hlook
    simp only [HList.get_cons_succ, List.getElem_cons_succ]
    have hvne : (bvs[j]'hj_lt) ≠ v := by
      intro hcontra
      have hid := hbwf.id_scheme j hj_lt
      -- `v.id` is `$__bv{bvs.length + ...}` — matching `id_scheme` for `v :: bvs` at 0.
      have hvid0 := hbwf'.id_scheme 0 (by simp)
      simp only [List.getElem_cons_zero, List.length_cons] at hvid0
      rw [← hcontra] at hvid0
      rw [hid] at hvid0
      have := bv_str_inj _ _ hvid0
      omega
    rw [hold _ hvne]
    exact henv_j

/-- If `baseTyToTermType` returns `some`, the type is base. -/
private theorem baseTyToTermType_isBase {τ : LMonoTy} {sty : TermType}
    (h : baseTyToTermType τ = some sty) : LExpr.MonoTyIsBase τ := by
  cases τ with
  | tcons name args =>
    simp [baseTyToTermType] at h
    split at h <;> simp_all
    all_goals (first | exact .bool | exact .int | exact .string)
  | bitvec n => exact .bitvec
  | _ => simp [baseTyToTermType] at h

/-- The LExpr-side denotation of a right-nested arrow type `foldr arrow rty acc`
    (under `simpTcInterp`/`simpTyVarVal`) equals the SMT-side `UFDenote'` at
    the corresponding SMT types. This is the curried-function-level analog of
    `tyDenote_eq_smtTyDenote` (which handles base types). -/
private theorem tyDenote_arrow_eq_UFDenote'
    {acc : List LMonoTy} {accSmt : List TermType} {rty : LMonoTy} {smtRty : TermType}
    (hacc : baseTysToTermTypes acc = some accSmt)
    (hrty : baseTyToTermType rty = some smtRty) :
    Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow rty acc)
      = UFDenote' accSmt smtRty := by
  induction acc generalizing accSmt with
  | nil =>
    simp [baseTysToTermTypes] at hacc; subst hacc
    simp [UFDenote', List.foldr]
    exact tyDenote_eq_smtTyDenote (baseTyToTermType_isBase hrty) hrty
  | cons aty rest ih =>
    simp only [baseTysToTermTypes, bind, Option.bind] at hacc
    cases haty : baseTyToTermType aty with
    | none => rw [haty] at hacc; exact absurd hacc (by simp)
    | some smtAty =>
      rw [haty] at hacc; simp only at hacc
      cases hrest : baseTysToTermTypes rest with
      | none => rw [hrest] at hacc; exact absurd hacc (by simp)
      | some smtRest =>
        rw [hrest] at hacc; simp only [Option.some.injEq] at hacc
        subst hacc
        simp only [List.foldr, UFDenote']
        -- TyDenote ... (arrow aty (foldr arrow rty rest))
        --   = SortDenote simpTcInterp (substTyVars simpTyVarVal (arrow aty ...))
        --   = SortDenote simpTcInterp (arrow ...) → SortDenote simpTcInterp (...)
        --   = SMTTyDenote smtAty → UFDenote' smtRest smtRty
        -- `TyDenote` on an arrow splits into a function type (definitional).
        have harrow : Lambda.TyDenote simpTcInterp simpTyVarVal
              (LMonoTy.arrow aty (List.foldr LMonoTy.arrow rty rest))
            = (Lambda.TyDenote simpTcInterp simpTyVarVal aty →
               Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow rty rest)) := rfl
        -- The argument type: base, so `TyDenote = SMTTyDenote`.
        have h_aty : Lambda.TyDenote simpTcInterp simpTyVarVal aty = SMTTyDenote smtAty :=
          tyDenote_eq_smtTyDenote (baseTyToTermType_isBase haty) haty
        -- The tail: by IH on `rest`.
        have h_rest : Lambda.TyDenote simpTcInterp simpTyVarVal
              (List.foldr LMonoTy.arrow rty rest) = UFDenote' smtRest smtRty := ih hrest
        rw [harrow, h_aty, h_rest]

/-- Correspondence between LExpr free variable valuation and n-ary UF interpretation.
    For each free variable `(name, τ)` declared in `Φ`, the LExpr-side curried denotation
    (via `fvarVal`) equals (under cast) the SMT-side curried UF denotation (via `ufInterp`).

    The LExpr side denotes a free variable of arrow type `τ = a₁ → a₂ → ⋯ → aₙ → rty`
    as `fvarVal ⟨name, ()⟩ (τ.substTyVars simpTyVarVal)`, which has Lean type
    `SortDenote simpTcInterp (τ.substTyVars simpTyVarVal)` ≅ `SMTTyDenote sty₁ → ⋯ → SMTTyDenote rty`.

    The SMT side denotes it as `ufInterp ⟨name, smtArgTys, smtRty⟩`, which has type
    `UFDenote' smtArgTys smtRty` = `SMTTyDenote sty₁ → ⋯ → SMTTyDenote smtRty`.

    These coincide under `tyDenote_eq_smtTyDenote` on each base constituent. -/
def UFEnvCorresponds
    {Φ : FVarCtx} {ufs : UFCtx}
    (hwf : FVarCtxWF Φ ufs)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (ufInterp : UFInterp) : Prop :=
  ∀ (name : String) (τ : LMonoTy) (hmem : (name, τ) ∈ Φ),
    -- `lookupUF` reads the declared signature out of `ufs` as **data**, exactly as
    -- `BVarEnvCorresponds` reads `bvs[i]` out of the bound-variable context.
    -- `FVarCtxWF`'s `args_eq`/`out_eq` give the encoding equalities directly, which
    -- feed `tyDenote_arrow_eq_UFDenote'` for the cast.
    let uf : UF := (lookupUF ufs name).get (hwf.fvar_resolves name τ hmem)
    let hlk : lookupUF ufs name = some uf := (Option.some_get _).symm
    cast (by
          have hargs := hwf.args_eq name τ uf hmem hlk
          have hout := hwf.out_eq name τ uf hmem hlk
          have h1 : τ = List.foldr LMonoTy.arrow (collectArrowTy τ).2 (collectArrowTy τ).1 := by
            have hf := collectArrowTy_foldr τ
            obtain ⟨argTys, rty, hcol⟩ : ∃ a r, collectArrowTy τ = (a, r) := ⟨_, _, rfl⟩
            rw [hcol] at hf ⊢; exact hf
          rw [h1]; exact tyDenote_arrow_eq_UFDenote' hargs hout)
         (fvarVal ⟨name, ()⟩ (τ.substTyVars simpTyVarVal))
      = ufInterp uf

/-- Correspondence between the LExpr operator interpretation and the n-ary UF
    interpretation, for user-defined-function `.op` heads. The analog of
    `UFEnvCorresponds`, except that the LExpr side denotes through `opInterp` (an `.op`
    node denotes as `opInterp o.name (ty.substTyVars vt)`) rather than through `fvarVal`.
    It ranges over `Ψ : FnCtx`; because `FnCtx` and `FVarCtx` are the same type and the
    well-formedness conditions are identical, it reuses the `FVarCtxWF` structure applied
    to `Ψ`. For opaque functions this is a hypothesis, exactly like `UFEnvCorresponds`. -/
def OpEnvCorresponds
    {Ψ : FnCtx} {ufs : UFCtx}
    (hwf : FVarCtxWF Ψ ufs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (ufInterp : UFInterp) : Prop :=
  ∀ (name : String) (τ : LMonoTy) (hmem : (name, τ) ∈ Ψ),
    -- `lookupUF` reads the declared signature out of `ufs` as **data**, exactly as in
    -- `UFEnvCorresponds`. The only difference is the LExpr-side valuation used: an
    -- `.op` node denotes through `opInterp` (keyed on the bare name string), not
    -- through `fvarVal`.
    let uf : UF := (lookupUF ufs name).get (hwf.fvar_resolves name τ hmem)
    let hlk : lookupUF ufs name = some uf := (Option.some_get _).symm
    cast (by
          have hargs := hwf.args_eq name τ uf hmem hlk
          have hout := hwf.out_eq name τ uf hmem hlk
          have h1 : τ = List.foldr LMonoTy.arrow (collectArrowTy τ).2 (collectArrowTy τ).1 := by
            have hf := collectArrowTy_foldr τ
            obtain ⟨argTys, rty, hcol⟩ : ∃ a r, collectArrowTy τ = (a, r) := ⟨_, _, rfl⟩
            rw [hcol] at hf ⊢; exact hf
          rw [h1]; exact tyDenote_arrow_eq_UFDenote' hargs hout)
         (opInterp name (τ.substTyVars simpTyVarVal))
      = ufInterp uf

/-! ## Soundness helper lemmas (cast/HEq plumbing) -/

/-- Transport of an `Eq.mpr`/`▸` under a family. -/
private theorem subst_heq {α : Sort u} {P : α → Sort v} {a b : α}
    (h : a = b) (x : P b) : HEq (h ▸ x) x := by subst h; exact HEq.rfl

/-- The `choose` from `MonoTyIsBase_baseTyToTermType` gives back the same `smtTy`
    that `baseTyToTermType` computes. -/
private theorem choose_eq_of_hτ {τ : LMonoTy} {smtTy : TermType}
    (hbase : LExpr.MonoTyIsBase τ) (hτ : baseTyToTermType τ = some smtTy) :
    (MonoTyIsBase_baseTyToTermType hbase).choose = smtTy := by
  have h := (MonoTyIsBase_baseTyToTermType hbase).choose_spec
  rw [h] at hτ; exact Option.some.inj hτ

/-- Convert an IH with opaque `choose` smtTy to one with an explicit `smtTy`. -/
private theorem ih_convert_smtTy {Γ : List TermVar} {ufs : UFCtx}
    {ufInterp : UFInterp} {env : SMTVarEnv}
    {tm : Term} {smtTy1 smtTy2 : TermType}
    (h_eq : smtTy1 = smtTy2)
    {x : SMTTyDenote smtTy1} {htc1 : Term.typeCheck ufs Γ tm = some smtTy1}
    (ih : x = SMTTerm.denote ufInterp env tm smtTy1 htc1)
    : HEq x (SMTTerm.denote ufInterp env tm smtTy2 (h_eq ▸ htc1)) := by
  subst h_eq; exact heq_of_eq ih

/-- A cast-wrapped `bif` corresponds to a `bif` when conditions and branches
    match (up to HEq on the branches). -/
private theorem bif_heq_of_cond_branches {α β : Type} {b1 : Bool} {b2 : Bool}
    {t1 e1 : α} {t2 e2 : β} (h_ty : α = β)
    (hb : b1 = b2) (ht : HEq t1 t2) (he : HEq e1 e2) :
    cast h_ty (bif b1 then t1 else e1) = (bif b2 then t2 else e2) := by
  subst h_ty; subst hb; cases ht; cases he; cases b1 <;> rfl

/-- Injectivity of `cast` on a single fixed type equality. -/
private theorem cast_inj_of_eq {α β : Type} (h : α = β) (a b : α)
    (hcast : cast h a = cast h b) : a = b := by cases h; exact hcast

/-- Casting a function and its argument along matching type equalities commutes
    with application: `(cast f) (cast x) = cast (f x)`. Used to peel one argument
    off a curried denotation in the application-spine step. -/
private theorem cast_arrow_app {A A' B B' : Type} (hA : A = A') (hB : B = B')
    (hAB : (A → B) = (A' → B')) (f : A → B) (x : A) :
    (cast hAB f) (cast hA x) = cast hB (f x) := by
  subst hA; subst hB; rfl

/-- `SMTTerm.denote` for a variable is HEq to the environment lookup. -/
private theorem SMTTerm_denote_var_heq {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp) (env : SMTVarEnv)
    (v : TermVar) (τ : TermType) (htc : Term.typeCheck ufs Γ (.var v) = some τ) :
    HEq (SMTTerm.denote ufInterp env (.var v) τ htc) (env v) := by
  unfold SMTTerm.denote
  obtain ⟨hmem, heq⟩ := tc_var_inv htc
  simp only
  exact cast_heq _ _

/-- Unfolding lemma for `SMTTerm.denote` on `ite`. -/
private noncomputable def SMTTerm_denote_ite {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp) (env : SMTVarEnv)
    (c t e : Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck ufs Γ (.app (.core .ite) [c, t, e] rty) = some τ) :
    SMTTerm.denote ufInterp env (.app (.core .ite) [c, t, e] rty) τ htc =
      bif SMTTerm.denote ufInterp env c .bool (tc_ite_inv htc).1
      then SMTTerm.denote ufInterp env t τ (tc_ite_inv htc).2.1
      else SMTTerm.denote ufInterp env e τ (tc_ite_inv htc).2.2 := by
  simp only [SMTTerm.denote]
  obtain ⟨hc, ht, he⟩ := tc_ite_inv htc
  rfl

/-- Unfolding lemma for `SMTTerm.denote` on `eq`. -/
private noncomputable def SMTTerm_denote_eq_unfold {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp) (env : SMTVarEnv)
    (t1 t2 : Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck ufs Γ (.app (.core .eq) [t1, t2] rty) = some τ) :
    SMTTerm.denote ufInterp env (.app (.core .eq) [t1, t2] rty) τ htc =
      cast (by rw [(tc_eq_inv htc).2.2.2]) (@decide
        (SMTTerm.denote ufInterp env t1 (tc_eq_inv htc).1 (tc_eq_inv htc).2.1
         = SMTTerm.denote ufInterp env t2 (tc_eq_inv htc).1 (tc_eq_inv htc).2.2.1)
        (Classical.propDecidable _)) := by
  simp only [SMTTerm.denote]
  obtain ⟨τ', h1, h2, heq⟩ := tc_eq_inv htc
  rfl

/-- Inversion for a UF application: recovers the type-check facts for the
    argument list and the output type. -/
private theorem tc_uf_inv {Γ : List TermVar} {ufs : UFCtx} {uf : UF}
    {args : List Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core (.uf uf)) args rty) = some τ) :
    Term.typeCheckArgs ufs Γ args uf.args = true ∧ τ = uf.out := by
  simp only [Term.typeCheck] at h
  split at h <;> (try split at h) <;> simp_all

/-- `SMTTerm.denote` is invariant (up to `HEq`) under a change of the type index
    when the two indices are provably equal. -/
private theorem SMTTerm_denote_cast {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp) (env : SMTVarEnv)
    (tm : Term) (τ τ' : TermType)
    (h : Term.typeCheck ufs Γ tm = some τ) (h' : Term.typeCheck ufs Γ tm = some τ')
    (heq : τ = τ') :
    HEq (SMTTerm.denote ufInterp env tm τ h) (SMTTerm.denote ufInterp env tm τ' h') := by
  subst heq; exact heq_of_eq (congrArg (SMTTerm.denote ufInterp env tm τ) (proof_irrel h h'))

/-- Unfolding lemma for `SMTTerm.denote` on a UF application, exposing the
    `applyUFDenote` of the head interpretation to the denoted arguments. -/
private noncomputable def SMTTerm_denote_uf_unfold {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp) (env : SMTVarEnv)
    (uf : UF) (args : List Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck ufs Γ (.app (.core (.uf uf)) args rty) = some τ) :
    SMTTerm.denote ufInterp env (.app (.core (.uf uf)) args rty) τ htc =
      cast (by rw [(tc_uf_inv htc).2])
        (applyUFDenote uf.args uf.out (ufInterp uf)
          (SMTTerm.denoteArgs ufInterp env args uf.args (tc_uf_inv htc).1)) := by
  simp only [SMTTerm.denote]

/-- LHS reduction for a **unary** operator head: the LExpr op interpretation,
    cast to `UFDenote' [sa] sr` and applied to one argument value, reduces to the
    semantic function `g` applied to that value — given the op-interpretation
    consistency equation. Encapsulates the `simpDenote`/`denote_op` unfolding and
    the `cast`/`subst`/`HEq` plumbing shared by every unary op arm. -/
private theorem applyUF1_of_cons
    {Δ : List LMonoTy}
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    {o : CoreLParams.Identifier} {a r : LMonoTy} {sa sr : TermType}
    {g : SMTTyDenote sa → SMTTyDenote sr}
    (htA : LExpr.HasTypeA Δ (.op () o (some (.tcons "arrow" [a, r])))
      (List.foldr LMonoTy.arrow r [a]))
    (hacc : baseTysToTermTypes [a] = some [sa]) (hrty : baseTyToTermType r = some sr)
    (hcons : HEq (opInterp o.name ((LMonoTy.tcons "arrow" [a, r]).substTyVars simpTyVarVal)) g)
    (v : SMTTyDenote sa) :
    applyUFDenote [sa] sr (cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
      (simpDenote opInterp fvarVal bvarVal (.op () o (some (.tcons "arrow" [a, r])))
        (List.foldr LMonoTy.arrow r [a]) htA)) (.cons v .nil) = g v := by
  have h_head : cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
      (simpDenote opInterp fvarVal bvarVal (.op () o (some (.tcons "arrow" [a, r])))
        (List.foldr LMonoTy.arrow r [a]) htA) = g := by
    simp only [simpDenote,
      Lambda.denote_op simpTcInterp opInterp fvarVal simpTyVarVal bvarVal htA]
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans (subst_heq (P := fun x => Lambda.TyDenote simpTcInterp simpTyVarVal x)
      (HasTypeA.op_inv htA)
      (opInterp o.name ((LMonoTy.tcons "arrow" [a, r]).substTyVars simpTyVarVal))) ?_
    exact hcons
  rw [h_head]; rfl

/-- LHS reduction for a **binary** operator head (the arity-2 analog of
    `applyUF1_of_cons`). -/
private theorem applyUF2_of_cons
    {Δ : List LMonoTy}
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    {o : CoreLParams.Identifier} {a1 a2 r : LMonoTy} {sa1 sa2 sr : TermType}
    {g : SMTTyDenote sa1 → SMTTyDenote sa2 → SMTTyDenote sr}
    (htA : LExpr.HasTypeA Δ (.op () o (some (.tcons "arrow" [a1, .tcons "arrow" [a2, r]])))
      (List.foldr LMonoTy.arrow r [a1, a2]))
    (hacc : baseTysToTermTypes [a1, a2] = some [sa1, sa2])
    (hrty : baseTyToTermType r = some sr)
    (hcons : HEq (opInterp o.name
      ((LMonoTy.tcons "arrow" [a1, .tcons "arrow" [a2, r]]).substTyVars simpTyVarVal)) g)
    (v1 : SMTTyDenote sa1) (v2 : SMTTyDenote sa2) :
    applyUFDenote [sa1, sa2] sr (cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
      (simpDenote opInterp fvarVal bvarVal
        (.op () o (some (.tcons "arrow" [a1, .tcons "arrow" [a2, r]])))
        (List.foldr LMonoTy.arrow r [a1, a2]) htA)) (.cons v1 (.cons v2 .nil)) = g v1 v2 := by
  have h_head : cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
      (simpDenote opInterp fvarVal bvarVal
        (.op () o (some (.tcons "arrow" [a1, .tcons "arrow" [a2, r]])))
        (List.foldr LMonoTy.arrow r [a1, a2]) htA) = g := by
    simp only [simpDenote,
      Lambda.denote_op simpTcInterp opInterp fvarVal simpTyVarVal bvarVal htA]
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans (subst_heq (P := fun x => Lambda.TyDenote simpTcInterp simpTyVarVal x)
      (HasTypeA.op_inv htA)
      (opInterp o.name
        ((LMonoTy.tcons "arrow" [a1, .tcons "arrow" [a2, r]]).substTyVars simpTyVarVal))) ?_
    exact hcons
  rw [h_head]; rfl

/-! ## Semantic preservation (soundness) of `toSMTTerm` — mutual induction -/

mutual
/-- **Semantic preservation of `toSMTTerm`.**

    If expression `e` has simple type `τ` (a base type) under contexts `Φ, Δ`,
    and the encoding `toSMTTerm bvs e` succeeds producing SMT term `tm`, then
    the LExpr denotation of `e` equals the SMT denotation of `tm`,
    transported across `tyDenote_eq_smtTyDenote`.

    This is the first half of the mutual induction; the second half
    (`appToSMTTerm_sound`) handles the application-spine case, relating
    the spine head's curried denotation applied to the translated argument
    values with the SMT translation's flat UF-application denotation.

    Together these two theorems establish that `toSMTTerm` is semantics-
    preserving: any model of the SMT encoding is a model of the original
    LExpr, and vice versa. -/
theorem toSMTTerm_sound
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (huwf : FVarCtxWF Φ ufs) (hψwf : FVarCtxWF Ψ ufs)
    {Δ : List LMonoTy} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Ψ Δ e τ)
    {bvs : TermVarCtx} (hbwf : BVarCtxWF Δ bvs ufs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (hop : OpInterpConsistent opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (ufInterp : UFInterp) (smtEnv : SMTVarEnv)
    (hfenv : UFEnvCorresponds huwf fvarVal ufInterp)
    (hopenv : OpEnvCorresponds hψwf opInterp ufInterp)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    {smtTy : TermType} (hτ : baseTyToTermType τ = some smtTy)
    (hbase : LExpr.MonoTyIsBase τ) (htA : LExpr.HasTypeA Δ e τ)
    {tm : Term} (h_ok : toSMTTerm bvs e = .ok tm)
    (htc : Term.typeCheck ufs bvs tm = some smtTy)
    : cast (tyDenote_eq_smtTyDenote hbase hτ)
        (simpDenote opInterp fvarVal bvarVal e τ htA)
      = SMTTerm.denote ufInterp smtEnv tm smtTy htc := by
  match e, τ, he, hτ, hbase, htA, h_ok, htc with
  | _, _, .const c hb, hτ, hbase, htA, h_ok, htc =>
    cases c with
    | boolConst b =>
      have htm : tm = .prim (.bool b) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, SMTTerm.denote, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ b).trans
        (@subst_heq _ SMTTyDenote _ _ (tc_prim_inv htc) b).symm)
    | intConst i =>
      have htm : tm = .prim (.int i) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, SMTTerm.denote, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ i).trans
        (@subst_heq _ SMTTyDenote _ _ (tc_prim_inv htc) i).symm)
    | strConst s =>
      have htm : tm = .prim (.string s) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, SMTTerm.denote, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ s).trans
        (@subst_heq _ SMTTyDenote _ _ (tc_prim_inv htc) s).symm)
    | bitvecConst n bv =>
      have htm : tm = .prim (.bitvec bv) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, SMTTerm.denote, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ bv).trans
        (@subst_heq _ SMTTyDenote _ _ (tc_prim_inv htc) bv).symm)
    | realConst _ =>
      exfalso; simp [toSMTTerm] at h_ok
  | _, _, .bvar i τ' hlook hb, hτ, hbase, htA, h_ok, htc =>
    have hi : i < bvs.length := by
      have hi_Δ : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
      exact hbwf.len_eq ▸ hi_Δ
    have htm : tm = .var (bvs[i]) := by
      unfold toSMTTerm at h_ok; rw [dif_pos hi] at h_ok
      simp at h_ok; exact h_ok.symm
    subst htm
    simp only [simpDenote, LExpr.denote]
    have hcorr := hbenv i τ' hb hlook
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans ?_ (SMTTerm_denote_var_heq ufInterp smtEnv _ _ htc).symm
    exact (cast_heq _ _).symm.trans (heq_of_eq hcorr)
  | _, _, .app fn arg rty hspine, hτ, hbase, htA, h_ok, htc =>
    -- `toSMTTerm (.app fn arg)` folds into `appToSMTTerm (.app fn arg) []`.
    have h_ok' : appToSMTTerm bvs (.app () fn arg) [] = .ok tm := by
      rw [appToSMTTerm]; rw [toSMTTerm] at h_ok; exact h_ok
    have hres := appToSMTTerm_sound huwf hψwf hspine hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv
      hfenv hopenv hbenv (show baseTysToTermTypes [] = some [] from rfl)
      (show Term.typeCheckArgs ufs bvs [] [] = true from rfl)
      HList.nil (show SMTTerm.denoteArgs ufInterp smtEnv [] [] rfl = HList.nil from rfl)
      hτ htA h_ok' htc
    -- `applyUFDenote [] smtTy f .nil = f`, and the arrow-cast at `[]` is the base cast.
    rw [hres]; rfl
  | _, _, .fvarNullary f τ_f rty hspine, hτ, hbase, htA, h_ok, htc =>
    have h_ok' : appToSMTTerm bvs (.fvar () f (some τ_f)) [] = .ok tm := by
      rw [toSMTTerm] at h_ok; exact h_ok
    have hres := appToSMTTerm_sound huwf hψwf hspine hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv
      hfenv hopenv hbenv (show baseTysToTermTypes [] = some [] from rfl)
      (show Term.typeCheckArgs ufs bvs [] [] = true from rfl)
      HList.nil (show SMTTerm.denoteArgs ufInterp smtEnv [] [] rfl = HList.nil from rfl)
      hτ htA h_ok' htc
    rw [hres]; rfl
  | _, _, .ite c t τ' e_ hc ht hee, hτ, hbase, htA, h_ok, htc =>
    have h_ok' := h_ok
    simp only [toSMTTerm, bind, Except.bind] at h_ok'
    revert h_ok' htc
    cases hc_ok : toSMTTerm bvs c with
    | error _ => simp
    | ok ct =>
      cases ht_ok : toSMTTerm bvs t with
      | error _ => simp
      | ok tt_tm =>
        cases he_ok : toSMTTerm bvs e_ with
        | error _ => simp
        | ok et =>
          intro h_ok' htc
          have htm : tm = Term.app (.core .ite) [ct, tt_tm, et] (Term.typeOf tt_tm) := by
            simp [toSMTTerm, bind, Except.bind, hc_ok, ht_ok, he_ok] at h_ok
            exact h_ok.symm
          subst htm
          have htc_c := toSMTTerm_typeChecks huwf hψwf hc hbwf hc_ok
            (show baseTyToTermType (.tcons "bool" []) = some .bool from rfl)
          have htc_t := toSMTTerm_typeChecks huwf hψwf ht hbwf ht_ok hτ
          have htc_e := toSMTTerm_typeChecks huwf hψwf hee hbwf he_ok hτ
          have ihc := toSMTTerm_sound huwf hψwf hc hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv
            hfenv hopenv hbenv (show baseTyToTermType (.tcons "bool" []) = some .bool from rfl)
            .bool (HasSimpType_implies_HasTypeA hc) hc_ok htc_c
          have iht := toSMTTerm_sound huwf hψwf ht hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv
            hfenv hopenv hbenv hτ hbase (HasSimpType_implies_HasTypeA ht) ht_ok htc_t
          have ihe := toSMTTerm_sound huwf hψwf hee hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv
            hfenv hopenv hbenv hτ hbase (HasSimpType_implies_HasTypeA hee) he_ok htc_e
          have h_ite_unfold := Lambda.denote_ite (T := CoreLParams) (tcInterp := simpTcInterp)
            (opInterp := opInterp) (fvarVal := fvarVal) (vt := simpTyVarVal)
            bvarVal
            (HasSimpType_implies_HasTypeA hc)
            (HasSimpType_implies_HasTypeA ht)
            (HasSimpType_implies_HasTypeA hee) htA
          simp only [simpDenote] at ihc iht ihe ⊢
          rw [h_ite_unfold]
          rw [SMTTerm_denote_ite]
          apply bif_heq_of_cond_branches (tyDenote_eq_smtTyDenote hbase hτ)
          · exact eq_of_heq ((cast_heq _ _).symm.trans (heq_of_eq ihc))
          · exact (cast_heq _ _).symm.trans (heq_of_eq iht)
          · exact (cast_heq _ _).symm.trans (heq_of_eq ihe)
  | _, _, .eq e1 e2 τ' hb he1 he2, hτ, hbase, htA, h_ok, htc =>
    have h_ok' := h_ok
    simp only [toSMTTerm, bind, Except.bind] at h_ok'
    revert h_ok' htc
    cases h1_ok : toSMTTerm bvs e1 with
    | error _ => simp
    | ok t1 =>
      cases h2_ok : toSMTTerm bvs e2 with
      | error _ => simp
      | ok t2 =>
        intro h_ok' htc
        have htm : tm = Term.app (.core .eq) [t1, t2] .bool := by
          simp [toSMTTerm, bind, Except.bind, h1_ok, h2_ok] at h_ok
          exact h_ok.symm
        subst htm
        have hτ_bool : smtTy = .bool := by
          simp [baseTyToTermType] at hτ; exact hτ.symm
        subst hτ_bool
        obtain ⟨τ'_smt, hτ'_spec⟩ := MonoTyIsBase_baseTyToTermType hb
        have htc1 := toSMTTerm_typeChecks huwf hψwf he1 hbwf h1_ok hτ'_spec
        have htc2 := toSMTTerm_typeChecks huwf hψwf he2 hbwf h2_ok hτ'_spec
        have ih1 := toSMTTerm_sound huwf hψwf he1 hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv
          hfenv hopenv hbenv hτ'_spec hb (HasSimpType_implies_HasTypeA he1) h1_ok htc1
        have ih2 := toSMTTerm_sound huwf hψwf he2 hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv
          hfenv hopenv hbenv hτ'_spec hb (HasSimpType_implies_HasTypeA he2) h2_ok htc2
        simp only [simpDenote] at ih1 ih2 ⊢
        rw [SMTTerm_denote_eq_unfold]
        obtain ⟨τ''_smt, htc1_inv, htc2_inv, heq_bool⟩ := tc_eq_inv htc
        have hτ''_eq : τ''_smt = τ'_smt :=
          Option.some.inj (htc1_inv.symm.trans htc1)
        subst hτ''_eq
        by_cases heq_vals : LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
            e1 τ' (HasSimpType_implies_HasTypeA he1) =
          LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
            e2 τ' (HasSimpType_implies_HasTypeA he2)
        · have h_lhs : LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
              (.eq () e1 e2) (.tcons "bool" []) htA = true :=
            Lambda.denote_eq_true bvarVal
              (HasSimpType_implies_HasTypeA he1)
              (HasSimpType_implies_HasTypeA he2) htA heq_vals
          rw [h_lhs]
          have hw_eq : SMTTerm.denote ufInterp smtEnv t1 _ htc1_inv =
              SMTTerm.denote ufInterp smtEnv t2 _ htc2_inv :=
            ih1.symm.trans (congrArg _ heq_vals |>.trans ih2)
          simp only [hw_eq, decide_true]; rfl
        · have h_lhs : LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
              (.eq () e1 e2) (.tcons "bool" []) htA = false :=
            Lambda.denote_eq_false bvarVal
              (HasSimpType_implies_HasTypeA he1)
              (HasSimpType_implies_HasTypeA he2) htA heq_vals
          rw [h_lhs]
          have hw_neq : SMTTerm.denote ufInterp smtEnv t1 _ htc1_inv ≠
              SMTTerm.denote ufInterp smtEnv t2 _ htc2_inv := by
            intro hw
            apply heq_vals
            have hcast : cast (tyDenote_eq_smtTyDenote hb hτ'_spec)
                (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
                  e1 τ' (HasSimpType_implies_HasTypeA he1)) =
              cast (tyDenote_eq_smtTyDenote hb hτ'_spec)
                (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
                  e2 τ' (HasSimpType_implies_HasTypeA he2)) :=
              ih1.trans (hw.trans ih2.symm)
            exact cast_inj_of_eq _ _ _ hcast
          simp only [hw_neq, decide_false]; rfl
  | _, _, .quant qty qbody qk qname hb hbody, hτ, hbase, htA, h_ok, htc =>
    obtain ⟨smtQTy, hqty⟩ := MonoTyIsBase_baseTyToTermType hb
    have hτ_bool : smtTy = .bool := by simp [baseTyToTermType] at hτ; exact hτ.symm
    subst hτ_bool
    simp only [toSMTTerm, hqty, bind, Except.bind] at h_ok
    revert htc
    cases hbody_ok : toSMTTerm (⟨s!"$__bv{bvs.length}", smtQTy⟩ :: bvs) qbody with
    | error _ => rw [hbody_ok] at h_ok; simp at h_ok
    | ok bodyTm =>
      rw [hbody_ok] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      intro htc
      let v : TermVar := ⟨s!"$__bv{bvs.length}", smtQTy⟩
      have hv : v = ⟨s!"$__bv{bvs.length}", smtQTy⟩ := rfl
      -- Well-formedness of the extended bound-variable context.
      have hstr : toString "$__bv" = "$__bv" := rfl
      have hstr2 : ∀ n : Nat, toString n = Nat.repr n := fun _ => rfl
      have hbwf' : BVarCtxWF (qty :: Δ) (v :: bvs) ufs := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [hbwf.len_eq]
        · intro i hi
          cases i with
          | zero => simp [hqty, hv]
          | succ j =>
            simp only [List.length_cons] at hi
            simp only [List.getElem_cons_succ]
            exact hbwf.ty_eq j (by omega)
        · intro i hi
          cases i with
          | zero =>
            simp only [hv, List.getElem_cons_zero, List.length_cons, hstr, hstr2]
            congr 1
          | succ j =>
            simp only [List.getElem_cons_succ, List.length_cons] at hi ⊢
            have hj : j < bvs.length := by omega
            have hid := hbwf.id_scheme j hj
            rw [hid]; simp only [hstr, hstr2]
            have : bvs.length + 1 - 1 - (j + 1) = bvs.length - 1 - j := by omega
            rw [this]
        · intro n
          have := hbwf.no_shadow n
          simp only [hstr, hstr2] at this
          exact this
      have hbody_tc : Term.typeCheck ufs (v :: bvs) bodyTm = some .bool :=
        toSMTTerm_typeChecks huwf hψwf hbody hbwf' hbody_ok rfl
      -- Correspondence of the body under any environment extending `smtEnv` at `v`.
      have h_ty_eq := tyDenote_eq_smtTyDenote hb hqty
      have body_eq : ∀ (x : Lambda.TyDenote simpTcInterp simpTyVarVal qty)
          (smtEnv' : SMTVarEnv),
          BVarEnvCorresponds hbwf' (.cons x bvarVal) smtEnv' →
          (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal
            (.cons x bvarVal) qbody (.tcons "bool" [])
            (HasSimpType_implies_HasTypeA hbody) : Bool) =
          SMTTerm.denote ufInterp smtEnv' bodyTm .bool hbody_tc := by
        intro x smtEnv' henv'
        have ih := toSMTTerm_sound huwf hψwf hbody hbwf' opInterp hop fvarVal (.cons x bvarVal)
          ufInterp smtEnv' hfenv hopenv henv' (show baseTyToTermType (.tcons "bool" []) = some .bool from rfl)
          .bool (HasSimpType_implies_HasTypeA hbody) hbody_ok hbody_tc
        simp only [simpDenote] at ih
        exact eq_of_heq ((cast_heq _ _).symm.trans (heq_of_eq ih))
      -- The combined environment for a given `ext`.
      simp only [simpDenote]
      apply eq_of_heq
      apply HEq.trans (cast_heq _ _)
      unfold LExpr.denote SMTTerm.denote
      dsimp only []
      obtain ⟨_, _, _, h_body_inv⟩ := HasTypeA.quant_inv htA
      obtain ⟨hbody_inv, heq_inv⟩ := tc_quant_inv htc
      dsimp only []
      apply HEq.trans _ (cast_heq _ _).symm
      apply heq_of_eq
      congr 1
      apply propext
      -- `v` is fresh: it does not occur in `bvs`.
      have hv_notin : v ∉ bvs := by
        intro hmem
        obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
        have hid := hbwf.id_scheme i hi
        have hveq : (bvs[i]'hi).id = v.id := congrArg TermVar.id hget
        rw [hid] at hveq
        simp only [hv] at hveq
        have := bv_str_inj _ _ hveq
        omega
      -- Bridge: LExpr body-truth at `x` ↔ SMT body-truth under the combined env
      -- that maps `v` to `x`.
      have h_pi1 : h_body_inv = HasSimpType_implies_HasTypeA hbody := proof_irrel _ _
      have h_pi2 : hbody_inv = hbody_tc := proof_irrel _ _
      rw [h_pi1, h_pi2]
      have bridge : ∀ (x : Lambda.TyDenote simpTcInterp simpTyVarVal qty)
          (ext : SMTVarEnv)
          (hxy : ext v = cast h_ty_eq x),
          (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal
            (.cons x bvarVal) qbody (.tcons "bool" [])
            (HasSimpType_implies_HasTypeA hbody) : Bool) = true ↔
          SMTTerm.denote ufInterp
            (fun w => if w ∈ [v] then ext w else smtEnv w) bodyTm .bool hbody_tc = true := by
        intro x ext hxy
        let smtEnv' : SMTVarEnv := fun w => if w ∈ [v] then ext w else smtEnv w
        have hcorr : BVarEnvCorresponds hbwf' (.cons x bvarVal) smtEnv' :=
          BVarEnvCorresponds_cons hbenv hb hqty x
            (show smtEnv' v = cast h_ty_eq x by
              simp only [smtEnv', List.mem_singleton, if_pos rfl]; exact hxy)
            (show ∀ w, w ≠ v → smtEnv' w = smtEnv w by
              intro w hwne
              simp only [smtEnv', List.mem_singleton, if_neg hwne])
            hbwf'
        have hbody := body_eq x smtEnv' hcorr
        exact ⟨fun h => hbody ▸ h, fun h => hbody ▸ h⟩
      -- Discharge the ∀/∃ equivalence.
      cases qk with
      | all =>
        constructor
        · intro hx ext
          let y := ext v
          exact (bridge (cast h_ty_eq.symm y) ext (by simp [y, cast_cast])).mp (hx _)
        · intro hext x
          let ext : SMTVarEnv := fun w =>
            if hw : w = v then cast (by rw [hw]; exact h_ty_eq) x else smtEnv w
          have hextv : ext v = cast h_ty_eq x := by simp [ext]
          exact (bridge x ext hextv).mpr (hext ext)
      | exist =>
        constructor
        · intro ⟨x, hx⟩
          let ext : SMTVarEnv := fun w =>
            if hw : w = v then cast (by rw [hw]; exact h_ty_eq) x else smtEnv w
          have hextv : ext v = cast h_ty_eq x := by simp [ext]
          exact ⟨ext, (bridge x ext hextv).mp hx⟩
        · intro ⟨ext, hext⟩
          let y := ext v
          exact ⟨cast h_ty_eq.symm y,
            (bridge (cast h_ty_eq.symm y) ext (by simp [y, cast_cast])).mpr hext⟩
  termination_by structural he

/-- **Semantic preservation of `appToSMTTerm` (spine case).**

    For an application spine `AppSpine Φ Ψ Δ e acc rty`, the function
    `appToSMTTerm` peels off `.app` nodes — translating each argument (for
    which `toSMTTerm_sound` provides the IH) — and at the head produces a
    flat UF/op application term.

    This theorem states that the resulting SMT term's denotation at the base
    return type `smtRty` equals the SMT-side application of the head's UF
    interpretation to the accumulated argument values.

    The key invariant is `h_acc_denote`: the SMT denotation of the already-
    translated argument terms equals `accArgVals`. At the `.app` step,
    `toSMTTerm_sound` on the fresh argument extends this invariant. At the
    head (`.fvar`/`.op`), `UFEnvCorresponds`/`OpInterpConsistent` closes the
    gap between LExpr and SMT interpretations.

    The conclusion is stated as `cast`-based equality at `SMTTyDenote smtRty`
    (a base type), using `tyDenote_eq_smtTyDenote` to transport between the
    LExpr and SMT type universes. When `acc = []`, this specializes to exactly
    the statement of `toSMTTerm_sound` for the `.app`/`.fvarNullary` cases. -/
theorem appToSMTTerm_sound
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (huwf : FVarCtxWF Φ ufs) (hψwf : FVarCtxWF Ψ ufs)
    {Δ : List LMonoTy} {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty)
    {bvs : TermVarCtx} (hbwf : BVarCtxWF Δ bvs ufs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (hop : OpInterpConsistent opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (ufInterp : UFInterp) (smtEnv : SMTVarEnv)
    (hfenv : UFEnvCorresponds huwf fvarVal ufInterp)
    (hopenv : OpEnvCorresponds hψwf opInterp ufInterp)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    {accTms : List Term} {accSmt : List TermType}
    (hacc : baseTysToTermTypes acc = some accSmt)
    (h_acc_tc : Term.typeCheckArgs ufs bvs accTms accSmt = true)
    (accArgVals : HList SMTTyDenote accSmt)
    (h_acc_denote : SMTTerm.denoteArgs ufInterp smtEnv accTms accSmt h_acc_tc = accArgVals)
    {smtRty : TermType} (hrty : baseTyToTermType rty = some smtRty)
    (htA : LExpr.HasTypeA Δ e (List.foldr LMonoTy.arrow rty acc))
    {tm : Term} (h_ok : appToSMTTerm bvs e accTms = .ok tm)
    (htc : Term.typeCheck ufs bvs tm = some smtRty)
    : -- Both sides have type `SMTTyDenote smtRty` (a base type): the LExpr head's
      -- curried denotation (of arrow type `foldr arrow rty acc`) is `cast` across
      -- `tyDenote_arrow_eq_UFDenote'` to `UFDenote' accSmt smtRty`, then applied to
      -- the argument values, yielding a base-type result — matching the SMT term's
      -- denotation. Now that the cast is a genuine term, this is plain equality.
      SMTTerm.denote ufInterp smtEnv tm smtRty htc
        = applyUFDenote accSmt smtRty
            (cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
              (simpDenote opInterp fvarVal bvarVal e
                (List.foldr LMonoTy.arrow rty acc) htA))
            accArgVals := by
  match e, acc, rty, hspine, hacc, h_acc_tc, accArgVals, h_acc_denote, hrty, htA, h_ok, htc with
  | _, _, _, .app fn arg aty acc' rty' harg hrest,
      hacc, h_acc_tc, accArgVals, h_acc_denote, hrty, htA, h_ok, htc =>
    -- `appToSMTTerm (.app fn arg) accTms` translates `arg`, then recurses on `fn`
    -- with the translated argument prepended to the accumulator.
    rw [appToSMTTerm] at h_ok
    cases h_arg_ok : toSMTTerm bvs arg with
    | error e => rw [h_arg_ok] at h_ok; simp [bind, Except.bind] at h_ok
    | ok argt =>
      rw [h_arg_ok] at h_ok; simp only [bind, Except.bind] at h_ok
      -- The argument's type `aty` is base, hence encodes as `saty`.
      obtain ⟨saty, h_saty⟩ := MonoTyIsBase_baseTyToTermType (HasSimpType_base harg)
      have h_argt := toSMTTerm_typeChecks huwf hψwf harg hbwf h_arg_ok h_saty
      have hacc' : baseTysToTermTypes (aty :: acc') = some (saty :: accSmt) := by
        simp only [baseTysToTermTypes, h_saty, hacc, bind, Option.bind]
      have h_acc_tc' : Term.typeCheckArgs ufs bvs (argt :: accTms) (saty :: accSmt) = true := by
        simp only [Term.typeCheckArgs, h_argt]; simp [h_acc_tc, BEq.beq]
      -- The fresh argument's value, and the extended accumulator's denotation.
      have htA_arg : LExpr.HasTypeA Δ arg aty := HasSimpType_implies_HasTypeA harg
      have htA_fn : LExpr.HasTypeA Δ fn (List.foldr LMonoTy.arrow rty' (aty :: acc')) :=
        AppSpine_implies_HasTypeA hrest
      let vArg : SMTTyDenote saty := SMTTerm.denote ufInterp smtEnv argt saty h_argt
      have h_acc_denote' :
          SMTTerm.denoteArgs ufInterp smtEnv (argt :: accTms) (saty :: accSmt) h_acc_tc'
            = .cons vArg accArgVals := by
        rw [← h_acc_denote]; rfl
      -- Argument soundness: `vArg` is the cast of the LExpr denotation of `arg`.
      have h_arg_sound : cast (tyDenote_eq_smtTyDenote (HasSimpType_base harg) h_saty)
          (simpDenote opInterp fvarVal bvarVal arg aty htA_arg) = vArg :=
        toSMTTerm_sound huwf hψwf harg hbwf opInterp hop fvarVal bvarVal
          ufInterp smtEnv hfenv hopenv hbenv h_saty (HasSimpType_base harg) htA_arg h_arg_ok h_argt
      -- Instantiate the IH on the sub-spine `hrest` with the extended accumulator.
      have ih := appToSMTTerm_sound huwf hψwf hrest hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv
        hfenv hopenv hbenv hacc' h_acc_tc' (.cons vArg accArgVals) h_acc_denote' hrty htA_fn h_ok htc
      rw [ih]
      -- `applyUFDenote` on `(saty :: accSmt)` peels its head argument (defeq); it
      -- remains to show the peeled head functions agree.
      show applyUFDenote accSmt smtRty _ accArgVals = applyUFDenote accSmt smtRty _ accArgVals
      apply congrArg (fun w => applyUFDenote accSmt smtRty w accArgVals)
      -- The fn head (cast to `UFDenote' (saty::accSmt) smtRty`) applied to `vArg`
      -- equals the app-node head (cast to `UFDenote' accSmt smtRty`).  Rewrite `vArg`
      -- to `cast (denote arg)` and the app-node denotation to `fn-denote arg-denote`
      -- (`denote_app`), then the two casts commute (`cast_arrow_app`).
      rw [← h_arg_sound]
      have happ : simpDenote opInterp fvarVal bvarVal (.app () fn arg)
          (List.foldr LMonoTy.arrow rty' acc') htA
          = (simpDenote opInterp fvarVal bvarVal fn
              (List.foldr LMonoTy.arrow rty' (aty :: acc')) htA_fn)
            (simpDenote opInterp fvarVal bvarVal arg aty htA_arg) := by
        simp only [simpDenote]
        exact Lambda.denote_app (T := CoreLParams) (tcInterp := simpTcInterp)
          (opInterp := opInterp) (fvarVal := fvarVal) (vt := simpTyVarVal)
          bvarVal htA_fn htA_arg htA
      rw [happ]
      exact cast_arrow_app (tyDenote_eq_smtTyDenote (HasSimpType_base harg) h_saty)
        (tyDenote_arrow_eq_UFDenote' hacc hrty) (tyDenote_arrow_eq_UFDenote' hacc' hrty)
        (simpDenote opInterp fvarVal bvarVal fn (List.foldr LMonoTy.arrow rty' (aty :: acc')) htA_fn)
        (simpDenote opInterp fvarVal bvarVal arg aty htA_arg)
  | _, _, _, .fvar f τ_f acc' rty' hmem hcol hb,
      hacc, h_acc_tc, accArgVals, h_acc_denote, hrty, htA, h_ok, htc =>
    -- The head resolves to a UF; destructure it so the signature equalities are
    -- plain field equations (no dependent-struct rewriting).
    have hresolve := huwf.fvar_resolves f.name τ_f hmem
    obtain ⟨uf, hlk⟩ := Option.isSome_iff_exists.mp hresolve
    obtain ⟨ufid, ufargs, ufout⟩ := uf
    have hid : ufid = f.name := lookupUF_id hlk
    subst hid
    have hargs_uf := huwf.args_eq f.name τ_f _ hmem hlk
    have hout_uf := huwf.out_eq f.name τ_f _ hmem hlk
    rw [hcol] at hargs_uf hout_uf
    simp only at hargs_uf hout_uf
    -- accSmt = ufargs (both encode acc'); smtRty = ufout.
    rw [hargs_uf] at hacc; injection hacc with hacc_eq; subst hacc_eq
    rw [hout_uf] at hrty; injection hrty with hrty_eq; subst hrty_eq
    have hmem_uf : (⟨f.name, ufargs, ufout⟩ : UF) ∈ ufs := lookupUF_mem hlk
    -- `buildAppHead` produced the UF-application term.
    have h_ok' : buildAppHead (.fvar () f (some τ_f)) accTms = .ok tm := by
      rw [← h_ok, appToSMTTerm]; intro fn arg h; nomatch h
    have htm : tm = .app (.core (.uf ⟨f.name, ufargs, ufout⟩)) accTms ufout := by
      simp only [buildAppHead, hcol, hout_uf, hargs_uf] at h_ok'
      injection h_ok' with h_ok'; exact h_ok'.symm
    subst htm
    -- Unfold the SMT denotation of the UF application.
    rw [SMTTerm_denote_uf_unfold]
    -- `UFEnvCorresponds` at `(f.name, τ_f)`, reduced to our concrete `uf`.
    have hfe := hfenv f.name τ_f hmem
    have hlk_uf : (lookupUF ufs f.name).get (huwf.fvar_resolves f.name τ_f hmem)
        = ⟨f.name, ufargs, ufout⟩ := by
      have hsome := huwf.fvar_resolves f.name τ_f hmem
      change (lookupUF ufs f.name).get hsome = _
      simp only [show lookupUF ufs f.name = some ⟨f.name, ufargs, ufout⟩ from hlk, Option.get_some]
    -- `ufInterp` at the resolved `.get` and at the concrete literal are HEq (equal args).
    have h_ufi_heq : HEq (ufInterp ((lookupUF ufs f.name).get (huwf.fvar_resolves f.name τ_f hmem)))
        (ufInterp ⟨f.name, ufargs, ufout⟩) := by rw [hlk_uf]
    -- The LExpr head denotation, cast to `UFDenote' ufargs ufout`, equals `ufInterp uf`.
    have h_head_eq : cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
        (simpDenote opInterp fvarVal bvarVal (.fvar () f (some τ_f))
          (List.foldr LMonoTy.arrow rty' acc') htA) = ufInterp ⟨f.name, ufargs, ufout⟩ := by
      simp only [simpDenote, LExpr.denote]
      apply eq_of_heq
      refine HEq.trans ?_ (h_ufi_heq)
      refine HEq.trans ?_ (heq_of_eq hfe)
      -- `f` and `⟨f.name, ()⟩` are defeq (metadata : Unit); strip the `cast` on the
      -- goal LHS and the `▸`/`cast` transports down to the bare `fvarVal` value.
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans
        (subst_heq (P := fun x => Lambda.TyDenote simpTcInterp simpTyVarVal x)
          (HasTypeA.fvar_inv htA) (fvarVal f (τ_f.substTyVars simpTyVarVal))) ?_
      exact (cast_heq _ _).symm
    -- Rewrite the denoted args to `accArgVals`.
    have h_denoteArgs : SMTTerm.denoteArgs ufInterp smtEnv accTms
        (⟨f.name, ufargs, ufout⟩ : UF).args (tc_uf_inv htc).1 = accArgVals := by
      rw [← h_acc_denote]
    -- Close via congruence: both sides are `applyUFDenote ufargs ufout ? accArgVals`.
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    apply heq_of_eq
    rw [h_denoteArgs, h_head_eq]
  | _, _, _, .fnOp o oty acc' rty' hmem hnpre hcol hb,
      hacc, h_acc_tc, accArgVals, h_acc_denote, hrty, htA, h_ok, htc =>
    -- User-defined-function head, mirroring the `.fvar` arm: the LExpr side denotes
    -- through `opInterp` (an `.op` node uses `HasTypeA.op_inv` / `opInterp o.name`),
    -- and the correspondence used is `OpEnvCorresponds` (`hopenv`). The `hnpre` guard
    -- forces `buildAppHead`'s `.op`-none fallback (the UF-application branch).
    -- The head resolves to a UF; destructure it so the signature equalities are
    -- plain field equations (no dependent-struct rewriting).
    have hresolve := hψwf.fvar_resolves o.name oty hmem
    obtain ⟨uf, hlk⟩ := Option.isSome_iff_exists.mp hresolve
    obtain ⟨ufid, ufargs, ufout⟩ := uf
    have hid : ufid = o.name := lookupUF_id hlk
    subst hid
    have hargs_uf := hψwf.args_eq o.name oty _ hmem hlk
    have hout_uf := hψwf.out_eq o.name oty _ hmem hlk
    rw [hcol] at hargs_uf hout_uf
    simp only at hargs_uf hout_uf
    -- accSmt = ufargs (both encode acc'); smtRty = ufout.
    rw [hargs_uf] at hacc; injection hacc with hacc_eq; subst hacc_eq
    rw [hout_uf] at hrty; injection hrty with hrty_eq; subst hrty_eq
    have hmem_uf : (⟨o.name, ufargs, ufout⟩ : UF) ∈ ufs := lookupUF_mem hlk
    -- `buildAppHead` produced the UF-application term (via the `.op`-none fallback).
    have h_ok' : buildAppHead (.op () o (some oty)) accTms = .ok tm := by
      rw [← h_ok, appToSMTTerm]; intro fn arg h; nomatch h
    have htm : tm = .app (.core (.uf ⟨o.name, ufargs, ufout⟩)) accTms ufout := by
      simp only [buildAppHead, hnpre, hcol, hout_uf, hargs_uf] at h_ok'
      injection h_ok' with h_ok'; exact h_ok'.symm
    subst htm
    -- Unfold the SMT denotation of the UF application.
    rw [SMTTerm_denote_uf_unfold]
    -- `OpEnvCorresponds` at `(o.name, oty)`, reduced to our concrete `uf`.
    have hoe := hopenv o.name oty hmem
    have hlk_uf : (lookupUF ufs o.name).get (hψwf.fvar_resolves o.name oty hmem)
        = ⟨o.name, ufargs, ufout⟩ := by
      have hsome := hψwf.fvar_resolves o.name oty hmem
      change (lookupUF ufs o.name).get hsome = _
      simp only [show lookupUF ufs o.name = some ⟨o.name, ufargs, ufout⟩ from hlk, Option.get_some]
    -- `ufInterp` at the resolved `.get` and at the concrete literal are HEq (equal args).
    have h_ufi_heq : HEq (ufInterp ((lookupUF ufs o.name).get (hψwf.fvar_resolves o.name oty hmem)))
        (ufInterp ⟨o.name, ufargs, ufout⟩) := by rw [hlk_uf]
    -- The LExpr head denotation, cast to `UFDenote' ufargs ufout`, equals `ufInterp uf`.
    -- The `.op` denotation uses `opInterp o.name` directly, matching `OpEnvCorresponds`.
    have h_head_eq : cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
        (simpDenote opInterp fvarVal bvarVal (.op () o (some oty))
          (List.foldr LMonoTy.arrow rty' acc') htA) = ufInterp ⟨o.name, ufargs, ufout⟩ := by
      simp only [simpDenote, LExpr.denote]
      apply eq_of_heq
      refine HEq.trans ?_ (h_ufi_heq)
      refine HEq.trans ?_ (heq_of_eq hoe)
      -- Strip the `cast` on the goal LHS and the `▸`/`cast` transports down to the
      -- bare `opInterp` value (via `HasTypeA.op_inv`).
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans
        (subst_heq (P := fun x => Lambda.TyDenote simpTcInterp simpTyVarVal x)
          (HasTypeA.op_inv htA) (opInterp o.name (oty.substTyVars simpTyVarVal))) ?_
      exact (cast_heq _ _).symm
    -- Rewrite the denoted args to `accArgVals`.
    have h_denoteArgs : SMTTerm.denoteArgs ufInterp smtEnv accTms
        (⟨o.name, ufargs, ufout⟩ : UF).args (tc_uf_inv htc).1 = accArgVals := by
      rw [← h_acc_denote]
    -- Close via congruence: both sides are `applyUFDenote ufargs ufout ? accArgVals`.
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    apply heq_of_eq
    rw [h_denoteArgs, h_head_eq]
  | _, _, _, .op o oty acc' rty' hopty hcol,
      hacc, h_acc_tc, accArgVals, h_acc_denote, hrty, htA, h_ok, htc =>
    have h_ok' : buildAppHead (.op () o (some oty)) accTms = .ok tm := by
      rw [← h_ok, appToSMTTerm]; intro fn arg h; nomatch h
    generalize hcop : CoreOp.ofString o.name = cop at hopty
    cases hopty with
    | intNeg =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "int" []] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, hst, h1⟩ := typeCheckArgs_one_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) .nil := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF1_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.neg o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.neg [t1] .int) .int htc
          = cast (by rw [(tc_intUn_inv htc).2])
              (-(SMTTerm.denote ufInterp smtEnv t1 .int (tc_intUn_inv htc).1)) := by
        simp only [SMTTerm.denote]
        obtain ⟨ht, heq⟩ := tc_intUn_inv htc
        rfl
      rw [hrhs, proof_irrel (tc_intUn_inv htc).1 h1]
      simp only [cast_eq]
    | boolNot =>
      have hoty : oty = .tcons "arrow" [.tcons "bool" [], .tcons "bool" []] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, hst, h1⟩ := typeCheckArgs_one_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .bool h1) .nil := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF1_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.not o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app (.core .not) [t1] .bool) .bool htc
          = cast (by rw [(tc_not_inv htc).2])
              (!(SMTTerm.denote ufInterp smtEnv t1 .bool (tc_not_inv htc).1)) := by
        simp only [SMTTerm.denote]
        obtain ⟨ht, heq⟩ := tc_not_inv htc
        rfl
      rw [hrhs, proof_irrel (tc_not_inv htc).1 h1]
      simp only [cast_eq]
    | intAdd =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.add o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.add [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inl rfl)).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inl rfl)).1) + (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inl rfl)).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inl rfl)).1 h1, proof_irrel (tc_intBin_inv htc (.inl rfl)).2.1 h2]
      simp only [cast_eq]
    | intSub =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.sub o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.sub [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inr (.inl rfl))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inl rfl))).1) - (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inl rfl))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inr (.inl rfl))).1 h1, proof_irrel (tc_intBin_inv htc (.inr (.inl rfl))).2.1 h2]
      simp only [cast_eq]
    | intMul =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.mul o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.mul [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inr (.inr (.inl rfl)))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inl rfl)))).1) * (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inl rfl)))).1 h1, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1 h2]
      simp only [cast_eq]
    | intDiv =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.div o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.div [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1) / (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1 h1, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1 h2]
      simp only [cast_eq]
    | intSafeDiv =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.safeDiv o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.div [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1) / (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1 h1, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1 h2]
      simp only [cast_eq]
    | intDivT =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.divT o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.div [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1) / (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1 h1, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1 h2]
      simp only [cast_eq]
    | intSafeDivT =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.safeDivT o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.div [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1) / (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1 h1, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1 h2]
      simp only [cast_eq]
    | intMod =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.mod_ o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.mod [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1) % (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1 h1, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1 h2]
      simp only [cast_eq]
    | intSafeMod =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.safeMod o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.mod [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1) % (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1 h1, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1 h2]
      simp only [cast_eq]
    | intModT =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.modT o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.mod [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1) % (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1 h1, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1 h2]
      simp only [cast_eq]
    | intSafeModT =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.safeModT o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.mod [t1, t2] .int) .int htc
          = cast (by rw [(tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1) % (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1 h1, proof_irrel (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1 h2]
      simp only [cast_eq]
    | intLt =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.lt o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.lt [t1, t2] .bool) .bool htc
          = cast (by rw [(tc_intCmp_inv htc (.inr (.inl rfl))).2.2]) (decide ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intCmp_inv htc (.inr (.inl rfl))).1) < (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intCmp_inv htc (.inr (.inl rfl))).2.1))) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intCmp_inv htc (.inr (.inl rfl))).1 h1, proof_irrel (tc_intCmp_inv htc (.inr (.inl rfl))).2.1 h2]
      simp only [cast_eq]
    | intLe =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.le o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.le [t1, t2] .bool) .bool htc
          = cast (by rw [(tc_intCmp_inv htc (.inl rfl)).2.2]) (decide ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intCmp_inv htc (.inl rfl)).1) ≤ (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intCmp_inv htc (.inl rfl)).2.1))) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intCmp_inv htc (.inl rfl)).1 h1, proof_irrel (tc_intCmp_inv htc (.inl rfl)).2.1 h2]
      simp only [cast_eq]
    | intGt =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.gt o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.gt [t1, t2] .bool) .bool htc
          = cast (by rw [(tc_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.2]) (decide ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intCmp_inv htc (.inr (.inr (.inr rfl)))).1) > (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1))) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intCmp_inv htc (.inr (.inr (.inr rfl)))).1 h1, proof_irrel (tc_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1 h2]
      simp only [cast_eq]
    | intGe =>
      have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .int h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.ge o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.ge [t1, t2] .bool) .bool htc
          = cast (by rw [(tc_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.2]) (decide ((SMTTerm.denote ufInterp smtEnv t1 .int (tc_intCmp_inv htc (.inr (.inr (.inl rfl)))).1) ≥ (SMTTerm.denote ufInterp smtEnv t2 .int (tc_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1))) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_intCmp_inv htc (.inr (.inr (.inl rfl)))).1 h1, proof_irrel (tc_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1 h2]
      simp only [cast_eq]
    | boolAnd =>
      have hoty : oty = .tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .bool h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .bool h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.and_ o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.and [t1, t2] .bool) .bool htc
          = cast (by rw [(tc_boolBin_inv htc (.inl rfl)).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .bool (tc_boolBin_inv htc (.inl rfl)).1) && (SMTTerm.denote ufInterp smtEnv t2 .bool (tc_boolBin_inv htc (.inl rfl)).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_boolBin_inv htc (.inl rfl)).1 h1, proof_irrel (tc_boolBin_inv htc (.inl rfl)).2.1 h2]
      simp only [cast_eq]
    | boolOr =>
      have hoty : oty = .tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .bool h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .bool h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.or_ o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.or [t1, t2] .bool) .bool htc
          = cast (by rw [(tc_boolBin_inv htc (.inr (.inl rfl))).2.2]) ((SMTTerm.denote ufInterp smtEnv t1 .bool (tc_boolBin_inv htc (.inr (.inl rfl))).1) || (SMTTerm.denote ufInterp smtEnv t2 .bool (tc_boolBin_inv htc (.inr (.inl rfl))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_boolBin_inv htc (.inr (.inl rfl))).1 h1, proof_irrel (tc_boolBin_inv htc (.inr (.inl rfl))).2.1 h2]
      simp only [cast_eq]
    | boolImplies =>
      have hoty : oty = .tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .bool h1) (.cons (SMTTerm.denote ufInterp smtEnv t2 .bool h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.implies o.name hcop))]
      have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.implies [t1, t2] .bool) .bool htc
          = cast (by rw [(tc_boolBin_inv htc (.inr (.inr rfl))).2.2]) (!(SMTTerm.denote ufInterp smtEnv t1 .bool (tc_boolBin_inv htc (.inr (.inr rfl))).1) || (SMTTerm.denote ufInterp smtEnv t2 .bool (tc_boolBin_inv htc (.inr (.inr rfl))).2.1)) := by
        simp only [SMTTerm.denote]
        split
        rfl
      rw [hrhs, proof_irrel (tc_boolBin_inv htc (.inr (.inr rfl))).1 h1, proof_irrel (tc_boolBin_inv htc (.inr (.inr rfl))).2.1 h2]
      simp only [cast_eq]
    | boolEquiv =>
      have hoty : oty = .tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]] := by
        have := collectArrowTy_foldr oty; rw [hcol] at this
        simpa [List.foldr, LMonoTy.arrow] using this
      subst hoty
      simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
      injection hacc with hacc; subst hacc
      simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
      obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
      simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok'
      injection h_ok' with h_ok'; subst h_ok'
      have h_av : accArgVals = .cons (SMTTerm.denote ufInterp smtEnv t1 .bool h1)
          (.cons (SMTTerm.denote ufInterp smtEnv t2 .bool h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.equiv o.name hcop))]
      -- The SMT `.eq` denotation (via `Classical.propDecidable` at the operand type
      -- `τ'`) matches the LExpr `decide` at `.bool`; bridge the operand type via
      -- `SMTTerm_denote_cast` and reconcile the two decidability instances.
      rw [SMTTerm_denote_eq_unfold]
      simp only [cast_eq]
      have hτ' : (tc_eq_inv htc).1 = .bool :=
        Option.some.inj ((tc_eq_inv htc).2.1.symm.trans h1)
      have hd1 := SMTTerm_denote_cast ufInterp smtEnv t1 .bool (tc_eq_inv htc).1
        h1 (tc_eq_inv htc).2.1 hτ'.symm
      have hd2 := SMTTerm_denote_cast ufInterp smtEnv t2 .bool (tc_eq_inv htc).1
        h2 (tc_eq_inv htc).2.2.1 hτ'.symm
      congr 1; apply propext; constructor
      · intro heq'; exact eq_of_heq (hd1.trans ((heq_of_eq heq').trans hd2.symm))
      · intro heq'; exact eq_of_heq (hd1.symm.trans ((heq_of_eq heq').trans hd2))
  termination_by structural hspine
end

/-! ## Encoder totality (progress)

`toSMTTerm_typeChecks` assumes `h_ok : toSMTTerm bvs e = .ok tm`. That hypothesis is
itself derivable from `HasSimpType`: a well-typed expression never hits any of the
encoder's `.error` sites. The four failure points are each ruled out by the typing
judgment:
  • `.const (.realConst _)`      — excluded: `MonoTyIsBase` has no real case.
  • `.bvar` out of bounds        — excluded by `BVarCtxWF.len_eq` + `Δ[i]? = some τ`.
  • quantifier type not encodable — excluded: `MonoTyIsBase qty` ⇒ encodable.
  • `buildAppHead` fvar/op errors — excluded by `FVarCtxWF` / `CoreOpHasType`.

Success of `appToSMTTerm` depends only on the *head* (via `buildAppHead`) and on each
peeled argument translating successfully, so the spine lemma needs no accumulator
invariant. -/

mutual
/-- The encoder never errors on a well-typed expression. -/
theorem toSMTTerm_succeeds
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (huwf : FVarCtxWF Φ ufs) (hψwf : FVarCtxWF Ψ ufs)
    {Δ : List LMonoTy} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Ψ Δ e τ)
    {bvs : TermVarCtx} (hbwf : BVarCtxWF Δ bvs ufs) :
    match toSMTTerm bvs e with
    | .error _ => False
    | .ok _ => True := by
  match he with
  | .const c hbase =>
    -- `MonoTyIsBase c.ty` rules out `.realConst` (the only erroring constant):
    -- a real type has no SMT encoding, contradicting `MonoTyIsBase`'s encodability.
    cases c <;> simp only [toSMTTerm] <;>
      first
        | exact True.intro
        | (obtain ⟨s, hs⟩ := MonoTyIsBase_baseTyToTermType hbase
           simp [LConst.ty, LMonoTy.real, baseTyToTermType] at hs)
  | .bvar i _ hlook hbase =>
    -- `hlook` bounds `i` in `Δ`; `hbwf.len_eq` transfers the bound to `bvs`, so the
    -- dependent `if` in `toSMTTerm` takes the `.ok` branch.
    simp only [toSMTTerm]
    have hi_Δ : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
    have hi : i < bvs.length := hbwf.len_eq ▸ hi_Δ
    rw [dif_pos hi]; exact True.intro
  | .app fn arg rty hspine =>
    -- `toSMTTerm (.app ..)` is defeq to `appToSMTTerm (.app ..) []`.
    exact appSpine_succeeds huwf hψwf hspine hbwf []
  | .fvarNullary f τ_f rty hspine =>
    -- `toSMTTerm (.fvar ..)` is defeq to `appToSMTTerm (.fvar ..) []`.
    exact appSpine_succeeds huwf hψwf hspine hbwf []
  | .ite c t _ e_ hc ht hee =>
    have ihc := toSMTTerm_succeeds huwf hψwf hc hbwf
    have iht := toSMTTerm_succeeds huwf hψwf ht hbwf
    have ihe := toSMTTerm_succeeds huwf hψwf hee hbwf
    unfold toSMTTerm; simp only [bind, Except.bind]
    cases hc_ok : toSMTTerm bvs c with
    | error e => rw [hc_ok] at ihc; exact ihc.elim
    | ok ct =>
      cases ht_ok : toSMTTerm bvs t with
      | error e => rw [ht_ok] at iht; exact iht.elim
      | ok tt =>
        cases he_ok : toSMTTerm bvs e_ with
        | error e => rw [he_ok] at ihe; exact ihe.elim
        | ok et => exact True.intro
  | .eq e1 e2 τ' hbase he1 he2 =>
    have ih1 := toSMTTerm_succeeds huwf hψwf he1 hbwf
    have ih2 := toSMTTerm_succeeds huwf hψwf he2 hbwf
    unfold toSMTTerm; simp only [bind, Except.bind]
    cases h1_ok : toSMTTerm bvs e1 with
    | error e => rw [h1_ok] at ih1; exact ih1.elim
    | ok t1 =>
      cases h2_ok : toSMTTerm bvs e2 with
      | error e => rw [h2_ok] at ih2; exact ih2.elim
      | ok t2 => exact True.intro
  | .quant qty qbody qk qname hbase hbody =>
    -- `MonoTyIsBase qty` ⇒ `qty` is encodable, so the guard passes; the body then
    -- succeeds by IH under the extended bound-variable context.
    obtain ⟨smtQTy, hqty_eq⟩ := MonoTyIsBase_baseTyToTermType hbase
    have hstr : toString "$__bv" = "$__bv" := rfl
    have hstr2 : ∀ n : Nat, toString n = Nat.repr n := fun _ => rfl
    have hbwf' : BVarCtxWF (qty :: Δ)
        (⟨"$__bv" ++ (bvs.length).repr, smtQTy⟩ :: bvs) ufs := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [hbwf.len_eq]
      · intro i hi
        cases i with
        | zero => simp [hqty_eq]
        | succ j =>
          simp only [List.length_cons] at hi
          simp only [List.getElem_cons_succ]
          exact hbwf.ty_eq j (by omega)
      · intro i hi
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero, List.length_cons, hstr, hstr2]
          congr 1
        | succ j =>
          simp only [List.getElem_cons_succ, List.length_cons] at hi ⊢
          have hj : j < bvs.length := by omega
          have hid := hbwf.id_scheme j hj
          rw [hid]; simp only [hstr, hstr2]
          have : bvs.length + 1 - 1 - (j + 1) = bvs.length - 1 - j := by omega
          rw [this]
      · intro n
        have := hbwf.no_shadow n
        simp only [hstr, hstr2] at this
        exact this
    have ihbody := toSMTTerm_succeeds huwf hψwf hbody hbwf'
    unfold toSMTTerm
    simp only [hqty_eq, bind, Except.bind]
    cases hbody_ok :
        toSMTTerm (⟨"$__bv" ++ (bvs.length).repr, smtQTy⟩ :: bvs) qbody with
    | error e => rw [hbody_ok] at ihbody; exact ihbody.elim
    | ok bodyTm => exact True.intro
  termination_by structural he

/-- `appToSMTTerm` never errors along a well-typed application spine, for any
    already-translated accumulator. -/
theorem appSpine_succeeds
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (huwf : FVarCtxWF Φ ufs) (hψwf : FVarCtxWF Ψ ufs)
    {Δ : List LMonoTy} {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty)
    {bvs : TermVarCtx} (hbwf : BVarCtxWF Δ bvs ufs) (accTms : List Term) :
    match appToSMTTerm bvs e accTms with
    | .error _ => False
    | .ok _ => True := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    -- Translate the argument (succeeds by IH), then recurse on the function spine
    -- with it prepended to the accumulator.
    have iharg := toSMTTerm_succeeds huwf hψwf harg hbwf
    rw [appToSMTTerm]; simp only [bind, Except.bind]
    cases h_arg_ok : toSMTTerm bvs arg with
    | error e => rw [h_arg_ok] at iharg; exact iharg.elim
    | ok argt => exact appSpine_succeeds huwf hψwf hrest hbwf (argt :: accTms)
  | .fvar f τ acc' rty hmem hcollect hbase =>
    -- `FVarCtxWF` supplies SMT encodings for the argument and return types, so
    -- `buildAppHead` on the fvar head returns `.ok`.
    have huwf_info := huwf.fvar_has_uf f.name τ hmem
    rw [hcollect] at huwf_info
    obtain ⟨smtArgTys, smtRty', h_smtArgTys, h_smtRty', _⟩ := huwf_info
    simp only [appToSMTTerm, buildAppHead, hcollect, h_smtRty', h_smtArgTys]
  | .op o oty acc' rty hop hcollect =>
    -- `CoreOpHasType` ⇒ `corePredefinedOpToSMTOp` is `some`, so `buildAppHead` on
    -- the op head returns `.ok`.
    generalize hcop : CoreOp.ofString o.name = cop at hop
    simp only [appToSMTTerm, buildAppHead, hcop]
    cases hop <;> simp only [corePredefinedOpToSMTOp] <;> exact True.intro
  | .fnOp o oty acc' rty hmem hnpre hcollect hbase =>
    -- User-defined-function head: `FVarCtxWF Ψ ufs` supplies SMT encodings for the
    -- argument and return types, so `buildAppHead`'s `.op`-none fallback returns `.ok`.
    have hψwf_info := hψwf.fvar_has_uf o.name oty hmem
    rw [hcollect] at hψwf_info
    obtain ⟨smtArgTys, smtRty', h_smtArgTys, h_smtRty', _⟩ := hψwf_info
    simp only [appToSMTTerm, buildAppHead, hnpre, hcollect, h_smtRty', h_smtArgTys]
  termination_by structural hspine
end

/-! ## Top-level correctness

Wraps `toSMTTerm_succeeds` (totality), `toSMTTerm_typeChecks` (sort agreement), and
`Term.typeOf_of_typeCheck` (annotation fidelity) into a single statement that assumes
*only* `HasSimpType` plus the context well-formedness side conditions — no `h_ok`, no `hτ`.

Both would-be existentials are replaced by pattern matches that return `False` on the
impossible branches:
  • `toSMTTerm bvs e = .error _`   — impossible (totality).
  • `baseTyToTermType τ = none`     — impossible (`τ` is `MonoTyIsBase`). -/

/-- If `e` has simple type `τ`, then `toSMTTerm` produces a term `tm` whose SMT
    sort is exactly the encoding of `τ` — both at the type it type-checks (hence
    denotes) and at its syntactic `Term.typeOf`. -/
theorem toSMTTerm_type_correct
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (huwf : FVarCtxWF Φ ufs) (hψwf : FVarCtxWF Ψ ufs)
    {Δ : List LMonoTy} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Ψ Δ e τ)
    {bvs : TermVarCtx} (hbwf : BVarCtxWF Δ bvs ufs) :
    match toSMTTerm bvs e, baseTyToTermType τ with
    | .ok tm, some smtTy =>
      Term.typeCheck ufs bvs tm = some smtTy ∧ Term.typeOf tm = smtTy
    | _, _ => False := by
  -- `τ` is base, so it is encodable — kills the `none` arm.
  obtain ⟨smtTy, hτ⟩ := MonoTyIsBase_baseTyToTermType (HasSimpType_base he)
  -- The encoder succeeds — kills the `.error` arm.
  have hsucc := toSMTTerm_succeeds huwf hψwf he hbwf
  rw [hτ]
  cases h_ok : toSMTTerm bvs e with
  | error e => rw [h_ok] at hsucc; exact hsucc.elim
  | ok tm =>
    -- `_typeChecks` proves the sort agreement; `typeOf_of_typeCheck` the fidelity.
    have htc := toSMTTerm_typeChecks huwf hψwf he hbwf h_ok hτ
    exact ⟨htc, Term.typeOf_of_typeCheck htc⟩

/-- **Top-level semantic correctness.** If `e` has simple type `τ`, then the term
    `tm` produced by `toSMTTerm` type-checks at the SMT encoding `smtTy` of `τ`,
    and its SMT denotation equals — transported across `tyDenote_eq_smtTyDenote` —
    the LExpr denotation of `e`.

    This is the semantic analog of `toSMTTerm_type_correct`: it wraps the mutual
    `toSMTTerm_sound` into a statement that assumes *only* `HasSimpType` plus the
    context/interpretation well-formedness and correspondence side conditions —
    no `h_ok`, no `hτ`, no `htA`, no `htc`. The two impossible would-be
    existentials are pattern matches returning `False`:
      • `toSMTTerm bvs e = .error _`   — impossible (totality).
      • `baseTyToTermType τ = none`     — impossible (`τ` is `MonoTyIsBase`),
    exactly as in `toSMTTerm_type_correct`; the sort encoding `hτ` is therefore
    *derived* here rather than assumed.

    The sort-check witness `htc` and the encoding proof `hτ` are bound as
    existentials in the conclusion. Binding `hτ` there (rather than referring to
    `baseTyToTermType τ` directly) is what keeps the `cast` well-formed under the
    `baseTyToTermType τ` match, letting the equality stay `cast`-based (as in
    `toSMTTerm_sound`) rather than an `HEq`. -/
theorem toSMTTerm_correct
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (huwf : FVarCtxWF Φ ufs) (hψwf : FVarCtxWF Ψ ufs)
    {Δ : List LMonoTy} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Ψ Δ e τ)
    {bvs : TermVarCtx} (hbwf : BVarCtxWF Δ bvs ufs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (hop : OpInterpConsistent opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (ufInterp : UFInterp) (smtEnv : SMTVarEnv)
    (hfenv : UFEnvCorresponds huwf fvarVal ufInterp)
    (hopenv : OpEnvCorresponds hψwf opInterp ufInterp)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv) :
    match toSMTTerm bvs e, baseTyToTermType τ with
    | .ok tm, some smtTy =>
      ∃ (hτ : baseTyToTermType τ = some smtTy)
        (htc : Term.typeCheck ufs bvs tm = some smtTy),
        cast (tyDenote_eq_smtTyDenote (HasSimpType_base he) hτ)
            (simpDenote opInterp fvarVal bvarVal e τ (HasSimpType_implies_HasTypeA he))
          = SMTTerm.denote ufInterp smtEnv tm smtTy htc
    | _, _ => False := by
  -- `τ` is base, so it is encodable — kills the `none` arm (as in `_type_correct`).
  obtain ⟨smtTy, hτ⟩ := MonoTyIsBase_baseTyToTermType (HasSimpType_base he)
  -- The encoder succeeds — kills the `.error` arm.
  have hsucc := toSMTTerm_succeeds huwf hψwf he hbwf
  -- `simp only` (not `rw`) rewrites the `baseTyToTermType τ` scrutinee: the
  -- existentially-bound `hτ` in the branch also mentions it, so match-congruence
  -- is needed to keep the motive type-correct.
  simp only [hτ]
  cases h_ok : toSMTTerm bvs e with
  | error e => rw [h_ok] at hsucc; exact hsucc.elim
  | ok tm =>
    -- `_typeChecks` supplies the witness `htc`; `_sound` supplies the equality at
    -- that witness (discharging encoder success `h_ok`, sort agreement `hτ`, and
    -- the LExpr typing `htA`).
    have htc := toSMTTerm_typeChecks huwf hψwf he hbwf h_ok hτ
    exact ⟨rfl, htc, toSMTTerm_sound huwf hψwf he hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv
      hfenv hopenv hbenv hτ (HasSimpType_base he) (HasSimpType_implies_HasTypeA he) h_ok htc⟩
