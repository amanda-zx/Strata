/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public import Strata.Languages.Core.Program
public import Strata.DL.SMT.DenoteTyped
public import Strata.DL.SMT.DenoteTypedProps
import all Strata.DL.SMT.DenoteTyped
import all Strata.DL.SMT.DenoteTypedProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.SMT.Term

/-!
# SMT encoding of the restricted `LExpr` fragment: typing, sort-correctness, and soundness

This file defines the SMT encoder for the SMT-encodable fragment of `LExpr` together with its
correctness theory. The fragment is carved out by the typing judgment `LExpr.HasSimpType` (with its
application-spine companion `LExpr.AppSpine`), which restricts expressions to base types (`bool`,
`int`, `string`, bitvectors), predefined Core operators (`LExpr.CoreOpHasType`), free variables,
user-defined functions, and quantifiers. The encoder `toSMTTerm` (with `appToSMTTerm` and the
non-recursive head `buildAppHead`) translates such an expression into an SMT `Term`.

Correctness is established by three theorems, each assuming only `HasSimpType` plus context
well-formedness: `toSMTTerm_type_correct` (the encoded term type-checks at the SMT encoding of the
source type), `toSMTTerm_succeeds` (the encoder never errors on a well-typed input), and
`toSMTTerm_correct` (its SMT denotation matches the `LExpr` denotation, transported across
`tyDenote_eq_smtTyDenote`). The bridge `HasSimpType_implies_HasTypeA` connects the restricted
judgment to Lambda's general `HasTypeA`.

The final sections model user-defined function and variable definitions (`FnDef`, `VarDef`) and the
SMT-side `define-fun` contract `IF.UFConsistent`, culminating in `UFConsistent_of_OpConsistent'` and
`UFConsistent_of_VarConsistent'`: given source-side consistency and correspondence, the encoded body
satisfies the `define-fun` guarantee.

Key definitions: `LExpr.HasSimpType`, `LExpr.AppSpine`, `toSMTTerm`, `FnDef`, `VarDef`,
`IF.UFConsistent`. Key results: `toSMTTerm_typeChecks`, `toSMTTerm_succeeds`, `toSMTTerm_sound`,
`toSMTTerm_correct`, `HasSimpType_implies_HasTypeA`, `UFConsistent_of_OpConsistent'`,
`UFConsistent_of_VarConsistent'`.
-/

open Core Lambda Imperative Strata.SMT Std
open Strata.SMT.DenoteTyped

variable {σ : SortInterp} [SortInterp.AllInhabited σ] {𝒜 : ArrayTheory}
set_option linter.unusedSectionVars false


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
  | intMod : CoreOpHasType (.numeric ⟨.int, .Mod⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
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

Relates a free variable's declared type to its argument/return decomposition, for function
application. -/

def collectArrowTy : LMonoTy → List LMonoTy × LMonoTy
  | .tcons "arrow" [ty1, ty2] =>
    let (atys, rty) := collectArrowTy ty2
    (ty1 :: atys, rty)
  | ty => ([], ty)

/-- Whether a Core operator name denotes a *predefined* operator — one with a
    `CoreOpHasType` signature (the LExpr-level typing fact the predefined `.op` head
    already uses). -/
def IsPredefinedOp (name : String) : Prop :=
  ∃ acc rty, LExpr.CoreOpHasType (CoreOp.ofString name) acc rty

/-! ## Typing judgment on `Expression.Expr` with n-ary free-variable application -/

abbrev FNameCtx := List (String × LMonoTy)
abbrev FVarCtx := FNameCtx

/-- A user-defined-function context: declared (name, full arrow type). Keyed
    for `.op` heads. -/
abbrev FnCtx := FNameCtx

mutual
inductive LExpr.HasSimpType (Φ : FVarCtx) (Ψ : FnCtx) : List LMonoTy → Expression.Expr → LMonoTy → Prop where
  | const c : MonoTyIsBase c.ty → HasSimpType Φ Ψ Δ (.const () c) c.ty
  | bvar i τ : Δ[i]? = some τ → MonoTyIsBase τ → HasSimpType Φ Ψ Δ (.bvar () i) τ
  -- An application node is typed by the application-spine judgment with no extra
  -- pending arguments; this subject is the `.app` tree the encoder peels.
  | app fn arg rty : LExpr.AppSpine Φ Ψ Δ (.app () fn arg) [] rty →
    HasSimpType Φ Ψ Δ (.app () fn arg) rty
  -- A bare free variable is a nullary application head.
  | fvarNullary f τ rty : LExpr.AppSpine Φ Ψ Δ (.fvar () f (some τ)) [] rty →
    HasSimpType Φ Ψ Δ (.fvar () f (some τ)) rty
  | ite c t τ e : HasSimpType Φ Ψ Δ c (.tcons "bool" []) → HasSimpType Φ Ψ Δ t τ →
    HasSimpType Φ Ψ Δ e τ → HasSimpType Φ Ψ Δ (.ite () c t e) τ
  | eq e1 e2 τ : MonoTyIsBase τ → HasSimpType Φ Ψ Δ e1 τ → HasSimpType Φ Ψ Δ e2 τ →
    HasSimpType Φ Ψ Δ (.eq () e1 e2) (.tcons "bool" [])
  -- The trigger `tr` is semantically inert (it guides SMT instantiation, not truth) and is discarded
  -- by the encoder, so it may be any expression that itself SMT-types to some base type `τ_tr`.
  | quant qty body k name tr τ_tr : MonoTyIsBase qty →
    HasSimpType Φ Ψ (qty :: Δ) tr τ_tr →
    HasSimpType Φ Ψ (qty :: Δ) body (.tcons "bool" []) →
    HasSimpType Φ Ψ Δ (.quant () k name (some qty) tr body) (.tcons "bool" [])

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
  -- User-defined-function head: an `.op` node whose symbol is not predefined.
  -- Its declared type decomposes into the pending argument types `acc` and a
  -- base return type, like the `.fvar` head, but it denotes through `opInterp`.
  | fnOp o oty acc rty : (o.name, oty) ∈ Ψ →
      ¬ IsPredefinedOp o.name →
      collectArrowTy oty = (acc, rty) →
      MonoTyIsBase rty →
      LExpr.AppSpine Φ Ψ Δ (.op () o (some oty)) acc rty
end

/-! ## LExpr denotation -/

noncomputable def simpTcInterp : Lambda.TyConstrInterp := fun _ _ => Unit

instance : Lambda.TyConstrInterp.AllInhabited simpTcInterp where
  inhabited := fun _ _ => ⟨()⟩

def simpTyVarVal : Lambda.TyVarVal := fun _ => .tcons "bool" []

abbrev BVarCtx := List LMonoTy

noncomputable def simpDenote
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {Δ : BVarCtx}
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (e : Expression.Expr) (τ : LMonoTy)
    (h : LExpr.HasTypeA Δ e τ)
    : Lambda.TyDenote simpTcInterp simpTyVarVal τ :=
  LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal e τ h




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

/-- `baseTyToTermType` only produces primitive base sorts, which are `WFSort` against any sort context. -/
theorem baseTyToTermType_wfSort {uss : USCtx} {ty : LMonoTy} {sty : TermType}
    (h : baseTyToTermType ty = some sty) : TermType.WFSort uss sty = true := by
  unfold baseTyToTermType at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [TermType.WFSort, TermType.isBase]

theorem baseTysToTermTypes_wfSort {uss : USCtx} {tys : List LMonoTy} {stys : List TermType}
    (h : baseTysToTermTypes tys = some stys) : stys.all (TermType.WFSort uss) = true := by
  induction tys generalizing stys with
  | nil => simp_all [baseTysToTermTypes]
  | cons ty rest ih =>
    simp only [baseTysToTermTypes, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨smtTy, hsty, tys, hrest, rfl⟩ := h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨baseTyToTermType_wfSort hsty, ih hrest⟩

/-- Translate a predefined `CoreOp` to its SMT `Op` builder + result sort. This is a MANY-TO-ONE
    map: several source ops may collapse onto one SMT operator.

    **Partiality-witness granularity (div-by-zero and friends).** SMT-LIB `div`/`mod` are TOTAL
    function symbols whose value at divisor `0` is unspecified-but-fixed within a model. That
    at-zero slice is represented by ONE `divByZero`/`modByZero : Int → Int` in `Term.denoteTyped` /
    `OpInterpConsistent` — shared across EVERY `Op.div`/`Op.mod` occurrence (two occurrences with
    equal arguments denote equally, by congruence). So the count
    of such witness functions scales with the number of PARTIAL SMT OPERATORS (here: 2 — `div`,
    `mod`), NOT with formula size or number of occurrences. A new partial SMT operator (e.g. a
    bitvector or real division) would need its own witness.

    **Constraint on the collapse.** When two DISTINCT source ops map to the SAME partial SMT
    operator, soundness requires their model interpretations to AGREE on the unspecified region.
    This is exactly why `Int.SafeDiv`/`Int.SafeMod` are out of scope: they would collapse onto the
    same `Op.div`/`Op.mod` as `Int.Div`/`Int.Mod`, but the factory leaves each independently
    unconstrained at divisor `0`, so a single shared `divByZero` cannot discharge both fields. Only
    add such a collapse if the shared-at-zero agreement is provable. -/
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
  | .numeric ⟨.int, .Div⟩ => some (.app Op.div, .int)
  | .numeric ⟨.int, .Mod⟩ => some (.app Op.mod, .int)
  | .numeric ⟨.int, .Neg⟩ => some (.app Op.neg, .int)
  | .numeric ⟨.int, .Lt⟩ => some (.app Op.lt, .bool)
  | .numeric ⟨.int, .Le⟩ => some (.app Op.le, .bool)
  | .numeric ⟨.int, .Gt⟩ => some (.app Op.gt, .bool)
  | .numeric ⟨.int, .Ge⟩ => some (.app Op.ge, .bool)
  | _ => none

/-- A name is not a predefined op exactly when the encoder has no builder for it. -/
theorem not_isPredefinedOp_iff {name : String} :
    ¬ IsPredefinedOp name ↔ corePredefinedOpToSMTOp (CoreOp.ofString name) = none := by
  rw [IsPredefinedOp]
  generalize CoreOp.ofString name = op
  constructor
  · -- No `CoreOpHasType` signature ⇒ no encoder builder. Case on `op`: predefined
    -- ops contradict the hypothesis (exhibit their signature); the rest are `none`.
    intro h
    cases op with
    | numeric nop =>
      obtain ⟨ty, kind⟩ := nop
      cases ty <;> cases kind <;>
        first
          | rfl
          | exact absurd ⟨_, _, by constructor⟩ h
    | bool kind => cases kind <;> exact absurd ⟨_, _, by constructor⟩ h
    | _ => rfl
  · -- Encoder has no builder ⇒ no `CoreOpHasType` signature: a witness pins `op` to
    -- a predefined op, contradicting `corePredefinedOpToSMTOp op = none`.
    rintro h ⟨acc, rty, hcot⟩
    cases hcot <;> simp_all [corePredefinedOpToSMTOp]


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
    node translates its argument eagerly and pushes the resulting `Term` into
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

/-- A `$__bv{n}` name never equals a fixed string whose character list does not
    begin with `'$'`. Used to discharge `no_reserved` for concrete UF-id lists whose
    ids are ordinary names (`"y"`, `"identity"`, …). -/
private theorem bv_str_ne_of_head {n : Nat} {s : String}
    (hs : s.toList.head? ≠ some '$') : s!"$__bv{n}" ≠ s := by
  intro h
  apply hs
  have h1 : ("$__bv" ++ toString n).toList = s.toList := congrArg String.toList h
  rw [String.toList_append] at h1
  -- LHS list is `'$' :: …`, so its head is `some '$'`; rewrite by `h1`.
  rw [← h1]; rfl

/-- SMT-side well-formedness of a UF context: its symbol names are distinct and none collides with a
    reserved `$__bv{n}` binder id. Both fields speak about `ufs` alone, so they are factored out of
    the source-context correspondence judgments (`FNameCtxWF`, `BVarCtxWF`). -/
structure UFCtxWF (ufs : UFCtx) : Prop where
  /-- UF ids are unique — the faithful model of SMT-LIB's rule that a name may not be declared twice.
      Since `ufs` keys interpretations on the full `(id, args, out)` struct, absent this a single name
      could carry two differently-typed UFs with independent `ufInterp` values, impossible for a real
      solver. -/
  uf_nodup : (ufs.map (·.id)).Nodup
  /-- No UF id collides with a reserved bound-variable name `$__bv{n}`; discharges the anti-shadowing
      side condition on the encoder's UF applications. -/
  no_reserved : ∀ n : Nat, s!"$__bv{n}" ∉ ufs.map (·.id)

structure BVarCtxWF (Δ : BVarCtx) (bvs : TermVarCtx) : Prop where
  len_eq : Δ.length = bvs.length
  ty_eq : ∀ i (hi : i < Δ.length), baseTyToTermType Δ[i] = some (bvs[i]'(by omega)).ty
  id_scheme : ∀ i (hi : i < bvs.length), (bvs[i]'hi).id = s!"$__bv{bvs.length - 1 - i}"

/-- Any UF-symbol id is free of capture by the bound-variable context: `bvs` ids
    all follow the `$__bv{…}` scheme (`id_scheme`), which no `ufs` id matches
    (`no_reserved`). This is what discharges the anti-shadowing side condition of
    `Term.typeCheck` on the encoder's UF applications. -/
theorem BVarCtxWF.uf_id_not_captured {Δ : BVarCtx} {bvs : TermVarCtx} {ufs : UFCtx}
    (hbwf : BVarCtxWF Δ bvs) (hufwf : UFCtxWF ufs)
    {name : String} (h_mem : name ∈ ufs.map (·.id)) :
    name ∉ bvs.map (·.id) := by
  intro hbv
  rw [List.mem_map] at hbv
  obtain ⟨v, hv_mem, hv_id⟩ := hbv
  rw [List.mem_iff_getElem] at hv_mem
  obtain ⟨i, hi, hvi⟩ := hv_mem
  have hid := hbwf.id_scheme i hi
  rw [hvi] at hid
  -- `name = v.id = "$__bv{bvs.length - 1 - i}"`, contradicting `no_reserved`.
  rw [← hv_id, hid] at h_mem
  exact hufwf.no_reserved _ h_mem

/-- The bound-variable ids follow the position-determined `$__bv{…}` scheme, so
    they are pairwise distinct; hence looking up `bvs[i]` by its name returns
    `bvs[i]` itself (it is the unique — hence innermost — binder of that name).
    This is what the `.var` type-check rule needs on the encoder's output. -/
theorem BVarCtxWF.find?_id_self {Δ : BVarCtx} {bvs : TermVarCtx}
    (hbwf : BVarCtxWF Δ bvs) (i : Nat) (hi : i < bvs.length) :
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
    the `ufs` data and can be used to build a `cast`. -/
def lookupUF (ufs : UFCtx) (name : String) : Option UF :=
  ufs.find? (·.id == name)

theorem lookupUF_mem {ufs : UFCtx} {name : String} {uf : UF}
    (h : lookupUF ufs name = some uf) : uf ∈ ufs :=
  List.mem_of_find?_eq_some h

theorem lookupUF_id {ufs : UFCtx} {name : String} {uf : UF}
    (h : lookupUF ufs name = some uf) : uf.id = name := by
  have := List.find?_some h; simpa using this

/-- Well-formedness of a free-variable context against a UF context: every declared name resolves —
    via `lookupUF` — to a *specific* UF whose signature is the SMT encoding of the fvar's collected
    arrow type. The signature is thus available as data, mirroring how `BVarCtxWF` exposes `bvs[i].ty`.

    The relational layer needs only per-name *resolution* (below); uniqueness of the `ufs` ids
    (which keeps `lookupUF` canonical) lives in `UFCtxWF`. -/
structure FNameCtxWF (Φ : FNameCtx) (ufs : UFCtx) : Prop where
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

/-- Existential view of `FNameCtxWF`: recovers the encoded signature and its membership in `ufs`
    from the lookup-based fields, for consumers that only need "some matching UF exists". -/
theorem FNameCtxWF.fvar_has_uf {Φ : FVarCtx} {ufs : UFCtx} (hwf : FNameCtxWF Φ ufs)
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
    (h : Term.typeCheckArgs ⟨[], ufs, Γ⟩ smtArgs smtTys = true) : smtArgs.length = smtTys.length := by
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
    (h : Term.typeCheckArgs ⟨[], ufs, Γ⟩ smtArgs [ty1, ty2] = true) :
    ∃ t1 t2, smtArgs = [t1, t2] ∧
      Term.typeCheck ⟨[], ufs, Γ⟩ t1 = .ok ty1 ∧ Term.typeCheck ⟨[], ufs, Γ⟩ t2 = .ok ty2 := by
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
    (h : Term.typeCheckArgs ⟨[], ufs, Γ⟩ smtArgs [ty1] = true) :
    ∃ t1, smtArgs = [t1] ∧ Term.typeCheck ⟨[], ufs, Γ⟩ t1 = .ok ty1 := by
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
    (h_tc_args : Term.typeCheckArgs ⟨[], ufs, bvs⟩ sargs smtArgTys = true)
    (h_build : buildAppHead (.fvar () f (some fty)) sargs = .ok tm) :
    Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty := by
  simp only [buildAppHead, hcollect, h_smtRty, h_smtArgTys] at h_build
  injection h_build with h_build; subst h_build
  simp only [Term.typeCheck, h_uf_mem, h_no_capture, h_tc_args,
    baseTysToTermTypes_wfSort h_smtArgTys, baseTyToTermType_wfSort h_smtRty,
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
    (h_tc_args : Term.typeCheckArgs ⟨[], ufs, bvs⟩ sargs smtArgTys = true)
    (h_build : buildAppHead (.op () o (some oty)) sargs = .ok tm) :
    Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty := by
  simp only [buildAppHead, h_not_pre, hcollect, h_smtRty, h_smtArgTys] at h_build
  injection h_build with h_build; subst h_build
  simp only [Term.typeCheck, h_uf_mem, h_no_capture, h_tc_args,
    baseTysToTermTypes_wfSort h_smtArgTys, baseTyToTermType_wfSort h_smtRty,
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
private theorem HasSimpType_base {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {τ : LMonoTy} (he : LExpr.HasSimpType Φ Ψ Δ e τ) : LExpr.MonoTyIsBase τ := by
  match he with
  | .const c hbase => exact hbase
  | .bvar i _ hlook hbase => exact hbase
  | .app fn arg rty hspine => exact AppSpine_base hspine
  | .fvarNullary f τ rty hspine => exact AppSpine_base hspine
  | .ite c t _ e_ hc ht hee => exact HasSimpType_base ht
  | .eq e1 e2 τ hbase he1 he2 => exact .bool
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody => exact .bool
private theorem AppSpine_base {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
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


/-- **Sort-correctness of the predefined-operator (`.op`) head**, factored out of
    `appSpine_typeChecks`'s `.op` arm. Each permitted Core operator is dispatched by
    the `cases` on `CoreOpHasType` below (unary vs. binary shape); the mutual
    sort-correctness proof calls this directly, so adding a new predefined operator
    touches only this lemma. A leaf (no recursive call), so
    it lives outside the `mutual` block and consumes no context/WF hypotheses. -/
private theorem predefinedOp_typeChecks
    {o : CoreLParams.Identifier} {oty : LMonoTy} {acc : List LMonoTy} {rty : LMonoTy}
    (hop : LExpr.CoreOpHasType (CoreOp.ofString o.name) acc rty)
    {ufs : UFCtx} {bvs : TermVarCtx} {accSmt : List TermType} {accTms : List Term}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (h_ok : appToSMTTerm bvs (.op () o (some oty)) accTms = .ok tm)
    (hacc : baseTysToTermTypes acc = some accSmt) (hrty : baseTyToTermType rty = some smtRty)
    : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty := by
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
      simp [Term.typeCheck, h1, bind, Except.bind]
    case intAdd | intSub | intMul | intDiv | intMod
       | intLt | intLe | intGt
       | intGe | boolAnd | boolOr | boolImplies | boolEquiv =>
        simp only [baseTysToTermTypes, baseTyToTermType, bind, Option.bind] at hacc
        injection hacc with hacc; subst hacc
        obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
        simp only [baseTyToTermType, Option.some.injEq] at hrty; subst hrty
        simp only [buildAppHead, hcop, corePredefinedOpToSMTOp] at h_ok
        injection h_ok with h_ok; subst h_ok
        simp [Term.typeCheck, h1, h2, bind, Except.bind]
mutual
theorem toSMTTerm_typeChecks
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Ψ Δ e τ)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx} {smtTy : TermType} {tm : Term}
    (hufwf : UFCtxWF ufs)
    -- ── correspondence (source ↔ target): encoding (term, type), then typing contexts ──
    (h_ok : toSMTTerm bvs e = .ok tm)
    (hτ : baseTyToTermType τ = some smtTy)
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) (hbwf : BVarCtxWF Δ bvs)
    : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtTy := by
  match he with
  | .const c hbase =>
    cases c <;>
      simp [toSMTTerm, LConst.ty, LMonoTy.int, LMonoTy.bool, LMonoTy.string,
        baseTyToTermType] at h_ok hτ ⊢ <;>
      (try subst h_ok) <;> (try subst hτ) <;>
      simp_all [Term.typeCheck, TermPrim.typeOf, TermType.isBase]
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
      exfalso
      refine hnotmem ⟨hbwf.find?_id_self i hi, ?_⟩
      have hi_Δ : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
      have hΔi_eq : Δ[i] = τ := (List.getElem?_eq_some_iff.mp hlook).2
      have hty_eq := hbwf.ty_eq i hi_Δ
      rw [hΔi_eq] at hty_eq
      exact baseTyToTermType_wfSort hty_eq
  | .app fn arg rty hspine =>
    -- The whole application is typed by the spine judgment with no pending args;
    -- `toSMTTerm (.app ..)` folds into `appToSMTTerm (.app ..) []` (empty acc).
    have h_ok' : appToSMTTerm bvs (.app () fn arg) [] = .ok tm := by
      rw [appToSMTTerm]; rw [toSMTTerm] at h_ok; exact h_ok
    exact appSpine_typeChecks hspine (by simp [Term.typeCheckArgs]) hufwf h_ok' rfl hτ huwf hψwf hbwf
  | .fvarNullary f τ_f rty hspine =>
    have h_ok' : appToSMTTerm bvs (.fvar () f (some τ_f)) [] = .ok tm := by
      rw [toSMTTerm] at h_ok; exact h_ok
    exact appSpine_typeChecks hspine (by simp [Term.typeCheckArgs]) hufwf h_ok' rfl hτ huwf hψwf hbwf
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
          have ihc := toSMTTerm_typeChecks (smtTy := .bool) hc hufwf hc_ok
            (by simp [baseTyToTermType]) huwf hψwf hbwf
          have iht := toSMTTerm_typeChecks ht hufwf ht_ok hτ huwf hψwf hbwf
          have ihe := toSMTTerm_typeChecks hee hufwf he_ok hτ huwf hψwf hbwf
          -- The ite annotation is `Term.typeOf tt`; the checker requires it to
          -- equal the then-branch type, which the typeOf/typeCheck agreement supplies.
          have htt : Term.typeOf tt = smtTy := Term.typeOf_of_typeCheck iht
          rw [ihc, iht, ihe, htt]; simp [bind, Except.bind]
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
            Term.typeCheck ⟨[], ufs, bvs⟩ t1 = .ok sty :=
          fun _ h => toSMTTerm_typeChecks he1 hufwf h1_ok h huwf hψwf hbwf
        have key2 : ∀ sty, baseTyToTermType τ' = some sty →
            Term.typeCheck ⟨[], ufs, bvs⟩ t2 = .ok sty :=
          fun _ h => toSMTTerm_typeChecks he2 hufwf h2_ok h huwf hψwf hbwf
        simp only [Term.typeCheck]
        cases hbase with
        | bool => rw [key1 .bool (by simp [baseTyToTermType]), key2 .bool (by simp [baseTyToTermType])]; simp [bind, Except.bind]
        | int => rw [key1 .int (by simp [baseTyToTermType]), key2 .int (by simp [baseTyToTermType])]; simp [bind, Except.bind]
        | string =>
          rw [key1 .string (by simp [baseTyToTermType]), key2 .string (by simp [baseTyToTermType])]; simp [bind, Except.bind]
        | bitvec =>
          rename_i n
          rw [key1 (.bitvec n) (by simp [baseTyToTermType]), key2 (.bitvec n) (by simp [baseTyToTermType])]
          simp [bind, Except.bind]
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody =>
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
          (⟨"$__bv" ++ (bvs.length).repr, smtQTy⟩ :: bvs) := by
        refine ⟨?_, ?_, ?_⟩
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
      have ihbody := toSMTTerm_typeChecks (smtTy := .bool) hbody
        hufwf hbody_ok (by simp [baseTyToTermType]) huwf hψwf hbwf'
      simp only [hstr, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append]
      rw [ihbody]; simp [baseTyToTermType_wfSort hqty_eq, Term.wfTriggers, bind, Except.bind]
  termination_by structural he

/-- Spine correctness. If `AppSpine Φ Ψ Δ e acc rty` and the already-translated
    accumulator `accTms` type-checks against the SMT encoding `accSmt` of `acc`,
    then `appToSMTTerm bvs e accTms` produces a term of sort `smtRty`.

    Structural on the `AppSpine` derivation — its `app` constructor recurses on the
    function position exactly as `appToSMTTerm` does, so the invariant about the
    accumulator threads through without any reverse-induction bookkeeping. -/
theorem appSpine_typeChecks
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx} {accSmt : List TermType} {accTms : List Term}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (hufwf : UFCtxWF ufs)
    -- ── correspondence (source ↔ target): encoding (term, types), then typing contexts ──
    (h_ok : appToSMTTerm bvs e accTms = .ok tm)
    (hacc : baseTysToTermTypes acc = some accSmt) (hrty : baseTyToTermType rty = some smtRty)
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) (hbwf : BVarCtxWF Δ bvs)
    : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty := by
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
      have h_argt := toSMTTerm_typeChecks harg hufwf h_arg_ok h_saty huwf hψwf hbwf
      have hacc' : baseTysToTermTypes (aty :: acc') = some (saty :: accSmt) := by
        simp only [baseTysToTermTypes, h_saty, hacc, bind, Option.bind]
      have h_acc_tc' : Term.typeCheckArgs ⟨[], ufs, bvs⟩ (argt :: accTms) (saty :: accSmt) = true := by
        simp only [Term.typeCheckArgs, h_argt]
        simp [h_acc_tc, BEq.beq]
      exact appSpine_typeChecks hrest h_acc_tc' hufwf h_ok hacc' hrty huwf hψwf hbwf
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
      hbwf.uf_id_not_captured hufwf (List.mem_map_of_mem h_uf_mem)
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
      hbwf.uf_id_not_captured hufwf (List.mem_map_of_mem h_uf_mem)
    exact buildAppHead_op_typeChecks hcollect (not_isPredefinedOp_iff.mp hnpre)
      h_smtArgTys h_smtRty' h_uf_mem h_no_capture h_acc_tc h_ok'
  | .op o oty acc' rty hop hcollect =>
    -- Predefined-operator head: handled by the standalone `predefinedOp_typeChecks`.
    -- A leaf (no recursive call), so extraction keeps new operators out of the
    -- mutual sort-correctness proof.
    exact predefinedOp_typeChecks hop h_acc_tc h_ok hacc hrty
  termination_by structural hspine
end

/-! ## Bridge: `HasSimpType` → `HasTypeA` -/

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
theorem HasSimpType_implies_HasTypeA {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
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
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody =>
    -- trigger's `HasTypeA` from its own `HasSimpType`
    exact .quant (HasSimpType_implies_HasTypeA htr) (HasSimpType_implies_HasTypeA hbody)

theorem AppSpine_implies_HasTypeA {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
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

omit [SortInterp.AllInhabited σ] in
/-- The LExpr-side `TyDenote` and the SMT-side `SMTTyDenote` agree on base types. -/
theorem tyDenote_eq_smtTyDenote {τ : LMonoTy} {smtTy : TermType}
    (hbase : LExpr.MonoTyIsBase τ) (h : baseTyToTermType τ = some smtTy) :
    Lambda.TyDenote simpTcInterp simpTyVarVal τ = TermType.denoteTyped σ 𝒜 smtTy := by
  cases hbase with
  | bool => simp [baseTyToTermType] at h; subst h; rfl
  | int => simp [baseTyToTermType] at h; subst h; rfl
  | string => simp [baseTyToTermType] at h; subst h; rfl
  | bitvec => simp [baseTyToTermType] at h; subst h; rfl

/-- Consistency of the operator interpretation with SMT semantics.
    Each primitive Core operator, when applied in the `simpDenote` world, computes
    the same function as the corresponding SMT operator node's `Term.denoteTyped`. -/
structure OpInterpConsistent (divByZero modByZero : Int → Int)
    (opInterp : Lambda.OpInterp simpTcInterp) : Prop where
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
        = (fun x y : Int => if y = 0 then divByZero x else x / y)
  mod_ : ∀ name, CoreOp.ofString name = .numeric ⟨.int, .Mod⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => if y = 0 then modByZero x else x % y)
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
    {Δ : BVarCtx} {bvs : TermVarCtx}
    (hwf : BVarCtxWF Δ bvs)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (smtEnv : VarEnv σ 𝒜) : Prop :=
  ∀ i (τ : LMonoTy) (hbase : LExpr.MonoTyIsBase τ) (hlook : Δ[i]? = some τ),
    let hi : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
    let hbvs : i < bvs.length := hwf.len_eq ▸ hi
    let hty : baseTyToTermType τ = some (bvs[i]'hbvs).ty := by
      have := hwf.ty_eq i hi
      rw [(List.getElem?_eq_some_iff.mp hlook).2] at this
      exact this
    cast (tyDenote_eq_smtTyDenote (σ := σ) hbase hty) (bvarVal.get i hlook)
      = smtEnv (bvs[i]'hbvs)

/-- Extension lemma for `BVarEnvCorresponds`: extending both the LExpr bound-var
    valuation (with a fresh value `x`) and the SMT environment (agreeing with `x`
    on the new variable `v` and with the old env elsewhere) preserves the
    correspondence. Because `v` follows the `$__bv{bvs.length}` scheme it never
    collides with an existing `bvs` entry, so the "elsewhere" clause is total. -/
theorem BVarEnvCorresponds_cons
    {Δ : BVarCtx} {bvs : TermVarCtx}
    {hbwf : BVarCtxWF Δ bvs}
    {bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ}
    {smtEnv : VarEnv σ 𝒜}
    (henv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    {qty : LMonoTy} {v : TermVar}
    (hbase : LExpr.MonoTyIsBase qty)
    (hty : baseTyToTermType qty = some v.ty)
    (x : Lambda.TyDenote simpTcInterp simpTyVarVal qty)
    {smtEnv' : VarEnv σ 𝒜}
    (hnew : smtEnv' v = cast (tyDenote_eq_smtTyDenote (σ := σ) hbase hty) x)
    (hold : ∀ w, w ≠ v → smtEnv' w = smtEnv w)
    (hbwf' : BVarCtxWF (qty :: Δ) (v :: bvs))
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
    (under `simpTcInterp`/`simpTyVarVal`) equals the SMT-side `UF.denoteTyped'` at
    the corresponding SMT types. This is the curried-function-level analog of
    `tyDenote_eq_smtTyDenote` (which handles base types). -/
private theorem tyDenote_arrow_eq_UFDenote'
    {acc : List LMonoTy} {accSmt : List TermType} {rty : LMonoTy} {smtRty : TermType}
    (hacc : baseTysToTermTypes acc = some accSmt)
    (hrty : baseTyToTermType rty = some smtRty) :
    Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow rty acc)
      = UF.denoteTyped' σ 𝒜 accSmt smtRty := by
  induction acc generalizing accSmt with
  | nil =>
    simp [baseTysToTermTypes] at hacc; subst hacc
    simp [UF.denoteTyped', List.foldr]
    exact tyDenote_eq_smtTyDenote (σ := σ) (baseTyToTermType_isBase hrty) hrty
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
        simp only [List.foldr, UF.denoteTyped']
        -- TyDenote ... (arrow aty (foldr arrow rty rest))
        --   = SortDenote simpTcInterp (substTyVars simpTyVarVal (arrow aty ...))
        --   = SortDenote simpTcInterp (arrow ...) → SortDenote simpTcInterp (...)
        --   = TermType.denoteTyped σ 𝒜 smtAty → UF.denoteTyped' smtRest smtRty
        -- `TyDenote` on an arrow splits into a function type (definitional).
        have harrow : Lambda.TyDenote simpTcInterp simpTyVarVal
              (LMonoTy.arrow aty (List.foldr LMonoTy.arrow rty rest))
            = (Lambda.TyDenote simpTcInterp simpTyVarVal aty →
               Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow rty rest)) := rfl
        -- The argument type: base, so `TyDenote = SMTTyDenote`.
        have h_aty : Lambda.TyDenote simpTcInterp simpTyVarVal aty = TermType.denoteTyped σ 𝒜 smtAty :=
          tyDenote_eq_smtTyDenote (σ := σ) (baseTyToTermType_isBase haty) haty
        -- The tail: by IH on `rest`.
        have h_rest : Lambda.TyDenote simpTcInterp simpTyVarVal
              (List.foldr LMonoTy.arrow rty rest) = UF.denoteTyped' σ 𝒜 smtRest smtRty := ih hrest
        rw [harrow, h_aty, h_rest]

/-- Correspondence between LExpr free variable valuation and n-ary UF interpretation.
    For each free variable `(name, τ)` declared in `Φ`, the LExpr-side curried denotation
    (via `fvarVal`) equals (under cast) the SMT-side curried UF denotation (via `ufInterp`).

    The LExpr side denotes a free variable of arrow type `τ = a₁ → a₂ → ⋯ → aₙ → rty`
    as `fvarVal ⟨name, ()⟩ (τ.substTyVars simpTyVarVal)`, which has Lean type
    `SortDenote simpTcInterp (τ.substTyVars simpTyVarVal)` ≅ `TermType.denoteTyped σ 𝒜 sty₁ → ⋯ → TermType.denoteTyped σ 𝒜 rty`.

    The SMT side denotes it as `ufInterp ⟨name, smtArgTys, smtRty⟩`, which has type
    `UF.denoteTyped' smtArgTys smtRty` = `TermType.denoteTyped σ 𝒜 sty₁ → ⋯ → TermType.denoteTyped σ 𝒜 smtRty`.

    These coincide under `tyDenote_eq_smtTyDenote` on each base constituent. -/
def FVarEnvCorresponds
    {Φ : FVarCtx} {ufs : UFCtx}
    (hwf : FNameCtxWF Φ ufs)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (ufInterp : UFInterp σ 𝒜) : Prop :=
  ∀ (name : String) (τ : LMonoTy) (hmem : (name, τ) ∈ Φ),
    -- `lookupUF` reads the declared signature out of `ufs` as **data**, exactly as
    -- `BVarEnvCorresponds` reads `bvs[i]` out of the bound-variable context:
    -- `FNameCtxWF`'s `args_eq`/`out_eq` give the encoding equalities directly, which
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
    interpretation, for user-defined-function `.op` heads. Like `FVarEnvCorresponds`,
    but the LExpr side denotes through `opInterp` (an `.op` node denotes as
    `opInterp o.name (ty.substTyVars vt)`). -/
def FnEnvCorresponds
    {Ψ : FnCtx} {ufs : UFCtx}
    (hwf : FNameCtxWF Ψ ufs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (ufInterp : UFInterp σ 𝒜) : Prop :=
  ∀ (name : String) (τ : LMonoTy) (hmem : (name, τ) ∈ Ψ),
    -- `lookupUF` reads the declared signature out of `ufs` as **data**, exactly as in
    -- `FVarEnvCorresponds`. Here the LExpr-side valuation is `opInterp`: an `.op`
    -- node denotes through `opInterp` (keyed on the bare name string).
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

omit [SortInterp.AllInhabited σ] in
/-- `Term.denoteTyped` for a variable is HEq to the environment lookup. -/
private theorem SMTTerm_denote_var_heq {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) {divByZero modByZero : Int → Int}
    (v : TermVar) (τ : TermType) (htc : Term.typeCheck ⟨[], ufs, Γ⟩ (.var v) = .ok τ) :
    HEq (Term.denoteTyped ufInterp env divByZero modByZero (.var v) τ htc) (env v) := by
  unfold Term.denoteTyped
  obtain ⟨hmem, heq⟩ := Term.typeCheck_var_inv htc
  simp only
  exact cast_heq _ _

/-- Unfolding lemma for `Term.denoteTyped` on `ite`. -/
private noncomputable def SMTTerm_denote_ite {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) {divByZero modByZero : Int → Int}
    (c t e : Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck ⟨[], ufs, Γ⟩ (.app (.core .ite) [c, t, e] rty) = .ok τ) :
    Term.denoteTyped ufInterp env divByZero modByZero (.app (.core .ite) [c, t, e] rty) τ htc =
      bif Term.denoteTyped ufInterp env divByZero modByZero c .bool (Term.typeCheck_ite_inv htc).1
      then Term.denoteTyped ufInterp env divByZero modByZero t τ (Term.typeCheck_ite_inv htc).2.1
      else Term.denoteTyped ufInterp env divByZero modByZero e τ (Term.typeCheck_ite_inv htc).2.2 := by
  simp only [Term.denoteTyped]
  obtain ⟨hc, ht, he⟩ := Term.typeCheck_ite_inv htc
  rfl

/-- Unfolding lemma for `Term.denoteTyped` on `eq`. -/
private noncomputable def SMTTerm_denote_eq_unfold {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) {divByZero modByZero : Int → Int}
    (t1 t2 : Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck ⟨[], ufs, Γ⟩ (.app (.core .eq) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env divByZero modByZero (.app (.core .eq) [t1, t2] rty) τ htc =
      cast (by rw [(Term.typeCheck_eq_inv htc).2.2.2]) (@decide
        (Term.denoteTyped ufInterp env divByZero modByZero t1 (Term.typeCheck_eq_inv htc).1 (Term.typeCheck_eq_inv htc).2.1
         = Term.denoteTyped ufInterp env divByZero modByZero t2 (Term.typeCheck_eq_inv htc).1 (Term.typeCheck_eq_inv htc).2.2.1)
        (Classical.propDecidable _)) := by
  simp only [Term.denoteTyped]
  obtain ⟨τ', h1, h2, heq⟩ := Term.typeCheck_eq_inv htc
  rfl

/-- Inversion for a UF application: recovers the type-check facts for the
    argument list and the output type. -/
private theorem tc_uf_inv {Γ : List TermVar} {ufs : UFCtx} {uf : UF}
    {args : List Term} {rty τ : TermType}
    (h : Term.typeCheck ⟨[], ufs, Γ⟩ (.app (.core (.uf uf)) args rty) = .ok τ) :
    Term.typeCheckArgs ⟨[], ufs, Γ⟩ args uf.args = true ∧ τ = uf.out := by
  simp only [Term.typeCheck] at h
  split at h <;> (try split at h) <;> simp_all

omit [SortInterp.AllInhabited σ] in
/-- `Term.denoteTyped` is invariant (up to `HEq`) under a change of the type index
    when the two indices are provably equal. -/
private theorem SMTTerm_denote_cast {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) {divByZero modByZero : Int → Int}
    (tm : Term) (τ τ' : TermType)
    (h : Term.typeCheck ⟨[], ufs, Γ⟩ tm = .ok τ) (h' : Term.typeCheck ⟨[], ufs, Γ⟩ tm = .ok τ')
    (heq : τ = τ') :
    HEq (Term.denoteTyped ufInterp env divByZero modByZero tm τ h) (Term.denoteTyped ufInterp env divByZero modByZero tm τ' h') := by
  subst heq; exact heq_of_eq (congrArg (Term.denoteTyped ufInterp env divByZero modByZero tm τ) (proof_irrel h h'))

/-- Unfolding lemma for `Term.denoteTyped` on a UF application, exposing the
    `UF.applyDenoteTyped'` of the head interpretation to the denoted arguments. -/
private noncomputable def SMTTerm_denote_uf_unfold {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) {divByZero modByZero : Int → Int}
    (uf : UF) (args : List Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck ⟨[], ufs, Γ⟩ (.app (.core (.uf uf)) args rty) = .ok τ) :
    Term.denoteTyped ufInterp env divByZero modByZero (.app (.core (.uf uf)) args rty) τ htc =
      cast (by rw [(tc_uf_inv htc).2])
        (UF.applyDenoteTyped' σ 𝒜 uf.args uf.out (ufInterp uf)
          (Term.denoteTypedArgs ufInterp env divByZero modByZero args uf.args (tc_uf_inv htc).1)) := by
  simp only [Term.denoteTyped]

/-- LHS reduction for a **unary** operator head: the LExpr op interpretation,
    cast to `UF.denoteTyped' [sa] sr` and applied to one argument value, reduces to the
    semantic function `g` applied to that value — given the op-interpretation
    consistency equation. Encapsulates the `simpDenote`/`denote_op` unfolding and
    the `cast`/`subst`/`HEq` plumbing shared by every unary op arm. -/
private theorem applyUF1_of_cons
    {Δ : BVarCtx}
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    {o : CoreLParams.Identifier} {a r : LMonoTy} {sa sr : TermType}
    {g : TermType.denoteTyped σ 𝒜 sa → TermType.denoteTyped σ 𝒜 sr}
    (htA : LExpr.HasTypeA Δ (.op () o (some (.tcons "arrow" [a, r])))
      (List.foldr LMonoTy.arrow r [a]))
    (hacc : baseTysToTermTypes [a] = some [sa]) (hrty : baseTyToTermType r = some sr)
    (hcons : HEq (opInterp o.name ((LMonoTy.tcons "arrow" [a, r]).substTyVars simpTyVarVal)) g)
    (v : TermType.denoteTyped σ 𝒜 sa) :
    UF.applyDenoteTyped' σ 𝒜 [sa] sr (cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
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
    {Δ : BVarCtx}
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    {o : CoreLParams.Identifier} {a1 a2 r : LMonoTy} {sa1 sa2 sr : TermType}
    {g : TermType.denoteTyped σ 𝒜 sa1 → TermType.denoteTyped σ 𝒜 sa2 → TermType.denoteTyped σ 𝒜 sr}
    (htA : LExpr.HasTypeA Δ (.op () o (some (.tcons "arrow" [a1, .tcons "arrow" [a2, r]])))
      (List.foldr LMonoTy.arrow r [a1, a2]))
    (hacc : baseTysToTermTypes [a1, a2] = some [sa1, sa2])
    (hrty : baseTyToTermType r = some sr)
    (hcons : HEq (opInterp o.name
      ((LMonoTy.tcons "arrow" [a1, .tcons "arrow" [a2, r]]).substTyVars simpTyVarVal)) g)
    (v1 : TermType.denoteTyped σ 𝒜 sa1) (v2 : TermType.denoteTyped σ 𝒜 sa2) :
    UF.applyDenoteTyped' σ 𝒜 [sa1, sa2] sr (cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
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

/-- **Soundness of the predefined-operator (`.op`) head**, factored out of
    `appToSMTTerm_sound`'s `.op` arm. Each permitted Core operator is handled by one
    `cases` arm below; the mutual soundness proof calls this lemma directly, so
    adding a new predefined operator touches only this lemma. This arm makes
    no recursive call (predefined ops are leaves of the spine), so it is a plain
    standalone theorem outside the `mutual` block. It consumes none of the context /
    correspondence hypotheses (`Φ`/`Ψ`/`FNameCtxWF`/`*EnvCorresponds`): a predefined
    op resolves via `corePredefinedOpToSMTOp`, and its consistency comes entirely
    from `OpInterpConsistent` (`hop`). -/
private theorem predefinedOp_sound
    {Δ : BVarCtx}
    {o : CoreLParams.Identifier} {oty : LMonoTy} {acc : List LMonoTy} {rty : LMonoTy}
    (hopty : LExpr.CoreOpHasType (CoreOp.ofString o.name) acc rty)
    (hcol : collectArrowTy oty = (acc, rty))
    (htA : LExpr.HasTypeA Δ (.op () o (some oty)) (List.foldr LMonoTy.arrow rty acc))
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    {ufs : UFCtx} {bvs : TermVarCtx} {accTms : List Term} {accSmt : List TermType}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (h_ok : appToSMTTerm bvs (.op () o (some oty)) accTms = .ok tm)
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty)
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜)
    (accArgVals : HList (TermType.denoteTyped σ 𝒜) accSmt)
    (h_acc_denote : Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero accTms accSmt h_acc_tc = accArgVals)
    (hacc : baseTysToTermTypes acc = some accSmt) (hrty : baseTyToTermType rty = some smtRty)
    : Term.denoteTyped ufInterp smtEnv divByZero modByZero tm smtRty htc
        = UF.applyDenoteTyped' σ 𝒜 accSmt smtRty
            (cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
              (simpDenote opInterp fvarVal bvarVal (.op () o (some oty))
                (List.foldr LMonoTy.arrow rty acc) htA))
            accArgVals := by
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) .nil := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF1_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.neg o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.neg [t1] .int) .int htc
          = cast (by rw [(Term.typeCheck_intUn_inv htc).2])
              (-(Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intUn_inv htc).1)) := by
        simp only [Term.denoteTyped]
        obtain ⟨ht, heq⟩ := Term.typeCheck_intUn_inv htc
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_intUn_inv htc).1 h1]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool h1) .nil := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF1_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.not o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app (.core .not) [t1] .bool) .bool htc
          = cast (by rw [(Term.typeCheck_not_inv htc).2])
              (!(Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool (Term.typeCheck_not_inv htc).1)) := by
        simp only [Term.denoteTyped]
        obtain ⟨ht, heq⟩ := Term.typeCheck_not_inv htc
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_not_inv htc).1 h1]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.add o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.add [t1, t2] .int) .int htc
          = cast (by rw [(Term.typeCheck_intBin_inv htc (.inl rfl)).2.2]) ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).1) + (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).2.1)) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_intBin_inv htc (.inl rfl)).1 h1, proof_irrel (Term.typeCheck_intBin_inv htc (.inl rfl)).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.sub o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.sub [t1, t2] .int) .int htc
          = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.2]) ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).1) - (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.1)) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).1 h1, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.mul o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.mul [t1, t2] .int) .int htc
          = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.2]) ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).1) * (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1)) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).1 h1, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.div o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.div [t1, t2] .int) .int htc
          = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2])
              (if (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1) = 0
               then divByZero (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1)
               else (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1) / (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1)) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1 h1, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.mod_ o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.mod [t1, t2] .int) .int htc
          = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2])
              (if (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1) = 0
               then modByZero (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1)
               else (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1) % (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1)) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1 h1, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.lt o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.lt [t1, t2] .bool) .bool htc
          = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.2]) (decide ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).1) < (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.1))) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).1 h1, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.le o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.le [t1, t2] .bool) .bool htc
          = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inl rfl)).2.2]) (decide ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).1) ≤ (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).2.1))) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_intCmp_inv htc (.inl rfl)).1 h1, proof_irrel (Term.typeCheck_intCmp_inv htc (.inl rfl)).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.gt o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.gt [t1, t2] .bool) .bool htc
          = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.2]) (decide ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).1) > (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1))) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).1 h1, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.ge o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.ge [t1, t2] .bool) .bool htc
          = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.2]) (decide ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).1) ≥ (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1))) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).1 h1, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.and_ o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.and [t1, t2] .bool) .bool htc
          = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inl rfl)).2.2]) ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool (Term.typeCheck_boolBin_inv htc (.inl rfl)).1) && (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool (Term.typeCheck_boolBin_inv htc (.inl rfl)).2.1)) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_boolBin_inv htc (.inl rfl)).1 h1, proof_irrel (Term.typeCheck_boolBin_inv htc (.inl rfl)).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.or_ o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.or [t1, t2] .bool) .bool htc
          = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.2]) ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).1) || (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.1)) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).1 h1, proof_irrel (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.implies o.name hcop))]
      have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.implies [t1, t2] .bool) .bool htc
          = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.2]) (!(Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).1) || (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.1)) := by
        simp only [Term.denoteTyped]
        split
        rfl
      rw [hrhs, proof_irrel (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).1 h1, proof_irrel (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.1 h2]
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
      have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool h1)
          (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool h2) .nil) := by
        rw [← h_acc_denote]; rfl
      subst h_av
      rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty
        (heq_of_eq (hop.equiv o.name hcop))]
      -- The SMT `.eq` denotation (via `Classical.propDecidable` at the operand type
      -- `τ'`) matches the LExpr `decide` at `.bool`; bridge the operand type via
      -- `SMTTerm_denote_cast` and reconcile the two decidability instances.
      rw [SMTTerm_denote_eq_unfold]
      simp only [cast_eq]
      have hτ' : (Term.typeCheck_eq_inv htc).1 = .bool :=
        Except.ok.inj ((Term.typeCheck_eq_inv htc).2.1.symm.trans h1)
      have hd1 := SMTTerm_denote_cast ufInterp smtEnv (divByZero := divByZero) (modByZero := modByZero) t1 .bool (Term.typeCheck_eq_inv htc).1
        h1 (Term.typeCheck_eq_inv htc).2.1 hτ'.symm
      have hd2 := SMTTerm_denote_cast ufInterp smtEnv (divByZero := divByZero) (modByZero := modByZero) t2 .bool (Term.typeCheck_eq_inv htc).1
        h2 (Term.typeCheck_eq_inv htc).2.2.1 hτ'.symm
      congr 1; apply propext; constructor
      · intro heq'; exact eq_of_heq (hd1.trans ((heq_of_eq heq').trans hd2.symm))
      · intro heq'; exact eq_of_heq (hd1.symm.trans ((heq_of_eq heq').trans hd2))

/-! ## Semantic preservation (soundness) of `toSMTTerm` -/

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
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Ψ Δ e τ) (htA : LExpr.HasTypeA Δ e τ)
    (hbase : LExpr.MonoTyIsBase τ)
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx} {smtTy : TermType} {tm : Term}
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtTy)
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜)
    (hufwf : UFCtxWF ufs)
    -- ── correspondence (source ↔ target): encoding, types, contexts, valuations ──
    (h_ok : toSMTTerm bvs e = .ok tm)
    (hτ : baseTyToTermType τ = some smtTy)
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) (hbwf : BVarCtxWF Δ bvs)
    (hfenv : FVarEnvCorresponds huwf fvarVal ufInterp)
    (hopenv : FnEnvCorresponds hψwf opInterp ufInterp)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    : cast (tyDenote_eq_smtTyDenote (σ := σ) hbase hτ)
        (simpDenote opInterp fvarVal bvarVal e τ htA)
      = Term.denoteTyped ufInterp smtEnv divByZero modByZero tm smtTy htc := by
  match e, τ, he, hτ, hbase, htA, h_ok, htc with
  | _, _, .const c hb, hτ, hbase, htA, h_ok, htc =>
    cases c with
    | boolConst b =>
      have htm : tm = .prim (.bool b) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, Term.denoteTyped, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ b).trans
        (@subst_heq _ (TermType.denoteTyped σ 𝒜) _ _ (Term.typeCheck_prim_inv htc) b).symm)
    | intConst i =>
      have htm : tm = .prim (.int i) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, Term.denoteTyped, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ i).trans
        (@subst_heq _ (TermType.denoteTyped σ 𝒜) _ _ (Term.typeCheck_prim_inv htc) i).symm)
    | strConst s =>
      have htm : tm = .prim (.string s) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, Term.denoteTyped, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ s).trans
        (@subst_heq _ (TermType.denoteTyped σ 𝒜) _ _ (Term.typeCheck_prim_inv htc) s).symm)
    | bitvecConst n bv =>
      have htm : tm = .prim (.bitvec bv) := by simp [toSMTTerm] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, Term.denoteTyped, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ bv).trans
        (@subst_heq _ (TermType.denoteTyped σ 𝒜) _ _ (Term.typeCheck_prim_inv htc) bv).symm)
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
    have hres := appToSMTTerm_sound hspine htA opInterp hop fvarVal bvarVal
      (show Term.typeCheckArgs ⟨[], ufs, bvs⟩ [] [] = true from rfl) htc ufInterp smtEnv
      HList.nil (show Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero [] [] rfl = HList.nil from rfl)
      hufwf h_ok' (show baseTysToTermTypes [] = some [] from rfl) hτ
      huwf hψwf hbwf hfenv hopenv hbenv
    -- `UF.applyDenoteTyped' σ 𝒜 [] smtTy f .nil = f`, and the arrow-cast at `[]` is the base cast.
    rw [hres]; rfl
  | _, _, .fvarNullary f τ_f rty hspine, hτ, hbase, htA, h_ok, htc =>
    have h_ok' : appToSMTTerm bvs (.fvar () f (some τ_f)) [] = .ok tm := by
      rw [toSMTTerm] at h_ok; exact h_ok
    have hres := appToSMTTerm_sound hspine htA opInterp hop fvarVal bvarVal
      (show Term.typeCheckArgs ⟨[], ufs, bvs⟩ [] [] = true from rfl) htc ufInterp smtEnv
      HList.nil (show Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero [] [] rfl = HList.nil from rfl)
      hufwf h_ok' (show baseTysToTermTypes [] = some [] from rfl) hτ
      huwf hψwf hbwf hfenv hopenv hbenv
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
          have htc_c := toSMTTerm_typeChecks hc hufwf hc_ok
            (show baseTyToTermType (.tcons "bool" []) = some .bool from rfl) huwf hψwf hbwf
          have htc_t := toSMTTerm_typeChecks ht hufwf ht_ok hτ huwf hψwf hbwf
          have htc_e := toSMTTerm_typeChecks hee hufwf he_ok hτ huwf hψwf hbwf
          have ihc := toSMTTerm_sound hc (HasSimpType_implies_HasTypeA hc) .bool
            opInterp hop fvarVal bvarVal htc_c ufInterp smtEnv
            hufwf hc_ok (show baseTyToTermType (.tcons "bool" []) = some .bool from rfl)
            huwf hψwf hbwf hfenv hopenv hbenv
          have iht := toSMTTerm_sound ht (HasSimpType_implies_HasTypeA ht) hbase
            opInterp hop fvarVal bvarVal htc_t ufInterp smtEnv
            hufwf ht_ok hτ huwf hψwf hbwf hfenv hopenv hbenv
          have ihe := toSMTTerm_sound hee (HasSimpType_implies_HasTypeA hee) hbase
            opInterp hop fvarVal bvarVal htc_e ufInterp smtEnv
            hufwf he_ok hτ huwf hψwf hbwf hfenv hopenv hbenv
          have h_ite_unfold := Lambda.denote_ite (T := CoreLParams) (tcInterp := simpTcInterp)
            (opInterp := opInterp) (fvarVal := fvarVal) (vt := simpTyVarVal)
            bvarVal
            (HasSimpType_implies_HasTypeA hc)
            (HasSimpType_implies_HasTypeA ht)
            (HasSimpType_implies_HasTypeA hee) htA
          simp only [simpDenote] at ihc iht ihe ⊢
          rw [h_ite_unfold]
          rw [SMTTerm_denote_ite]
          apply bif_heq_of_cond_branches (tyDenote_eq_smtTyDenote (σ := σ) hbase hτ)
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
        have htc1 := toSMTTerm_typeChecks he1 hufwf h1_ok hτ'_spec huwf hψwf hbwf
        have htc2 := toSMTTerm_typeChecks he2 hufwf h2_ok hτ'_spec huwf hψwf hbwf
        have ih1 := toSMTTerm_sound he1 (HasSimpType_implies_HasTypeA he1) hb
          opInterp hop fvarVal bvarVal htc1 ufInterp smtEnv
          hufwf h1_ok hτ'_spec huwf hψwf hbwf hfenv hopenv hbenv
        have ih2 := toSMTTerm_sound he2 (HasSimpType_implies_HasTypeA he2) hb
          opInterp hop fvarVal bvarVal htc2 ufInterp smtEnv
          hufwf h2_ok hτ'_spec huwf hψwf hbwf hfenv hopenv hbenv
        simp only [simpDenote] at ih1 ih2 ⊢
        rw [SMTTerm_denote_eq_unfold]
        obtain ⟨τ''_smt, htc1_inv, htc2_inv, heq_bool⟩ := Term.typeCheck_eq_inv htc
        have hτ''_eq : τ''_smt = τ'_smt :=
          Except.ok.inj (htc1_inv.symm.trans htc1)
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
          have hw_eq : Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 _ htc1_inv =
              Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 _ htc2_inv :=
            ih1.symm.trans (congrArg _ heq_vals |>.trans ih2)
          simp only [hw_eq, decide_true]; rfl
        · have h_lhs : LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
              (.eq () e1 e2) (.tcons "bool" []) htA = false :=
            Lambda.denote_eq_false bvarVal
              (HasSimpType_implies_HasTypeA he1)
              (HasSimpType_implies_HasTypeA he2) htA heq_vals
          rw [h_lhs]
          have hw_neq : Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 _ htc1_inv ≠
              Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 _ htc2_inv := by
            intro hw
            apply heq_vals
            have hcast : cast (tyDenote_eq_smtTyDenote (σ := σ) hb hτ'_spec)
                (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
                  e1 τ' (HasSimpType_implies_HasTypeA he1)) =
              cast (tyDenote_eq_smtTyDenote (σ := σ) hb hτ'_spec)
                (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
                  e2 τ' (HasSimpType_implies_HasTypeA he2)) :=
              ih1.trans (hw.trans ih2.symm)
            exact cast_inj_of_eq _ _ _ hcast
          simp only [hw_neq, decide_false]; rfl
  | _, _, .quant qty qbody qk qname qtr qτtr hb htr hbody, hτ, hbase, htA, h_ok, htc =>
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
      have hbwf' : BVarCtxWF (qty :: Δ) (v :: bvs) := by
        refine ⟨?_, ?_, ?_⟩
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
      have hbody_tc : Term.typeCheck ⟨[], ufs, (v :: bvs)⟩ bodyTm = .ok .bool :=
        toSMTTerm_typeChecks hbody hufwf hbody_ok rfl huwf hψwf hbwf'
      -- Correspondence of the body under any environment extending `smtEnv` at `v`.
      have h_ty_eq := tyDenote_eq_smtTyDenote (σ := σ) (𝒜 := 𝒜) hb hqty
      have body_eq : ∀ (x : Lambda.TyDenote simpTcInterp simpTyVarVal qty)
          (smtEnv' : VarEnv σ 𝒜),
          BVarEnvCorresponds hbwf' (.cons x bvarVal) smtEnv' →
          (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal
            (.cons x bvarVal) qbody (.tcons "bool" [])
            (HasSimpType_implies_HasTypeA hbody) : Bool) =
          Term.denoteTyped ufInterp smtEnv' divByZero modByZero bodyTm .bool hbody_tc := by
        intro x smtEnv' henv'
        have ih := toSMTTerm_sound hbody (HasSimpType_implies_HasTypeA hbody) .bool
          opInterp hop fvarVal (.cons x bvarVal) hbody_tc ufInterp smtEnv'
          hufwf hbody_ok (show baseTyToTermType (.tcons "bool" []) = some .bool from rfl)
          huwf hψwf hbwf' hfenv hopenv henv'
        simp only [simpDenote] at ih
        exact eq_of_heq ((cast_heq _ _).symm.trans (heq_of_eq ih))
      -- The combined environment for a given `ext`.
      simp only [simpDenote]
      apply eq_of_heq
      apply HEq.trans (cast_heq _ _)
      unfold LExpr.denote Term.denoteTyped
      dsimp only []
      obtain ⟨_, _, _, h_body_inv⟩ := HasTypeA.quant_inv htA
      obtain ⟨hbody_inv, heq_inv⟩ := Term.typeCheck_quant_inv htc
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
          (ext : VarEnv σ 𝒜)
          (hxy : ext v = cast h_ty_eq x),
          (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal
            (.cons x bvarVal) qbody (.tcons "bool" [])
            (HasSimpType_implies_HasTypeA hbody) : Bool) = true ↔
          Term.denoteTyped ufInterp
            (fun w => if w ∈ [v] then ext w else smtEnv w) divByZero modByZero bodyTm .bool hbody_tc = true := by
        intro x ext hxy
        let smtEnv' : VarEnv σ 𝒜 := fun w => if w ∈ [v] then ext w else smtEnv w
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
          let ext : VarEnv σ 𝒜 := fun w =>
            if hw : w = v then cast (by rw [hw]; exact h_ty_eq) x else smtEnv w
          have hextv : ext v = cast h_ty_eq x := by simp [ext]
          exact (bridge x ext hextv).mpr (hext ext)
      | exist =>
        constructor
        · intro ⟨x, hx⟩
          let ext : VarEnv σ 𝒜 := fun w =>
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
    head (`.fvar`/`.op`), `FVarEnvCorresponds`/`OpInterpConsistent` closes the
    gap between LExpr and SMT interpretations.

    The conclusion is stated as `cast`-based equality at `TermType.denoteTyped σ 𝒜 smtRty`
    (a base type), using `tyDenote_eq_smtTyDenote` to transport between the
    LExpr and SMT type universes. When `acc = []`, this specializes to exactly
    the statement of `toSMTTerm_sound` for the `.app`/`.fvarNullary` cases. -/
theorem appToSMTTerm_sound
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty)
    (htA : LExpr.HasTypeA Δ e (List.foldr LMonoTy.arrow rty acc))
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx} {accTms : List Term} {accSmt : List TermType}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty)
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜)
    (accArgVals : HList (TermType.denoteTyped σ 𝒜) accSmt)
    (h_acc_denote : Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero accTms accSmt h_acc_tc = accArgVals)
    (hufwf : UFCtxWF ufs)
    -- ── correspondence (source ↔ target): encoding, types, contexts, valuations ──
    (h_ok : appToSMTTerm bvs e accTms = .ok tm)
    (hacc : baseTysToTermTypes acc = some accSmt) (hrty : baseTyToTermType rty = some smtRty)
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) (hbwf : BVarCtxWF Δ bvs)
    (hfenv : FVarEnvCorresponds huwf fvarVal ufInterp)
    (hopenv : FnEnvCorresponds hψwf opInterp ufInterp)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    : -- Both sides have type `TermType.denoteTyped σ 𝒜 smtRty` (a base type): the LExpr head's
      -- curried denotation (of arrow type `foldr arrow rty acc`) is `cast` across
      -- `tyDenote_arrow_eq_UFDenote'` to `UF.denoteTyped' accSmt smtRty`, then applied to
      -- the argument values, yielding a base-type result — matching the SMT term's
      -- denotation. The cast is a genuine term, so this is plain equality.
      Term.denoteTyped ufInterp smtEnv divByZero modByZero tm smtRty htc
        = UF.applyDenoteTyped' σ 𝒜 accSmt smtRty
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
      have h_argt := toSMTTerm_typeChecks harg hufwf h_arg_ok h_saty huwf hψwf hbwf
      have hacc' : baseTysToTermTypes (aty :: acc') = some (saty :: accSmt) := by
        simp only [baseTysToTermTypes, h_saty, hacc, bind, Option.bind]
      have h_acc_tc' : Term.typeCheckArgs ⟨[], ufs, bvs⟩ (argt :: accTms) (saty :: accSmt) = true := by
        simp only [Term.typeCheckArgs, h_argt]; simp [h_acc_tc, BEq.beq]
      -- The fresh argument's value, and the extended accumulator's denotation.
      have htA_arg : LExpr.HasTypeA Δ arg aty := HasSimpType_implies_HasTypeA harg
      have htA_fn : LExpr.HasTypeA Δ fn (List.foldr LMonoTy.arrow rty' (aty :: acc')) :=
        AppSpine_implies_HasTypeA hrest
      let vArg : TermType.denoteTyped σ 𝒜 saty := Term.denoteTyped ufInterp smtEnv divByZero modByZero argt saty h_argt
      have h_acc_denote' :
          Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero (argt :: accTms) (saty :: accSmt) h_acc_tc'
            = .cons vArg accArgVals := by
        rw [← h_acc_denote]; rfl
      -- Argument soundness: `vArg` is the cast of the LExpr denotation of `arg`.
      have h_arg_sound : cast (tyDenote_eq_smtTyDenote (σ := σ) (HasSimpType_base harg) h_saty)
          (simpDenote opInterp fvarVal bvarVal arg aty htA_arg) = vArg :=
        toSMTTerm_sound harg htA_arg (HasSimpType_base harg)
          opInterp hop fvarVal bvarVal h_argt ufInterp smtEnv
          hufwf h_arg_ok h_saty huwf hψwf hbwf hfenv hopenv hbenv
      -- Instantiate the IH on the sub-spine `hrest` with the extended accumulator.
      have ih := appToSMTTerm_sound hrest htA_fn opInterp hop fvarVal bvarVal
        h_acc_tc' htc ufInterp smtEnv (.cons vArg accArgVals) h_acc_denote'
        hufwf h_ok hacc' hrty huwf hψwf hbwf hfenv hopenv hbenv
      rw [ih]
      -- `UF.applyDenoteTyped'` on `(saty :: accSmt)` peels its head argument (defeq); it
      -- remains to show the peeled head functions agree.
      show UF.applyDenoteTyped' σ 𝒜 accSmt smtRty _ accArgVals = UF.applyDenoteTyped' σ 𝒜 accSmt smtRty _ accArgVals
      apply congrArg (fun w => UF.applyDenoteTyped' σ 𝒜 accSmt smtRty w accArgVals)
      -- The fn head (cast to `UF.denoteTyped' (saty::accSmt) smtRty`) applied to `vArg`
      -- equals the app-node head (cast to `UF.denoteTyped' accSmt smtRty`).  Rewrite `vArg`
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
      exact cast_arrow_app (tyDenote_eq_smtTyDenote (σ := σ) (HasSimpType_base harg) h_saty)
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
    -- `FVarEnvCorresponds` at `(f.name, τ_f)`, reduced to our concrete `uf`.
    have hfe := hfenv f.name τ_f hmem
    have hlk_uf : (lookupUF ufs f.name).get (huwf.fvar_resolves f.name τ_f hmem)
        = ⟨f.name, ufargs, ufout⟩ := by
      have hsome := huwf.fvar_resolves f.name τ_f hmem
      change (lookupUF ufs f.name).get hsome = _
      simp only [show lookupUF ufs f.name = some ⟨f.name, ufargs, ufout⟩ from hlk, Option.get_some]
    -- `ufInterp` at the resolved `.get` and at the concrete literal are HEq (equal args).
    have h_ufi_heq : HEq (ufInterp ((lookupUF ufs f.name).get (huwf.fvar_resolves f.name τ_f hmem)))
        (ufInterp ⟨f.name, ufargs, ufout⟩) := by rw [hlk_uf]
    -- The LExpr head denotation, cast to `UF.denoteTyped' ufargs ufout`, equals `ufInterp uf`.
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
    have h_denoteArgs : Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero accTms
        (⟨f.name, ufargs, ufout⟩ : UF).args (tc_uf_inv htc).1 = accArgVals := by
      rw [← h_acc_denote]
    -- Close via congruence: both sides are `UF.applyDenoteTyped' σ 𝒜 ufargs ufout ? accArgVals`.
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    apply heq_of_eq
    rw [h_denoteArgs, h_head_eq]
  | _, _, _, .fnOp o oty acc' rty' hmem hnpre hcol hb,
      hacc, h_acc_tc, accArgVals, h_acc_denote, hrty, htA, h_ok, htc =>
    -- User-defined-function head: like the `.fvar` arm, but the LExpr side denotes
    -- through `opInterp` (an `.op` node uses `HasTypeA.op_inv` / `opInterp o.name`),
    -- with correspondence `FnEnvCorresponds` (`hopenv`). The `hnpre` guard forces
    -- `buildAppHead`'s `.op`-none fallback (the UF-application branch).
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
    have hnpre' := not_isPredefinedOp_iff.mp hnpre
    have htm : tm = .app (.core (.uf ⟨o.name, ufargs, ufout⟩)) accTms ufout := by
      simp only [buildAppHead, hnpre', hcol, hout_uf, hargs_uf] at h_ok'
      injection h_ok' with h_ok'; exact h_ok'.symm
    subst htm
    -- Unfold the SMT denotation of the UF application.
    rw [SMTTerm_denote_uf_unfold]
    -- `FnEnvCorresponds` at `(o.name, oty)`, reduced to our concrete `uf`.
    have hoe := hopenv o.name oty hmem
    have hlk_uf : (lookupUF ufs o.name).get (hψwf.fvar_resolves o.name oty hmem)
        = ⟨o.name, ufargs, ufout⟩ := by
      have hsome := hψwf.fvar_resolves o.name oty hmem
      change (lookupUF ufs o.name).get hsome = _
      simp only [show lookupUF ufs o.name = some ⟨o.name, ufargs, ufout⟩ from hlk, Option.get_some]
    -- `ufInterp` at the resolved `.get` and at the concrete literal are HEq (equal args).
    have h_ufi_heq : HEq (ufInterp ((lookupUF ufs o.name).get (hψwf.fvar_resolves o.name oty hmem)))
        (ufInterp ⟨o.name, ufargs, ufout⟩) := by rw [hlk_uf]
    -- The LExpr head denotation, cast to `UF.denoteTyped' ufargs ufout`, equals `ufInterp uf`.
    -- The `.op` denotation uses `opInterp o.name` directly, matching `FnEnvCorresponds`.
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
    have h_denoteArgs : Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero accTms
        (⟨o.name, ufargs, ufout⟩ : UF).args (tc_uf_inv htc).1 = accArgVals := by
      rw [← h_acc_denote]
    -- Close via congruence: both sides are `UF.applyDenoteTyped' σ 𝒜 ufargs ufout ? accArgVals`.
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    apply heq_of_eq
    rw [h_denoteArgs, h_head_eq]
  | _, _, _, .op o oty acc' rty' hopty hcol,
      hacc, h_acc_tc, accArgVals, h_acc_denote, hrty, htA, h_ok, htc =>
    -- Predefined-operator head: fully handled by the standalone `predefinedOp_sound`
    -- (each Core op is one `cases` arm there). This arm is a leaf — no recursive call —
    -- so extracting it keeps new operators out of the mutual soundness proof.
    exact predefinedOp_sound hopty hcol htA opInterp hop fvarVal bvarVal
      h_acc_tc h_ok htc ufInterp smtEnv accArgVals h_acc_denote hacc hrty
  termination_by structural hspine
end

/-! ## Encoder totality (progress)

`toSMTTerm_typeChecks` assumes `h_ok : toSMTTerm bvs e = .ok tm`. That hypothesis is itself derivable
from `HasSimpType`: a well-typed expression never hits any of the encoder's `.error` sites. The four
failure points are each ruled out by the typing judgment:
  • `.const (.realConst _)`      — excluded: `MonoTyIsBase` has no real case.
  • `.bvar` out of bounds        — excluded by `BVarCtxWF.len_eq` + `Δ[i]? = some τ`.
  • quantifier type not encodable — excluded: `MonoTyIsBase qty` ⇒ encodable.
  • `buildAppHead` fvar/op errors — excluded by `FNameCtxWF` / `CoreOpHasType`.

Success of `appToSMTTerm` depends only on the *head* (via `buildAppHead`) and on each peeled argument
translating successfully, so the spine lemma needs no accumulator invariant. -/

mutual
/-- The encoder never errors on a well-typed expression. -/
theorem toSMTTerm_succeeds
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Ψ Δ e τ)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx}
    -- ── correspondence (source ↔ target): typing contexts ──
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) (hbwf : BVarCtxWF Δ bvs) :
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
    exact appSpine_succeeds hspine [] huwf hψwf hbwf
  | .fvarNullary f τ_f rty hspine =>
    -- `toSMTTerm (.fvar ..)` is defeq to `appToSMTTerm (.fvar ..) []`.
    exact appSpine_succeeds hspine [] huwf hψwf hbwf
  | .ite c t _ e_ hc ht hee =>
    have ihc := toSMTTerm_succeeds hc huwf hψwf hbwf
    have iht := toSMTTerm_succeeds ht huwf hψwf hbwf
    have ihe := toSMTTerm_succeeds hee huwf hψwf hbwf
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
    have ih1 := toSMTTerm_succeeds he1 huwf hψwf hbwf
    have ih2 := toSMTTerm_succeeds he2 huwf hψwf hbwf
    unfold toSMTTerm; simp only [bind, Except.bind]
    cases h1_ok : toSMTTerm bvs e1 with
    | error e => rw [h1_ok] at ih1; exact ih1.elim
    | ok t1 =>
      cases h2_ok : toSMTTerm bvs e2 with
      | error e => rw [h2_ok] at ih2; exact ih2.elim
      | ok t2 => exact True.intro
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody =>
    -- `MonoTyIsBase qty` ⇒ `qty` is encodable, so the guard passes; the body then
    -- succeeds by IH under the extended bound-variable context.
    obtain ⟨smtQTy, hqty_eq⟩ := MonoTyIsBase_baseTyToTermType hbase
    have hstr : toString "$__bv" = "$__bv" := rfl
    have hstr2 : ∀ n : Nat, toString n = Nat.repr n := fun _ => rfl
    have hbwf' : BVarCtxWF (qty :: Δ)
        (⟨"$__bv" ++ (bvs.length).repr, smtQTy⟩ :: bvs) := by
      refine ⟨?_, ?_, ?_⟩
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
    have ihbody := toSMTTerm_succeeds hbody huwf hψwf hbwf'
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
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx} (accTms : List Term)
    -- ── correspondence (source ↔ target): typing contexts ──
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) (hbwf : BVarCtxWF Δ bvs) :
    match appToSMTTerm bvs e accTms with
    | .error _ => False
    | .ok _ => True := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    -- Translate the argument (succeeds by IH), then recurse on the function spine
    -- with it prepended to the accumulator.
    have iharg := toSMTTerm_succeeds harg huwf hψwf hbwf
    rw [appToSMTTerm]; simp only [bind, Except.bind]
    cases h_arg_ok : toSMTTerm bvs arg with
    | error e => rw [h_arg_ok] at iharg; exact iharg.elim
    | ok argt => exact appSpine_succeeds hrest (argt :: accTms) huwf hψwf hbwf
  | .fvar f τ acc' rty hmem hcollect hbase =>
    -- `FNameCtxWF` supplies SMT encodings for the argument and return types, so
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
    -- User-defined-function head: `FNameCtxWF Ψ ufs` supplies SMT encodings for the
    -- argument and return types, so `buildAppHead`'s `.op`-none fallback returns `.ok`.
    have hψwf_info := hψwf.fvar_has_uf o.name oty hmem
    rw [hcollect] at hψwf_info
    obtain ⟨smtArgTys, smtRty', h_smtArgTys, h_smtRty', _⟩ := hψwf_info
    simp only [appToSMTTerm, buildAppHead, not_isPredefinedOp_iff.mp hnpre, hcollect,
      h_smtRty', h_smtArgTys]
  termination_by structural hspine
end

/-! ## Top-level correctness

Wraps `toSMTTerm_succeeds` (totality), `toSMTTerm_typeChecks` (sort agreement), and
`Term.typeOf_of_typeCheck` (annotation fidelity) into a single statement that assumes *only*
`HasSimpType` plus the context well-formedness side conditions — no `h_ok`, no `hτ`.

Both would-be existentials are replaced by pattern matches that return `False` on the impossible
branches:
  • `toSMTTerm bvs e = .error _`   — impossible (totality).
  • `baseTyToTermType τ = none`     — impossible (`τ` is `MonoTyIsBase`). -/

/-- If `e` has simple type `τ`, then `toSMTTerm` produces a term `tm` whose SMT
    sort is exactly the encoding of `τ` — both at the type it type-checks (hence
    denotes) and at its syntactic `Term.typeOf`. -/
theorem toSMTTerm_type_correct
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Ψ Δ e τ)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx}
    (hufwf : UFCtxWF ufs)
    -- ── correspondence (source ↔ target): typing contexts ──
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) (hbwf : BVarCtxWF Δ bvs) :
    match toSMTTerm bvs e, baseTyToTermType τ with
    | .ok tm, some smtTy =>
      Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtTy ∧ Term.typeOf tm = smtTy
    | _, _ => False := by
  -- `τ` is base, so it is encodable — kills the `none` arm.
  obtain ⟨smtTy, hτ⟩ := MonoTyIsBase_baseTyToTermType (HasSimpType_base he)
  -- The encoder succeeds — kills the `.error` arm.
  have hsucc := toSMTTerm_succeeds he huwf hψwf hbwf
  rw [hτ]
  cases h_ok : toSMTTerm bvs e with
  | error e => rw [h_ok] at hsucc; exact hsucc.elim
  | ok tm =>
    -- `_typeChecks` proves the sort agreement; `typeOf_of_typeCheck` the fidelity.
    have htc := toSMTTerm_typeChecks he hufwf h_ok hτ huwf hψwf hbwf
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
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Ψ Δ e τ)
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx}
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜)
    (hufwf : UFCtxWF ufs)
    -- ── correspondence (source ↔ target): typing contexts, then valuations ──
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) (hbwf : BVarCtxWF Δ bvs)
    (hfenv : FVarEnvCorresponds huwf fvarVal ufInterp)
    (hopenv : FnEnvCorresponds hψwf opInterp ufInterp)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv) :
    match toSMTTerm bvs e, baseTyToTermType τ with
    | .ok tm, some smtTy =>
      ∃ (hτ : baseTyToTermType τ = some smtTy)
        (htc : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtTy),
        cast (tyDenote_eq_smtTyDenote (σ := σ) (HasSimpType_base he) hτ)
            (simpDenote opInterp fvarVal bvarVal e τ (HasSimpType_implies_HasTypeA he))
          = Term.denoteTyped ufInterp smtEnv divByZero modByZero tm smtTy htc
    | _, _ => False := by
  -- `τ` is base, so it is encodable — kills the `none` arm (as in `_type_correct`).
  obtain ⟨smtTy, hτ⟩ := MonoTyIsBase_baseTyToTermType (HasSimpType_base he)
  -- The encoder succeeds — kills the `.error` arm.
  have hsucc := toSMTTerm_succeeds he huwf hψwf hbwf
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
    have htc := toSMTTerm_typeChecks he hufwf h_ok hτ huwf hψwf hbwf
    exact ⟨rfl, htc, toSMTTerm_sound he (HasSimpType_implies_HasTypeA he) (HasSimpType_base he)
      opInterp hop fvarVal bvarVal htc ufInterp smtEnv
      hufwf h_ok hτ huwf hψwf hbwf hfenv hopenv hbenv⟩



/-! ## Ordered interpreted-function context

Data model for the pipeline-level generalisation. The LExpr-level source lists are PRIMARY;
`UFCtx`/`IFs` are DERIVED by encoding. Declarations and definitions are SPLIT: `decls : FnCtx` are
body-less (unordered, globally visible), `defs : List FnDef` are the defined functions (ordered,
callee-before-caller). A `FnDef` stores its body with formals ALREADY lifted to `.bvar`, so
`toSMTTerm` handles it with no substitution.

The signatures of the definitions are extracted and merged into other declarations for LExpr
denotation, so `FnCtx` carries information from `FnDef` and `UFCtx` from `IFs` in that stage. -/

/-- A user-defined function DEFINITION, LExpr side. `argTys` is the bound-variable context `Δ`;
    `body`'s formal `i` is `.bvar () i` (pre-lifted at construction); the substitution that produces
    this form is not verified (a model/implementation boundary). -/
structure FnDef where
  name : String
  argTys : List LMonoTy
  retTy : LMonoTy
  body : Expression.Expr

abbrev FnDefs := List FnDef

/-- Intrinsic well-formedness of a `FnDef`: its formal-argument types are all base
    types — the SIGNATURE-encodability half. This is what makes `baseTysToTermTypes
    d.argTys` (hence `FnDef.smtArgTys`/`toUF`) total and `d.argTys` a valid
    bound-variable context for `HasSimpType`/`BVarCtxWF`.

    Only `argTys` is constrained here, and it is NOT redundant with the body's
    `HasSimpType`: that judgment forces `MonoTyIsBase` on an argument type only if
    the body REFERENCES it (via the `.bvar` rule), so an unused formal of non-base
    type would slip past `HasSimpType` yet break `baseTysToTermTypes d.argTys`. The
    RETURN type's base-ness and the BODY's encodability are supplied by the
    context-relative `HasSimpType Φ Ψ d.argTys d.body d.retTy`. -/
def FnDef.WF (d : FnDef) : Prop :=
  ∀ t ∈ d.argTys, LExpr.MonoTyIsBase t

/-- The LExpr signature `(name, a₁ → ⋯ → aₙ → ret)` — the arrow type this
    definition contributes to the obligation's `FnCtx`. -/
def FnDef.sig (d : FnDef) : String × LMonoTy :=
  (d.name, List.foldr LMonoTy.arrow d.retTy d.argTys)

/-! ## Consistency of `opInterp` with a single `FnDef` (Lambda side)

The atom the pipeline-level consistency notions build on. It is purely Lambda-side (stated over
`simpDenote`, with no `ufInterp`/`Term.denoteTyped`): a `FnDef`'s body is already bvar-lifted (formal
`i` is `.bvar () i`, typed at `d.argTys`), so the argument valuation is a `BVarVal` over `d.argTys`
and the head is applied by `applyBVarVal` below. -/

/-- Apply a curried Lambda value of arrow type `a₁ → ⋯ → aₙ → ret` (as it denotes
    under `simpTyVarVal`) to the values of a `BVarVal` over `[a₁, …, aₙ]`, yielding
    the `ret` denotation. This is the Lambda-side, SMT-free analog of
    `UF.applyDenoteTyped'`: `substTyVars` distributes over `LMonoTy.arrow`, so the head's
    type reduces definitionally to the iterated function type and each application
    is plain — no reindexing cast. -/
def applyBVarVal : (argTys : List LMonoTy) → (ret : LMonoTy) →
    Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow ret argTys) →
    Lambda.BVarVal simpTcInterp simpTyVarVal argTys →
    Lambda.TyDenote simpTcInterp simpTyVarVal ret
  | [], _, f, .nil => f
  | _ :: _, ret, f, .cons x xs => applyBVarVal _ ret (f x) xs

/-- **`opInterp` is consistent with the definition `d`.** For every argument
    valuation, the operator interpretation at `d`'s signature — applied to those
    arguments — equals the denotation of `d`'s (bvar-lifted) body under the same
    valuation. This is the LExpr-side (2) contract, per function: "`opInterp d.name`
    IS the body's meaning", exactly as production defines a UDF's interpretation.

    A nullary `d` (`argTys = []`) is the variable-definition case: it reduces to
    `opInterp d.name (…) = simpDenote … d.body`, i.e. `define-fun d.name () = body`.

    `fvarVal` is quantified (the body may mention free variables / other symbols);
    `htA` is the body's Lambda typing, derived from `FnDef.WFIn` (the body's
    `HasSimpType` in the callee context) via `HasSimpType_implies_HasTypeA`. -/
def FnDef.OpConsistent
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (d : FnDef) (htA : LExpr.HasTypeA d.argTys d.body d.retTy) : Prop :=
  ∀ (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal d.argTys),
    applyBVarVal d.argTys d.retTy
      (opInterp d.name ((List.foldr LMonoTy.arrow d.retTy d.argTys).substTyVars simpTyVarVal))
      bvarVal
    = simpDenote opInterp fvarVal bvarVal d.body d.retTy htA

/-- **Context-relative well-formedness of a `FnDef`.** Its (bvar-lifted) body is
    SMT-encodably well-typed in the callee context `(Φ, Ψ)` at return type `d.retTy`,
    with `d.argTys` as the bound-variable context. This is the BODY + RETURN-TYPE
    encodability half (the complement of the intrinsic `FnDef.WF`, which covers the
    signature's argument types): `HasSimpType` here supplies both the
    `toSMTTerm_sound`/`_typeChecks` precondition (IF-correspondence, SMT side) AND,
    via `HasSimpType_implies_HasTypeA`, the `HasTypeA` that `OpConsistent` consumes
    (consistency, Lambda side) — one judgment feeding both. The context is the FULL obligation
    `(Φ, Ψ)` (no prefix/weakening); at the pipeline level `Ψ` includes this and every sibling
    definition's signature. -/
def FnDef.WFIn (Φ : FVarCtx) (Ψ : FnCtx) (d : FnDef) : Prop :=
  LExpr.HasSimpType Φ Ψ d.argTys d.body d.retTy

/-- The `HasTypeA` body typing `OpConsistent` needs, DERIVED from `WFIn` — the
    single-judgment bridge that keeps typing contexts out of the consistency def. -/
theorem FnDef.WFIn.hasTypeA {Φ : FVarCtx} {Ψ : FnCtx} {d : FnDef}
    (h : d.WFIn Φ Ψ) : LExpr.HasTypeA d.argTys d.body d.retTy :=
  HasSimpType_implies_HasTypeA h

/-- **Context-relative well-formedness of a list of `FnDef`s.** Every definition is `WFIn` in the
    (full) callee context — the collection-level companion of `FnDef.WFIn`. It is a SEPARATE premise
    from `FnDefs.OpConsistent` (well-formedness and consistency are distinct concerns): the
    `(1)+(2)⟹(3)` derivation draws the per-function `WFIn` from it — both to run `toSMTTerm_sound`
    (needs `HasSimpType`) AND to discharge `FnDefs.OpConsistent`'s context-free `HasTypeA` premise
    (via `WFIn.hasTypeA`), so one judgment feeds both without baking SMT-encoding contexts into the
    consistency notion. -/
def FnDefsWF (Φ : FVarCtx) (Ψ : FnCtx) (defs : List FnDef) : Prop :=
  ∀ (d : FnDef), d ∈ defs → d.WFIn Φ Ψ

/-- **`opInterp` is consistent with a list of `FnDef`s.** The per-function
    `FnDef.OpConsistent` holds for every definition. Like its single-function
    counterpart this is PURELY LExpr-side: it takes the context-free body typings
    `ht` (a `HasTypeA` per definition) directly, so no `FVarCtx`/`FnCtx` appears — the
    SMT-encoding contexts live only in the `FnDefsWF` premise the derivation supplies
    (via `WFIn.hasTypeA`). An ORDER-FREE conjunction: list order is incidental (emission
    only). This is the LExpr-side hypothesis the model transfer consumes; `.det`
    variable definitions participate as their nullary (`argTys = []`) case. -/
def FnDefs.OpConsistent
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (defs : List FnDef)
    (ht : ∀ d ∈ defs, LExpr.HasTypeA d.argTys d.body d.retTy) : Prop :=
  ∀ (d : FnDef) (hmem : d ∈ defs),
    d.OpConsistent opInterp fvarVal (ht d hmem)

/-! ## Consistency of `ufInterp` with a single `IF` (SMT side, the (3) contract)

The SMT-side mirror of `FnDef.OpConsistent`. It is exactly `define-fun` semantics: `ufInterp` at the
function's signature, applied to argument values, equals the SMT denotation of the encoded body
`f.body` under the environment that binds `f`'s formals to those values. Where `OpConsistent` is
stated over `simpDenote`/`applyBVarVal` (Lambda), this is over `Term.denoteTyped`/`UF.applyDenoteTyped`
(SMT). Together with correspondence (1) and `toSMTTerm_sound` these are the three sides of the
triangle; (3) is what a `define-fun` preamble guarantees. -/

/-- Place an HList of SMT argument values into an `VarEnv σ 𝒜` at the positions named
    by `bvs`, with an arbitrary `default` elsewhere. The SMT-side analog of
    `applyBVarVal` building a `BVarVal` — a stating helper for the (3) contract.
    No ambient/base env is threaded: a well-typed IF body's
    only `.var` nodes are its formals (`toSMTTerm` emits `.var` solely from `.bvar`;
    free variables become UF applications resolved through `ufInterp`), so the
    `default` branch is never denoted — making this closed over the formals exactly
    as `applyBVarVal` is closed over `argTys`. -/
noncomputable def hlToEnv : (bvs : TermVarCtx) → HList (TermType.denoteTyped σ 𝒜) (bvs.map (·.ty)) → VarEnv σ 𝒜
  | [], _ => fun _ => default
  | v :: rest, hl =>
    match hl with
    | .cons x xs => fun w => if h : w = v then cast (by rw [h]) x else hlToEnv rest xs w

/-- **`ufInterp` is consistent with the interpreted function `f`** (the `define-fun`
    contract (3)). For every argument valuation, `ufInterp` at `f`'s UF signature —
    applied to those arguments — equals the SMT denotation of the encoded body
    `f.body` under the environment binding `f`'s formals to them. `htc` witnesses
    that `f.body` type-checks at `f.out` in `f`'s formal context (`f.args` alone — a
    well-typed body has no free `.var` outside its formals, which is why no ambient
    env is needed; see `hlToEnv`).

    A nullary `f` (`args = []`) is the variable-definition case: `ufInterp ⟨name,[],out⟩
    = Term.denoteTyped … f.body`, i.e. `define-fun name () out f.body`. -/
def IF.UFConsistent {ufs : UFCtx} (f : IF)
    (htc : Term.typeCheck ⟨[], ufs, f.args⟩ f.body = .ok f.out)
    (ufInterp : UFInterp σ 𝒜) (divByZero modByZero : Int → Int) : Prop :=
  ∀ hl : HList (TermType.denoteTyped σ 𝒜) f.toUF.args,
    UF.applyDenoteTyped σ 𝒜 f.toUF (ufInterp f.toUF) hl
    = Term.denoteTyped ufInterp (hlToEnv f.args hl) divByZero modByZero f.body f.out htc

/-- The ordered interpreted-function context: the SMT `IF`s in emission order, matching production's
    `SMT.Context.ifs : Array IF`. Kept as a distinct notion (`IF` carries the ALREADY-ENCODED body);
    resolution/typing use only `IF.toUF`, so most proofs work through `FnDef`/`toUF` and materialise
    `Ω` only where the encoded body is needed. -/
abbrev IFs := List IF

/-- **`ufInterp` is consistent with a list of `IF`s** — the SMT-side collection
    contract (3), the exact mirror of the LExpr-side `FnDefs.OpConsistent`. Given each
    IF's body type-checks (the per-element `htc` family), the per-function
    `IF.UFConsistent` holds for every IF. Like its mirror it is an ORDER-FREE
    conjunction; nullary IFs (`args = []`) are the variable-definition instances. This
    is what the construction layer must establish for the emitted `define-fun`
    preamble, discharged per-function via `UFConsistent_of_OpConsistent'`. -/
def IFs.UFConsistent {ufs : UFCtx} (fs : IFs)
    (htc : ∀ f ∈ fs, Term.typeCheck ⟨[], ufs, f.args⟩ f.body = .ok f.out)
    (ufInterp : UFInterp σ 𝒜) (divByZero modByZero : Int → Int) : Prop :=
  ∀ (f : IF) (hmem : f ∈ fs),
    IF.UFConsistent f (htc f hmem) ufInterp divByZero modByZero

/-! ## Bridge (1)+(2) ⟹ (3)

A corresponding, consistent `opInterp` yields the `define-fun` contract for the encoded body. The
consistency premises are the pure-Lambda `FnDef.OpConsistent` (2) and the SMT `IF.UFConsistent` (3)
is the goal, bridged by `toSMTTerm_sound`. Because `OpConsistent` uses `applyBVarVal` rather than the
SMT-flavoured `UF.applyDenoteTyped'`, the `applyBVarVal ↔ UF.applyDenoteTyped'` step is an explicit
bridge lemma here. -/

/-- Head projection of `baseTysToTermTypes` on a cons. -/
private theorem baseTysToTermTypes_cons_head {a : LMonoTy} {as : List LMonoTy}
    {s : TermType} {ss : List TermType} (h : baseTysToTermTypes (a :: as) = some (s :: ss)) :
    baseTyToTermType a = some s := by
  simp only [baseTysToTermTypes, bind, Option.bind] at h
  cases ha : baseTyToTermType a with
  | none => rw [ha] at h; exact absurd h (by simp)
  | some sa =>
    rw [ha] at h; simp only at h
    cases hr : baseTysToTermTypes as with
    | none => rw [hr] at h; exact absurd h (by simp)
    | some sr => rw [hr] at h; simp only [Option.some.injEq, List.cons.injEq] at h; rw [h.1]

/-- Tail projection of `baseTysToTermTypes` on a cons. -/
private theorem baseTysToTermTypes_cons_tail {a : LMonoTy} {as : List LMonoTy}
    {s : TermType} {ss : List TermType} (h : baseTysToTermTypes (a :: as) = some (s :: ss)) :
    baseTysToTermTypes as = some ss := by
  simp only [baseTysToTermTypes, bind, Option.bind] at h
  cases ha : baseTyToTermType a with
  | none => rw [ha] at h; exact absurd h (by simp)
  | some sa =>
    rw [ha] at h; simp only at h
    cases hr : baseTysToTermTypes as with
    | none => rw [hr] at h; exact absurd h (by simp)
    | some sr => rw [hr] at h; simp only [Option.some.injEq, List.cons.injEq] at h; rw [h.2]

/-- Drop the head binder of a well-formed bound-variable context. -/
theorem BVarCtxWF.tail {a : LMonoTy} {as : List LMonoTy} {v : TermVar} {rest : TermVarCtx}
    (h : BVarCtxWF (a :: as) (v :: rest)) : BVarCtxWF as rest := by
  refine ⟨?_, ?_, ?_⟩
  · have := h.len_eq; simpa using this
  · intro i hi
    have := h.ty_eq (i + 1) (by simp only [List.length_cons]; omega)
    simpa using this
  · intro i hi
    have hcpy := h.id_scheme (i + 1) (by simp only [List.length_cons]; omega)
    simp only [List.getElem_cons_succ, List.length_cons] at hcpy
    have hnat : rest.length + 1 - 1 - (i + 1) = rest.length - 1 - i := by omega
    rw [hcpy, hnat]

/-- A bound-variable context's monotypes encode exactly to the SMT sorts of its
    term variables (from `len_eq` + `ty_eq`). -/
theorem BVarCtxWF.baseTysToTermTypes_eq {Δ : List LMonoTy} {bvs : TermVarCtx}
    (h : BVarCtxWF Δ bvs) : baseTysToTermTypes Δ = some (bvs.map (·.ty)) := by
  induction Δ generalizing bvs with
  | nil =>
    have hlen := h.len_eq
    cases bvs with
    | nil => rfl
    | cons b bs => simp at hlen
  | cons a as ih =>
    have hlen := h.len_eq
    cases bvs with
    | nil => simp at hlen
    | cons b bs =>
      have hty := h.ty_eq 0 (by simp)
      simp only [List.getElem_cons_zero] at hty
      have htail : BVarCtxWF as bs := h.tail
      simp only [baseTysToTermTypes, List.map_cons, hty, ih htail, bind, Option.bind]

omit [SortInterp.AllInhabited σ] in
/-- Two curried UF denotations that agree on every argument HList are equal —
    the uncurry direction the correspondence proof needs. -/
theorem UF.denoteTyped'_ext :
    (argTys : List TermType) → (out : TermType) → (f g : UF.denoteTyped' σ 𝒜 argTys out) →
    (∀ hl : HList (TermType.denoteTyped σ 𝒜) argTys, UF.applyDenoteTyped' σ 𝒜 argTys out f hl = UF.applyDenoteTyped' σ 𝒜 argTys out g hl) →
    f = g
  | [], _, f, g, h => by
    have := h .nil; simpa only [UF.applyDenoteTyped'] using this
  | a :: rest, out, f, g, h => by
    funext (x : TermType.denoteTyped σ 𝒜 a)
    exact UF.denoteTyped'_ext rest out (f x) (g x) (fun hl => by
      have := h (.cons x hl); simpa only [UF.applyDenoteTyped'] using this)

/-- Reinterpret an HList of SMT argument values (indexed by `bvs`) as an LExpr
    bound-variable valuation over `Δ`, casting each element back across
    `tyDenote_eq_smtTyDenote`. -/
noncomputable def hlToBVarVal :
    (Δ : List LMonoTy) → (bvs : TermVarCtx) →
    baseTysToTermTypes Δ = some (bvs.map (·.ty)) →
    HList (TermType.denoteTyped σ 𝒜) (bvs.map (·.ty)) →
    Lambda.BVarVal simpTcInterp simpTyVarVal Δ
  | [], [], _, _ => .nil
  | [], b :: bs, henc, _ => absurd henc (by simp [baseTysToTermTypes])
  | a :: as, [], henc, _ => by
      exfalso; simp only [List.map_nil] at henc
      simp only [baseTysToTermTypes, bind, Option.bind] at henc
      cases ha : baseTyToTermType a with
      | none => rw [ha] at henc; exact absurd henc (by simp)
      | some sa => rw [ha] at henc; simp only at henc
                   cases hr : baseTysToTermTypes as with
                   | none => rw [hr] at henc; exact absurd henc (by simp)
                   | some sr => rw [hr] at henc; exact absurd henc (by simp)
  | a :: as, b :: bs, henc, .cons x xs =>
    have henc' : baseTysToTermTypes (a :: as) = some (b.ty :: bs.map (·.ty)) := by
      simpa using henc
    .cons (cast (tyDenote_eq_smtTyDenote (σ := σ) (baseTyToTermType_isBase (baseTysToTermTypes_cons_head henc'))
                  (baseTysToTermTypes_cons_head henc')).symm x)
          (hlToBVarVal as bs (baseTysToTermTypes_cons_tail henc') xs)

/-- The environment bridge: `hlToBVarVal` and `hlToEnv` built from the same HList
    correspond under `BVarEnvCorresponds`. -/
theorem hlToBVarVal_hlToEnv_corresponds :
    (Δ : List LMonoTy) → (bvs : TermVarCtx) →
    (hbwf : BVarCtxWF Δ bvs) →
    (henc : baseTysToTermTypes Δ = some (bvs.map (·.ty))) →
    (hl : HList (TermType.denoteTyped σ 𝒜) (bvs.map (·.ty))) →
    BVarEnvCorresponds hbwf (hlToBVarVal Δ bvs henc hl) (hlToEnv bvs hl)
  | [], [], hbwf, henc, _ => by
    intro i τ hbase hlook; exact absurd hlook (by simp)
  | [], b :: bs, _, henc, _ => absurd henc (by simp [baseTysToTermTypes])
  | a :: as, [], _, henc, _ => by
    exfalso; simp only [List.map_nil, baseTysToTermTypes, bind, Option.bind] at henc
    cases ha : baseTyToTermType a with
    | none => rw [ha] at henc; exact absurd henc (by simp)
    | some sa => rw [ha] at henc; simp only at henc
                 cases hr : baseTysToTermTypes as with
                 | none => rw [hr] at henc; exact absurd henc (by simp)
                 | some sr => rw [hr] at henc; exact absurd henc (by simp)
  | a :: as, v :: rest, hbwf, henc, .cons x xs => by
    have henc' : baseTysToTermTypes (a :: as) = some (v.ty :: rest.map (·.ty)) := by simpa using henc
    have ha : baseTyToTermType a = some v.ty := baseTysToTermTypes_cons_head henc'
    have hrest_enc : baseTysToTermTypes as = some (rest.map (·.ty)) := baseTysToTermTypes_cons_tail henc'
    have hbwf_tail : BVarCtxWF as rest := hbwf.tail
    have ih := hlToBVarVal_hlToEnv_corresponds as rest hbwf_tail hrest_enc xs
    have hbv_eq : hlToBVarVal (a :: as) (v :: rest) henc (.cons x xs)
        = .cons (cast (tyDenote_eq_smtTyDenote (σ := σ) (baseTyToTermType_isBase ha) ha).symm x)
                (hlToBVarVal as rest hrest_enc xs) := by
      simp only [hlToBVarVal]
    have henv_eq : hlToEnv (v :: rest) (.cons x xs)
        = fun w => if h : w = v then cast (by rw [h]) x else hlToEnv rest xs w := by
      simp only [hlToEnv]
    rw [hbv_eq, henv_eq]
    refine BVarEnvCorresponds_cons ih (baseTyToTermType_isBase ha) ha
      (cast (tyDenote_eq_smtTyDenote (σ := σ) (baseTyToTermType_isBase ha) ha).symm x) ?_ ?_ hbwf
    · simp only [dif_pos]
      rw [cast_cast, cast_eq]
    · intro w hwne
      simp only [dif_neg hwne]

/-- The empty function context is well-formed against any UF context (our
    `FNameCtxWF` carries only resolution fields, so the empty context is vacuous). -/
theorem FNameCtxWF.nil {ufs : UFCtx} : FNameCtxWF [] ufs where
  fvar_resolves := by intro name τ hmem; exact absurd hmem (by simp)
  args_eq := by intro name τ uf hmem; exact absurd hmem (by simp)
  out_eq := by intro name τ uf hmem; exact absurd hmem (by simp)

/-- `FnEnvCorresponds` is vacuously true for the empty function context. -/
theorem FnEnvCorresponds.nil {ufs : UFCtx}
    (opInterp : Lambda.OpInterp simpTcInterp) (ufInterp : UFInterp σ 𝒜) :
    FnEnvCorresponds (FNameCtxWF.nil (ufs := ufs)) opInterp ufInterp := by
  intro name τ hmem; exact absurd hmem (by simp)

/-- **The `applyBVarVal ↔ UF.applyDenoteTyped'` bridge.** Applying a curried Lambda head to a
    `BVarVal` (built from `hl` via `hlToBVarVal`) and applying the SAME head — cast across
    `tyDenote_arrow_eq_UFDenote'` to a `UF.denoteTyped'` — to `hl` itself give the same value (modulo
    the base-type cast on the result). This is the step the pure-Lambda `FnDef.OpConsistent` needs.
    Proved by induction on `(Δ, bvs)` in lockstep, mirroring `hlToBVarVal`. -/
theorem applyBVarVal_eq_applyDenoteTyped' :
    (Δ : List LMonoTy) → (bvs : TermVarCtx) → {rty : LMonoTy} → {smtRty : TermType} →
    (henc : baseTysToTermTypes Δ = some (bvs.map (·.ty))) →
    (hrty : baseTyToTermType rty = some smtRty) →
    (hd : Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow rty Δ)) →
    (hl : HList (TermType.denoteTyped σ 𝒜) (bvs.map (·.ty))) →
    UF.applyDenoteTyped' σ 𝒜 (bvs.map (·.ty)) smtRty
        (cast (tyDenote_arrow_eq_UFDenote' (by rw [henc]) hrty) hd) hl
      = cast (tyDenote_eq_smtTyDenote (σ := σ) (baseTyToTermType_isBase hrty) hrty)
          (applyBVarVal Δ rty hd (hlToBVarVal Δ bvs henc hl))
  | [], [], rty, smtRty, henc, hrty, hd, .nil => by
    simp only [hlToBVarVal, applyBVarVal]
    -- Both sides are `cast (…) hd`; the two casts coincide by proof irrelevance.
    rfl
  | [], b :: bs, _, _, henc, _, _, _ => absurd henc (by simp [baseTysToTermTypes])
  | a :: as, [], _, _, henc, _, _, _ => by
    exfalso; simp only [List.map_nil] at henc
    simp only [baseTysToTermTypes, bind, Option.bind] at henc
    cases ha : baseTyToTermType a with
    | none => rw [ha] at henc; exact absurd henc (by simp)
    | some sa => rw [ha] at henc; simp only at henc
                 cases hr : baseTysToTermTypes as with
                 | none => rw [hr] at henc; exact absurd henc (by simp)
                 | some sr => rw [hr] at henc; exact absurd henc (by simp)
  | a :: as, v :: rest, rty, smtRty, henc, hrty, hd, .cons x xs => by
    have henc' : baseTysToTermTypes (a :: as) = some (v.ty :: rest.map (·.ty)) := by simpa using henc
    have ha : baseTyToTermType a = some v.ty := baseTysToTermTypes_cons_head henc'
    have hrest_enc : baseTysToTermTypes as = some (rest.map (·.ty)) := baseTysToTermTypes_cons_tail henc'
    -- Abbreviation for the argument-type cast.
    let AC : Lambda.TyDenote simpTcInterp simpTyVarVal a = TermType.denoteTyped σ 𝒜 v.ty :=
      tyDenote_eq_smtTyDenote (σ := σ) (baseTyToTermType_isBase ha) ha
    -- The whole head, cast to `UF.denoteTyped' (v.ty :: rest.map) smtRty`, applied to `x`
    -- equals `hd` applied to the (back-cast) `x`, re-cast to the tail `UF.denoteTyped'`.
    -- Rewrite `x` as `cast AC (cast AC.symm x)` so `cast_arrow_app` applies.
    have hcaa := cast_arrow_app AC (tyDenote_arrow_eq_UFDenote' hrest_enc hrty)
          (tyDenote_arrow_eq_UFDenote' henc' hrty) hd (cast AC.symm x)
    -- `cast AC (cast AC.symm x) = x`, so `hcaa` becomes the head equality we want.
    rw [cast_cast, cast_eq] at hcaa
    have hhead : (cast (tyDenote_arrow_eq_UFDenote' henc' hrty) hd) x
        = cast (tyDenote_arrow_eq_UFDenote' hrest_enc hrty) (hd (cast AC.symm x)) := hcaa
    -- Reduce each applier by one (definitional) cons step, then bridge + tail IH.
    show UF.applyDenoteTyped' σ 𝒜 (rest.map (·.ty)) smtRty
          ((cast (tyDenote_arrow_eq_UFDenote' henc' hrty) hd) x) xs
        = cast (tyDenote_eq_smtTyDenote (σ := σ) (baseTyToTermType_isBase hrty) hrty)
            (applyBVarVal as rty (hd (cast AC.symm x)) (hlToBVarVal as rest hrest_enc xs))
    rw [hhead]
    rw [applyBVarVal_eq_applyDenoteTyped' as rest hrest_enc hrty (hd (cast AC.symm x)) xs]

/-- **(1)+(2) ⟹ (3), per function (the atom).** For a single interpreted function at
    an arbitrary callee context `Ψ`, given correspondence (1) `cast (opInterp d.name)
    = ufInterp uf` (plus callee correspondence `hopenv` for `Ψ`) and the pure-Lambda
    consistency (2) `d.OpConsistent`, the `define-fun` contract (3) `IF.UFConsistent`
    for the encoded body holds. The proof chains, at each argument HList `hl`:
    `UF.applyDenoteTyped σ 𝒜 (ufInterp uf) =[1, bridge] applyBVarVal (opInterp d.name)
    (hlToBVarVal hl) =[2] cast (simpDenote body) =[toSMTTerm_sound] Term.denoteTyped
    ifbody`. This is where `HasSimpType` (via `WFIn`) is REQUIRED — it is the `he`
    premise of `toSMTTerm_sound` bridging the two body denotations. The model transfer
    applies this per emitted function to cover a whole `defs`. -/
theorem UFConsistent_of_OpConsistent'
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} (d : FnDef)
    (hbody : LExpr.HasSimpType Φ Ψ d.argTys d.body d.retTy)
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    -- (2) consistency (pure Lambda-side):
    (hcons : d.OpConsistent opInterp fvarVal (HasSimpType_implies_HasTypeA hbody))
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx} {smtRty : TermType} {ifbody : Term}
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ ifbody = .ok smtRty)
    (ufInterp : UFInterp σ 𝒜)
    (hufwf : UFCtxWF ufs)
    -- ── correspondence (source ↔ target): encoding, types, contexts, valuations ──
    (h_bridge : toSMTTerm bvs d.body = .ok ifbody)
    (hrty : baseTyToTermType d.retTy = some smtRty)
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs) (hbwf : BVarCtxWF d.argTys bvs)
    (hfenv : FVarEnvCorresponds huwf fvarVal ufInterp)
    -- (1a) callee correspondence, for the body's function context `Ψ` (a relational
    -- hypothesis — bodies that call other IFs supply their callees' correspondence
    -- here; `Ψ = []` recovers the callee-free case via `FnEnvCorresponds.nil`):
    (hopenv : FnEnvCorresponds hψwf opInterp ufInterp)
    -- (1b) `d`'s own correspondence, at the canonical resolved UF signature:
    (hcorr : cast (tyDenote_arrow_eq_UFDenote' hbwf.baseTysToTermTypes_eq hrty)
              (opInterp d.name ((List.foldr LMonoTy.arrow d.retTy d.argTys).substTyVars simpTyVarVal))
            = ufInterp ⟨d.name, bvs.map (·.ty), smtRty⟩) :
    IF.UFConsistent ⟨d.name, bvs, smtRty, ifbody⟩ htc ufInterp divByZero modByZero := by
  unfold IF.UFConsistent
  intro hl
  have henc := hbwf.baseTysToTermTypes_eq
  -- (3) LHS: `UF.applyDenoteTyped σ 𝒜 uf (ufInterp uf) hl`. `IF.toUF` reduces to the canonical
  -- UF signature; then rewrite via correspondence (1b) and the bridge.
  simp only [IF.toUF, UF.applyDenoteTyped]
  rw [← hcorr]
  rw [applyBVarVal_eq_applyDenoteTyped' d.argTys bvs henc hrty _ hl]
  -- (2): the applied head equals the (cast) body denotation.
  rw [hcons (hlToBVarVal d.argTys bvs henc hl)]
  -- toSMTTerm_sound: the two body denotations coincide, using the callee
  -- correspondence `hopenv` supplied for `Ψ`.
  have hbenv : BVarEnvCorresponds hbwf (hlToBVarVal d.argTys bvs henc hl) (hlToEnv bvs hl) :=
    hlToBVarVal_hlToEnv_corresponds d.argTys bvs hbwf henc hl
  have h_sound := toSMTTerm_sound hbody (HasSimpType_implies_HasTypeA hbody)
    (baseTyToTermType_isBase hrty) opInterp hop fvarVal (hlToBVarVal d.argTys bvs henc hl)
    htc ufInterp (hlToEnv bvs hl)
    hufwf h_bridge hrty huwf hψwf hbwf hfenv hopenv hbenv
  rw [h_sound]

/-! ## Fvar-side nullary consistency bridge (for `.det` variable definitions)

A `.det init x := e` variable definition is FVAR-SIDE: `x` is referenced as `.fvar`, resolved through
`Φ`/`fvarVal`/`FVarEnvCorresponds`, and emitted as `define-fun x () τ e` = a NULLARY
`IF ⟨x, [], smtτ, ifbody⟩`. Its `define-fun` contract (`IF.UFConsistent`) is derived from
correspondence (1, fvar-side `FVarEnvCorresponds`) + the pinning `fvarVal x = simpDenote e` (a
hypothesis on the ASSIGNMENT `fvarVal`) + `toSMTTerm_sound`. This is the fvar analog of
`UFConsistent_of_OpConsistent'`, but NULLARY
(`Δ = []`, `bvs = []`, closed body): no `applyBVarVal ↔ UF.applyDenoteTyped'`, no non-trivial
`BVarCtxWF` — just head-correspondence + `toSMTTerm_sound` at the empty contexts. -/

/-! ## Variable definitions (`.det` program variables — the fvar-side dual of `FnDef`)

A `VarDef` is the fvar-side counterpart of a `FnDef`: same `name`/`ty`/`body` shape, but its body is
CLOSED (nullary, `Δ = []`) and it denotes through `fvarVal` (via `VarDef.Consistent`). Keeping it a
SEPARATE structure — rather than a nullary
`FnDef` — is what lets the encoder select the fvar-side consistency bridge
(`UFConsistent_of_VarConsistent'`), and lets the accumulator (`OblCtx`) carry `varDefs : List VarDef`
symmetric to `defs : List FnDef` (the split image of the SMT side's single `fs : IFs`).
`WFIn`/`Consistent`/`WFIn.hasTypeA` are the exact fvar-side duals of
`FnDef.WFIn`/`FnDef.OpConsistent`/`FnDef.WFIn.hasTypeA`. -/

/-- A `.det` variable definition: the (closed) defining body `body` for program variable
    `name` at declared type `ty`. The fvar-side dual of `FnDef`. -/
structure VarDef where
  name : String
  ty   : LMonoTy
  body : Expression.Expr

abbrev VarDefs := List VarDef

/-- **Context-relative well-formedness of a `VarDef`.** Its (closed) body is SMT-encodably
    well-typed in the callee context `(Φ, Ψ)` at `ty`, with the EMPTY bvar context (fvar
    bodies are closed). The fvar-side dual of `FnDef.WFIn`; supplies both the
    `toSMTTerm_sound`/`_typeChecks` precondition and (via `HasSimpType_implies_HasTypeA`) the
    `HasTypeA` that `VarDef.Consistent` consumes. -/
def VarDef.WFIn (Φ : FVarCtx) (Ψ : FnCtx) (v : VarDef) : Prop :=
  LExpr.HasSimpType Φ Ψ [] v.body v.ty

/-- The `HasTypeA` body typing `VarDef.Consistent` needs, DERIVED from `WFIn`. -/
theorem VarDef.WFIn.hasTypeA {Φ : FVarCtx} {Ψ : FnCtx} {v : VarDef}
    (h : v.WFIn Φ Ψ) : LExpr.HasTypeA [] v.body v.ty :=
  HasSimpType_implies_HasTypeA h

/-- **`fvarVal` pins the defined variable `v` to its body** — the fvar-side analog of
    `FnDef.OpConsistent`. The variable's valuation equals the denotation of its (closed)
    defining body. Stated over `htA : HasTypeA [] v.body v.ty` (from `WFIn.hasTypeA`). Nullary
    throughout (`Δ = []`), which is the whole content of the fvar/op difference. -/
def VarDef.Consistent
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (v : VarDef) (htA : LExpr.HasTypeA [] v.body v.ty) : Prop :=
  fvarVal ⟨v.name, ()⟩ (v.ty.substTyVars simpTyVarVal)
    = simpDenote opInterp fvarVal .nil v.body v.ty htA

/-- **Context-relative well-formedness of a list of `VarDef`s.** Every definition is `WFIn`
    in the (full) callee context — the fvar-side dual of `FnDefsWF`. -/
def VarDefsWF (Φ : FVarCtx) (Ψ : FnCtx) (vs : List VarDef) : Prop :=
  ∀ (v : VarDef), v ∈ vs → v.WFIn Φ Ψ

/-- **`fvarVal` is consistent with a list of `VarDef`s** — the fvar-side dual of
    `FnDefs.OpConsistent`. Order-free; takes the context-free body typings `ht` directly. -/
def VarDefs.Consistent
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (vs : List VarDef)
    (ht : ∀ v ∈ vs, LExpr.HasTypeA [] v.body v.ty) : Prop :=
  ∀ (v : VarDef) (hmem : v ∈ vs),
    v.Consistent opInterp fvarVal (ht v hmem)

/-- **(1)+(2) ⟹ (3), per variable-definition (nullary, fvar-side).** The exact fvar-side dual
    of `UFConsistent_of_OpConsistent'`: takes a `VarDef v` and its bundled `v.Consistent`
    (the pinning (2)), plus fvar-side correspondence (1) `cast (fvarVal v.name) =
    ufInterp ⟨v.name, [], smtτ⟩`, and yields the `define-fun` contract (3)
    `IF.UFConsistent ⟨v.name, [], smtτ, ifbody⟩`. Chains, at the (empty) argument HList:
    `UF.applyDenoteTyped σ 𝒜 (ufInterp uf) .nil = ufInterp uf =[1] cast (fvarVal v.name) =[2]
    cast (simpDenote v.body) =[toSMTTerm_sound] Term.denoteTyped ifbody`. `Δ = []`/`bvs = []`
    throughout (closed body). -/
theorem UFConsistent_of_VarConsistent'
    -- ── LExpr (source) side ──
    {Φ : FVarCtx} {Ψ : FnCtx} (v : VarDef)
    (hbase : LExpr.MonoTyIsBase v.ty)
    (hbody : LExpr.HasSimpType Φ Ψ [] v.body v.ty)
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    -- (2) consistency (pure Lambda-side):
    (hcons : v.Consistent opInterp fvarVal (HasSimpType_implies_HasTypeA hbody))
    -- ── SMT (target) side ──
    {ufs : UFCtx} {smtτ : TermType} {ifbody : Term}
    (htc : Term.typeCheck ⟨[], ufs, []⟩ ifbody = .ok smtτ)
    (ufInterp : UFInterp σ 𝒜)
    (hufwf : UFCtxWF ufs)
    -- ── correspondence (source ↔ target) ──
    (h_bridge : toSMTTerm [] v.body = .ok ifbody)
    (hτ : baseTyToTermType v.ty = some smtτ)
    (huwf : FNameCtxWF Φ ufs) (hψwf : FNameCtxWF Ψ ufs)
    (hfenv : FVarEnvCorresponds huwf fvarVal ufInterp)
    -- (1a) callee correspondence: a `.det` body may call UDFs, so its `Ψ` callees supply their
    -- correspondence here (`Ψ = []` recovers the callee-free case via `FnEnvCorresponds.nil`):
    (hopenv : FnEnvCorresponds hψwf opInterp ufInterp)
    -- (1b) `v`'s own correspondence, at the canonical resolved UF signature `⟨v.name, [], smtτ⟩`:
    (hcorr : cast (tyDenote_eq_smtTyDenote (σ := σ) hbase hτ)
              (fvarVal ⟨v.name, ()⟩ (v.ty.substTyVars simpTyVarVal))
            = ufInterp ⟨v.name, [], smtτ⟩) :
    IF.UFConsistent ⟨v.name, [], smtτ, ifbody⟩ htc ufInterp divByZero modByZero := by
  unfold IF.UFConsistent
  intro hl
  -- nullary: `hl : HList (TermType.denoteTyped σ 𝒜) [] = .nil`; the UF application reduces to `ufInterp uf`.
  have hnil : hl = .nil := by cases hl; rfl
  subst hnil
  simp only [IF.toUF, UF.applyDenoteTyped, UF.applyDenoteTyped', List.map_nil]
  -- (1b): `ufInterp ⟨v.name,[],smtτ⟩ = cast (fvarVal v.name)`.
  rw [← hcorr]
  -- (2): the pinning (`VarDef.Consistent`) replaces `fvarVal v.name` by `simpDenote v.body`.
  rw [show v.Consistent opInterp fvarVal (HasSimpType_implies_HasTypeA hbody) from hcons]
  -- toSMTTerm_sound: the two body denotations coincide. The bvar context is `[]` (its three
  -- fields vacuous at the empty lists); the callee context `Ψ` is supplied by `hopenv`.
  have hbwf : BVarCtxWF [] [] := ⟨rfl, by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  have hbenv : BVarEnvCorresponds hbwf (.nil) (hlToEnv (σ := σ) (𝒜 := 𝒜) [] .nil) := by
    intro i τ' hbase' hlook; exact absurd hlook (by simp)
  have h_sound := toSMTTerm_sound hbody (HasSimpType_implies_HasTypeA hbody) hbase
    opInterp hop fvarVal .nil htc ufInterp (hlToEnv (σ := σ) [] .nil)
    hufwf h_bridge hτ huwf hψwf hbwf hfenv hopenv hbenv
  rw [h_sound]
