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
# `LExpr`-to-SMT translation with free variables as nullary UFs

This file defines a translation from a simply-typed fragment of Core `LExpr` expressions into
SMT `Term`s in which free variables are encoded as nullary uninterpreted functions (UFs),
matching the representation used by `SMTEncoder`. It provides a type checker and a denotational
semantics for both sides and proves the translation type-preserving and semantics-preserving.

Design:
- Free variables (from `varDecl` / `.init`) translate to `Term.app (.core (.uf ...)) [] smtTy`.
- Bound variables (from quantifiers) translate to `Term.var v`.
- These occupy distinct syntactic forms in the `Term` type, eliminating structural collision.
- A `no_shadow` condition on `BVarCtxWF` prevents bound-variable names from coinciding with UF
  names, reflecting the encoder's guarantee that shadowing is avoided.

SMT-LIB correspondence:
- Free vars correspond to top-level `(declare-const x Int)` commands.
- Bound vars correspond to quantifier bindings `(forall ((x Int)) ...)`.
- The `no_shadow` condition reflects that the encoder renames bound vars to avoid shadowing
  declared symbols.

Key definitions: `LExpr.HasSimpType`, `toSMTTerm`, `Term.typeCheck`, `SMTTerm.denote`.
Key results: `toSMTTerm_typeChecks` (type preservation) and `toSMTTerm_sound` (semantic
soundness).
-/

open Core Lambda Imperative Strata.SMT Std

/-! ## Restrictions on LExpr types and operators -/

inductive LExpr.MonoTyIsBase : LMonoTy → Prop where
  | bool : MonoTyIsBase (.tcons "bool" [])
  | int : MonoTyIsBase (.tcons "int" [])
  | string : MonoTyIsBase (.tcons "string" [])
  | bitvec : MonoTyIsBase (.bitvec n)

inductive LExpr.OpIsSimp1 : CoreOp → LMonoTy → LMonoTy → Prop where
  | intNeg : OpIsSimp1 (.numeric ⟨.int, .Neg⟩) (.tcons "int" []) (.tcons "int" [])
  | boolNot : OpIsSimp1 (.bool .Not) (.tcons "bool" []) (.tcons "bool" [])

inductive LExpr.OpIsSimp2 : CoreOp → LMonoTy → LMonoTy → LMonoTy → Prop where
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
  | intLt : OpIsSimp2 (.numeric ⟨.int, .Lt⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "bool" [])
  | intLe : OpIsSimp2 (.numeric ⟨.int, .Le⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "bool" [])
  | intGt : OpIsSimp2 (.numeric ⟨.int, .Gt⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "bool" [])
  | intGe : OpIsSimp2 (.numeric ⟨.int, .Ge⟩) (.tcons "int" []) (.tcons "int" []) (.tcons "bool" [])
  | boolAnd : OpIsSimp2 (.bool .And) (.tcons "bool" []) (.tcons "bool" []) (.tcons "bool" [])
  | boolOr : OpIsSimp2 (.bool .Or) (.tcons "bool" []) (.tcons "bool" []) (.tcons "bool" [])
  | boolImplies : OpIsSimp2 (.bool .Implies) (.tcons "bool" []) (.tcons "bool" []) (.tcons "bool" [])
  | boolEquiv : OpIsSimp2 (.bool .Equiv) (.tcons "bool" []) (.tcons "bool" []) (.tcons "bool" [])

/-! ## Typing judgment with free variables -/

abbrev FVarCtx := List (String × LMonoTy)

inductive LExpr.HasSimpType (Φ : FVarCtx) : List LMonoTy → Expression.Expr → LMonoTy → Prop where
  | const : MonoTyIsBase c.ty → HasSimpType Φ Δ (.const () c) c.ty
  | bvar : Δ[i]? = some τ → MonoTyIsBase τ → HasSimpType Φ Δ (.bvar () i) τ
  | fvar : (f.name, τ) ∈ Φ → MonoTyIsBase τ →
    HasSimpType Φ Δ (.fvar () f (some τ)) τ
  | app1 : OpIsSimp1 (CoreOp.ofString o.name) aty rty →
    HasSimpType Φ Δ arg aty →
    HasSimpType Φ Δ (.app () (.op () o (some (.tcons "arrow" [aty, rty]))) arg) rty
  | app2 : OpIsSimp2 (CoreOp.ofString o.name) aty1 aty2 rty →
    HasSimpType Φ Δ arg1 aty1 →
    HasSimpType Φ Δ arg2 aty2 →
    HasSimpType Φ Δ (.app () (.app () (.op () o (some (.tcons "arrow" [aty1, .tcons "arrow" [aty2, rty]]))) arg1) arg2) rty
  | ite : HasSimpType Φ Δ c (.tcons "bool" []) → HasSimpType Φ Δ t τ →
    HasSimpType Φ Δ e τ → HasSimpType Φ Δ (.ite () c t e) τ
  | eq : MonoTyIsBase τ → HasSimpType Φ Δ e1 τ → HasSimpType Φ Δ e2 τ →
    HasSimpType Φ Δ (.eq () e1 e2) (.tcons "bool" [])
  | quant : MonoTyIsBase qty → HasSimpType Φ (qty :: Δ) body (.tcons "bool" []) →
    HasSimpType Φ Δ (.quant () k name (some qty) (.const () (.boolConst true)) body) (.tcons "bool" [])

theorem HasSimpType_implies_HasTypeA :
    {Φ : FVarCtx} → {Δ : List LMonoTy} → {e : Expression.Expr} → {τ : LMonoTy} →
    LExpr.HasSimpType Φ Δ e τ → LExpr.HasTypeA Δ e τ := by
  intro Φ Δ e τ h
  induction h with
  | const _ => exact .const
  | bvar hi _ => exact .bvar hi
  | fvar _ _ => exact .fvar
  | app1 _ _ ih_arg => exact .app .op ih_arg
  | app2 _ _ _ ih1 ih2 => exact .app (.app .op ih1) ih2
  | ite _ _ _ ihc iht ihe => exact .ite ihc iht ihe
  | eq _ _ _ ih1 ih2 => exact .eq ih1 ih2
  | quant _ _ ih_body => exact .quant (by exact .const) ih_body

theorem HasSimpType_result_isBase {Φ : FVarCtx} {Δ : List LMonoTy} {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Φ Δ e τ) : LExpr.MonoTyIsBase τ := by
  induction he with
  | const hbase => exact hbase
  | bvar _ hbase => exact hbase
  | fvar _ hbase => exact hbase
  | app1 hop _ _ =>
    generalize CoreOp.ofString _ = cop at hop
    cases hop with | intNeg => exact .int | boolNot => exact .bool
  | app2 hop _ _ _ _ =>
    generalize CoreOp.ofString _ = cop at hop
    cases hop <;> first | exact .int | exact .bool
  | ite _ _ _ _ iht _ => exact iht
  | eq _ _ _ _ _ => exact .bool
  | quant _ _ _ => exact .bool

/-! ## LExpr denotation (parameterized by `opInterp` and `fvarVal`) -/

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

/-! ## SMT translation: `LExpr` to `Term` (nullary UFs for free variables) -/

abbrev UFCtx := List UF
abbrev BoundVars := List TermVar

def monoTyToTermType : LMonoTy → Option TermType
  | .tcons "bool" [] => some .bool
  | .tcons "int" [] => some .int
  | .bitvec n => some (.bitvec n)
  | .tcons "string" [] => some .string
  | _ => none

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

def toSMTTerm (ufs : UFCtx) (bvs : BoundVars) : Expression.Expr → Except Format Term
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
  | .fvar () f (some ty) =>
    match monoTyToTermType ty with
    | some smtTy =>
      let uf : UF := ⟨f.name, [], smtTy⟩
      if uf ∈ ufs then .ok (.app (.core (.uf uf)) [] smtTy)
      else .error f!"Free variable not in context: {f.name}"
    | none => .error f!"Cannot encode free variable type: {repr ty}"
  | .eq () e1 e2 => do
    let t1 ← toSMTTerm ufs bvs e1
    let t2 ← toSMTTerm ufs bvs e2
    .ok (Term.app (.core .eq) [t1, t2] .bool)
  | .ite () c t e => do
    let ct ← toSMTTerm ufs bvs c
    let tt ← toSMTTerm ufs bvs t
    let et ← toSMTTerm ufs bvs e
    .ok (Term.app (.core .ite) [ct, tt, et] (Term.typeOf tt))
  | .app () (.op () fn (some _)) e1 =>
    match corePredefinedOpToSMTOp (CoreOp.ofString fn.name) with
    | some (builder, retTy) => do
      let t1 ← toSMTTerm ufs bvs e1
      .ok (builder [t1] retTy)
    | none => .error f!"Unsupported op: {fn.name}"
  | .app () (.app () (.op () fn (some _)) e1) e2 =>
    match corePredefinedOpToSMTOp (CoreOp.ofString fn.name) with
    | some (builder, retTy) => do
      let t1 ← toSMTTerm ufs bvs e1
      let t2 ← toSMTTerm ufs bvs e2
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
    let bodyTm ← toSMTTerm ufs bvs' body
    let smtKind : Strata.SMT.QuantifierKind := match k with
      | .all => .all | .exist => .exist
    .ok (.quant smtKind [v] [] bodyTm)
  | e => .error f!"Unsupported expression: {repr e}"

/-! ## SMT type checker (over a bound-variable context and UF declarations) -/

mutual
def Term.typeCheck (ufs : UFCtx) (Γ : List TermVar) : Term → Option TermType
  | .prim p => some p.typeOf
  | .var v => if v ∈ Γ then some v.ty else none
  | .app (.core (.uf uf)) [] _ =>
    if uf ∈ ufs then some uf.out else none
  | .app (.core .not) [t] _ => do
    let tTy ← typeCheck ufs Γ t
    if tTy == .bool then some .bool else none
  | .app (.core .and) [t1, t2] _ | .app (.core .or) [t1, t2] _
  | .app (.core .implies) [t1, t2] _ => do
    let ty1 ← typeCheck ufs Γ t1
    let ty2 ← typeCheck ufs Γ t2
    if ty1 == .bool && ty2 == .bool then some .bool else none
  | .app (.core .eq) [t1, t2] _ => do
    let ty1 ← typeCheck ufs Γ t1
    let ty2 ← typeCheck ufs Γ t2
    if ty1 == ty2 then some .bool else none
  | .app (.core .ite) [c, t, e] _ => do
    let cTy ← typeCheck ufs Γ c
    let tTy ← typeCheck ufs Γ t
    let eTy ← typeCheck ufs Γ e
    if cTy == .bool && tTy == eTy then some tTy else none
  | .app (.num .neg) [t] _ => do
    let tTy ← typeCheck ufs Γ t
    if tTy == .int then some .int else none
  | .app (.num .add) [t1, t2] _ | .app (.num .sub) [t1, t2] _
  | .app (.num .mul) [t1, t2] _ | .app (.num .div) [t1, t2] _
  | .app (.num .mod) [t1, t2] _ => do
    let ty1 ← typeCheck ufs Γ t1
    let ty2 ← typeCheck ufs Γ t2
    if ty1 == .int && ty2 == .int then some .int else none
  | .app (.num .le) [t1, t2] _ | .app (.num .lt) [t1, t2] _
  | .app (.num .ge) [t1, t2] _ | .app (.num .gt) [t1, t2] _ => do
    let ty1 ← typeCheck ufs Γ t1
    let ty2 ← typeCheck ufs Γ t2
    if ty1 == .int && ty2 == .int then some .bool else none
  | .app (.core .distinct) ts _ => do
    let _ ← typeCheckAllSame ufs Γ ts
    some .bool
  | .quant _ vs [] body => do
    let bodyTy ← typeCheck ufs (vs ++ Γ) body
    if bodyTy == .bool then some .bool else none
  | _ => none

def Term.typeCheckAllSame (ufs : UFCtx) (Γ : List TermVar) : List Term → Option TermType
  | [] => some .bool
  | [t] => typeCheck ufs Γ t
  | t :: rest => do
    let ty ← typeCheck ufs Γ t
    let ty' ← typeCheckAllSame ufs Γ rest
    if ty == ty' then some ty else none
end

/-! ## Well-formedness conditions -/

structure BVarCtxWF (Δ : List LMonoTy) (bvs : BoundVars) (ufs : UFCtx) : Prop where
  len_eq : Δ.length = bvs.length
  ty_eq : ∀ i (hi : i < Δ.length), monoTyToTermType Δ[i] = some (bvs[i]'(by omega)).ty
  id_scheme : ∀ i (hi : i < bvs.length), (bvs[i]'hi).id = s!"$__bv{bvs.length - 1 - i}"
  no_shadow : ∀ n : Nat, s!"$__bv{n}" ∉ ufs.map (·.id)

structure UFCtxWF (Φ : FVarCtx) (ufs : UFCtx) : Prop where
  len_eq : Φ.length = ufs.length
  ty_eq : ∀ i (hi : i < Φ.length), monoTyToTermType (Φ[i]).2 = some (ufs[i]'(by omega)).out
  id_eq : ∀ i (hi : i < Φ.length), (Φ[i]).1 = (ufs[i]'(by omega)).id
  nullary : ∀ i (hi : i < ufs.length), (ufs[i]'hi).args = []

/-! ## Sort-correctness: well-typed LExprs produce well-sorted SMT terms -/

private theorem MonoTyIsBase_monoTyToTermType {τ : LMonoTy}
    (h : LExpr.MonoTyIsBase τ) : ∃ sty, monoTyToTermType τ = some sty := by
  cases h with
  | bool => exact ⟨.bool, rfl⟩
  | int => exact ⟨.int, rfl⟩
  | string => exact ⟨.string, rfl⟩
  | bitvec => exact ⟨_, rfl⟩

private theorem UFCtxWF_mem {Φ : FVarCtx} {ufs : UFCtx}
    (huwf : UFCtxWF Φ ufs) {name : String} {τ : LMonoTy} {smtTy : TermType}
    (hmem : (name, τ) ∈ Φ) (hty : monoTyToTermType τ = some smtTy)
    : (⟨name, [], smtTy⟩ : UF) ∈ ufs := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < Φ.length := hi
  have hi_ufs : i < ufs.length := huwf.len_eq ▸ hi'
  have hid := huwf.id_eq i hi'
  have htyeq := huwf.ty_eq i hi'
  have hnull := huwf.nullary i hi_ufs
  have hget_fst : (Φ[i]).1 = name := congrArg Prod.fst hget
  have hget_snd : (Φ[i]).2 = τ := congrArg Prod.snd hget
  rw [hget_snd] at htyeq
  rw [hty] at htyeq; simp at htyeq
  have heq : ufs[i] = ⟨name, [], smtTy⟩ := by
    have h1 : (ufs[i]).id = name := by rw [← hid]; exact hget_fst
    have h2 : (ufs[i]).args = [] := hnull
    have h3 : (ufs[i]).out = smtTy := htyeq.symm
    exact match ufs[i], h1, h2, h3 with | ⟨_, _, _⟩, rfl, rfl, rfl => rfl
  exact heq ▸ List.getElem_mem hi_ufs

theorem toSMTTerm_typeChecks
    {Φ : FVarCtx} {ufs : UFCtx} {Δ : List LMonoTy} {bvs : BoundVars}
    (huwf : UFCtxWF Φ ufs) (hbwf : BVarCtxWF Δ bvs ufs)
    (e : Expression.Expr) (τ : LMonoTy) (smtTy : TermType)
    (he : LExpr.HasSimpType Φ Δ e τ)
    (tm : Term) (h_ok : toSMTTerm ufs bvs e = .ok tm)
    (hτ : monoTyToTermType τ = some smtTy)
    : Term.typeCheck ufs bvs tm = some smtTy := by
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
      have hwfty := hbwf.ty_eq i hleni
      have hget : Δ'[i] = τ' := (List.getElem?_eq_some_iff.mp hlook).2
      rw [hget] at hwfty
      rw [hwfty] at hτ; simp at hτ; exact hτ
    · simp at h_ok
  | fvar hmemΦ hbase =>
    simp only [toSMTTerm] at h_ok
    rw [hτ] at h_ok; simp only at h_ok
    have huf_mem : (⟨_, [], smtTy⟩ : UF) ∈ ufs := UFCtxWF_mem huwf hmemΦ hτ
    simp [huf_mem, Except.ok.injEq] at h_ok
    subst h_ok
    simp [Term.typeCheck, huf_mem]
  | app1 hop _ ih_arg =>
    simp only [toSMTTerm] at h_ok
    generalize hcop : CoreOp.ofString _ = cop at hop h_ok
    cases hop with
    | intNeg =>
      simp [corePredefinedOpToSMTOp] at h_ok
      simp [monoTyToTermType] at hτ; subst hτ
      revert h_ok
      cases h_arg : toSMTTerm ufs bvs _ with
      | error _ => simp [bind, Except.bind]
      | ok t_arg =>
        simp [bind, Except.bind]
        intro h_tm; subst h_tm
        simp only [Term.typeCheck]
        have ih := ih_arg hbwf .int t_arg h_arg (by simp [monoTyToTermType])
        simp [ih, bind, Option.bind]
    | boolNot =>
      simp [corePredefinedOpToSMTOp] at h_ok
      simp [monoTyToTermType] at hτ; subst hτ
      revert h_ok
      cases h_arg : toSMTTerm ufs bvs _ with
      | error _ => simp [bind, Except.bind]
      | ok t_arg =>
        simp [bind, Except.bind]
        intro h_tm; subst h_tm
        simp only [Term.typeCheck]
        have ih := ih_arg hbwf .bool t_arg h_arg (by simp [monoTyToTermType])
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
      cases h1 : toSMTTerm ufs bvs _ with
      | error _ => simp [bind, Except.bind]
      | ok t1 =>
        cases h2 : toSMTTerm ufs bvs _ with
        | error _ => simp [bind, Except.bind]
        | ok t2 =>
          simp [bind, Except.bind]
          intro h_tm; subst h_tm; simp only [Term.typeCheck]
          simp [ih_arg1 hbwf _ _ h1 rfl, ih_arg2 hbwf _ _ h2 rfl, bind, Option.bind]
  | ite _ _ _ ihc iht ihe =>
    simp only [toSMTTerm] at h_ok
    revert h_ok
    cases hc : toSMTTerm ufs bvs _ with
    | error _ => simp [bind, Except.bind]
    | ok ct =>
      cases ht : toSMTTerm ufs bvs _ with
      | error _ => simp [bind, Except.bind]
      | ok tt_tm =>
        cases he : toSMTTerm ufs bvs _ with
        | error _ => simp [bind, Except.bind]
        | ok et =>
          simp [bind, Except.bind]
          intro h_tm; subst h_tm
          simp only [Term.typeCheck]
          have ih_c := ihc hbwf .bool ct hc (by simp [monoTyToTermType])
          have ih_t := iht hbwf smtTy tt_tm ht hτ
          have ih_e := ihe hbwf smtTy et he hτ
          simp [ih_c, ih_t, ih_e, bind, Option.bind, beq_iff_eq]
  | eq hbase _ _ ih1 ih2 =>
    simp [monoTyToTermType] at hτ; subst hτ
    simp only [toSMTTerm, bind, Except.bind] at h_ok
    revert h_ok
    cases ha : toSMTTerm ufs bvs _ with
    | error _ => simp
    | ok t1 =>
      cases hb : toSMTTerm ufs bvs _ with
      | error _ => simp
      | ok t2 =>
        simp
        intro h_tm; subst h_tm
        simp only [Term.typeCheck]
        cases hbase with
        | bool =>
          have htc1 := ih1 hbwf .bool t1 ha (by rfl)
          have htc2 := ih2 hbwf .bool t2 hb (by rfl)
          rw [htc1, htc2]; simp [bind, Option.bind]
        | int =>
          have htc1 := ih1 hbwf .int t1 ha (by rfl)
          have htc2 := ih2 hbwf .int t2 hb (by rfl)
          rw [htc1, htc2]; simp [bind, Option.bind]
        | string =>
          have htc1 := ih1 hbwf .string t1 ha (by rfl)
          have htc2 := ih2 hbwf .string t2 hb (by rfl)
          rw [htc1, htc2]; simp [bind, Option.bind]
        | bitvec =>
          have htc1 := ih1 hbwf _ t1 ha (by rfl)
          have htc2 := ih2 hbwf _ t2 hb (by rfl)
          rw [htc1, htc2]; simp [bind, Option.bind]
  | quant hbase _ ih_body =>
    simp only [monoTyToTermType, Option.some.injEq] at hτ; subst hτ
    obtain ⟨smtQTy, hqty⟩ := MonoTyIsBase_monoTyToTermType hbase
    simp only [toSMTTerm] at h_ok
    rw [hqty] at h_ok; simp only at h_ok
    revert h_ok
    cases hbody : toSMTTerm ufs (⟨s!"$__bv{bvs.length}", smtQTy⟩ :: bvs) _ with
    | error _ => simp [bind, Except.bind]
    | ok bodyTm =>
      simp [bind, Except.bind]
      intro h_tm; subst h_tm
      simp only [Term.typeCheck, List.singleton_append, bind, Option.bind]
      have hbwf' : BVarCtxWF (_ :: _) (⟨s!"$__bv{bvs.length}", smtQTy⟩ :: bvs) ufs :=
        ⟨congrArg (· + 1) hbwf.len_eq, fun i hi => by
          cases i with
          | zero => exact hqty
          | succ j =>
            simp only [List.length, Nat.succ_lt_succ_iff] at hi
            simp only [List.getElem_cons_succ]
            exact hbwf.ty_eq j hi,
         fun i hi => by
          cases i with
          | zero => simp [List.length]
          | succ j =>
            simp only [List.getElem_cons_succ, List.length] at hi ⊢
            have hj_lt : j < bvs.length := by omega
            have := hbwf.id_scheme j hj_lt
            rw [this]; simp; congr 1; omega,
         hbwf.no_shadow⟩
      have ih := ih_body hbwf' _ bodyTm hbody rfl
      change Term.typeCheck ufs (⟨s!"$__bv{bvs.length}", smtQTy⟩ :: bvs) bodyTm = some .bool at ih
      have hts : (toString "$__bv" : String) = "$__bv" := rfl
      have htn : toString (List.length bvs) = (List.length bvs).repr := rfl
      simp only [hts, htn] at *
      rw [ih]; simp

/-! ## SMT type and term denotation -/

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

/-- Any type in the image of `monoTyToTermType` is a base SMT type. -/
theorem monoTyToTermType_SMTTyIsBase {τ : LMonoTy} {sty : TermType}
    (h : monoTyToTermType τ = some sty) : SMTTyIsBase sty := by
  cases τ with
  | tcons name args =>
    simp only [monoTyToTermType] at h
    split at h <;> simp at h
    all_goals (subst h; first | exact .bool | exact .int | exact .string | exact .bitvec)
  | bitvec n => simp [monoTyToTermType] at h; subst h; exact .bitvec
  | _ => simp [monoTyToTermType] at h

/-- Variable environment for SMT: maps bound variables to values. -/
def SMTVarEnv (Γ : List TermVar) := ∀ v, v ∈ Γ → SMTTyDenote v.ty

def SMTVarEnv.empty : SMTVarEnv [] := fun _ h => nomatch h

def SMTVarEnv.cons {v : TermVar} (val : SMTTyDenote v.ty) (env : SMTVarEnv Γ) :
    SMTVarEnv (v :: Γ) :=
  fun w hmem =>
    if h : w = v then h ▸ val
    else env w (by cases hmem with | head => exact absurd rfl h | tail _ htl => exact htl)

/-- UF interpretation: maps each declared nullary UF to a value of its output type. -/
def UFInterp (ufs : UFCtx) := ∀ uf, uf ∈ ufs → SMTTyDenote uf.out

private theorem tc_prim_inv {Γ : List TermVar} {ufs : UFCtx} {p : TermPrim} {τ : TermType}
    (h : Term.typeCheck ufs Γ (.prim p) = some τ) : τ = p.typeOf := by
  simp [Term.typeCheck] at h; exact h.symm

private theorem tc_var_inv {Γ : List TermVar} {ufs : UFCtx} {v : TermVar} {τ : TermType}
    (h : Term.typeCheck ufs Γ (.var v) = some τ) : v ∈ Γ ∧ v.ty = τ := by
  simp [Term.typeCheck] at h; exact h

private theorem tc_uf_inv {Γ : List TermVar} {ufs : UFCtx} {uf : UF} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core (.uf uf)) [] rty) = some τ) :
    uf ∈ ufs ∧ uf.out = τ := by
  simp [Term.typeCheck] at h; exact h

private theorem tc_not_inv {Γ : List TermVar} {ufs : UFCtx} {t : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core .not) [t] rty) = some τ) :
    Term.typeCheck ufs Γ t = some .bool ∧ τ = .bool := by
  simp only [Term.typeCheck] at h
  revert h
  cases h1 : Term.typeCheck ufs Γ t with
  | none => simp [bind, Option.bind]
  | some ty1 =>
    simp only [bind, Option.bind]
    intro h'
    split at h' <;> simp_all

private theorem tc_boolBin_inv {Γ : List TermVar} {ufs : UFCtx} {op : Op.Core}
    {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core op) [t1, t2] rty) = some τ)
    (hop : op = .and ∨ op = .or ∨ op = .implies) :
    Term.typeCheck ufs Γ t1 = some .bool ∧ Term.typeCheck ufs Γ t2 = some .bool ∧ τ = .bool := by
  rcases hop with rfl | rfl | rfl <;> {
    simp only [Term.typeCheck] at h
    revert h
    cases h1 : Term.typeCheck ufs Γ t1 with
    | none => simp [bind, Option.bind]
    | some ty1 =>
      cases h2 : Term.typeCheck ufs Γ t2 with
      | none => simp [bind, Option.bind]
      | some ty2 =>
        simp only [bind, Option.bind]
        intro h'
        split at h' <;> simp_all
  }

private def tc_eq_inv {Γ : List TermVar} {ufs : UFCtx} {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core .eq) [t1, t2] rty) = some τ) :
    Σ' τ', Term.typeCheck ufs Γ t1 = some τ' ∧ Term.typeCheck ufs Γ t2 = some τ' ∧ τ = .bool := by
  simp only [Term.typeCheck] at h
  revert h
  cases h1 : Term.typeCheck ufs Γ t1 with
  | none => simp [bind, Option.bind]; exact fun h => absurd h (by trivial)
  | some ty1 =>
    cases h2 : Term.typeCheck ufs Γ t2 with
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

private theorem tc_ite_inv {Γ : List TermVar} {ufs : UFCtx} {c t e : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core .ite) [c, t, e] rty) = some τ) :
    Term.typeCheck ufs Γ c = some .bool ∧ Term.typeCheck ufs Γ t = some τ ∧
    Term.typeCheck ufs Γ e = some τ := by
  simp only [Term.typeCheck] at h
  revert h
  cases hc : Term.typeCheck ufs Γ c with
  | none => simp [bind, Option.bind]
  | some tyc =>
    cases ht : Term.typeCheck ufs Γ t with
    | none => simp [bind, Option.bind]
    | some tyt =>
      cases he : Term.typeCheck ufs Γ e with
      | none => simp [bind, Option.bind]
      | some tye =>
        simp only [bind, Option.bind]
        intro h'
        split at h' <;> simp_all

private theorem tc_intUn_inv {Γ : List TermVar} {ufs : UFCtx} {t : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.num .neg) [t] rty) = some τ) :
    Term.typeCheck ufs Γ t = some .int ∧ τ = .int := by
  simp only [Term.typeCheck] at h
  revert h
  cases h1 : Term.typeCheck ufs Γ t with
  | none => simp [bind, Option.bind]
  | some ty1 =>
    simp only [bind, Option.bind]
    intro h'
    split at h' <;> simp_all

private theorem tc_intBin_inv {Γ : List TermVar} {ufs : UFCtx} {op : Op.Num}
    {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.num op) [t1, t2] rty) = some τ)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod) :
    Term.typeCheck ufs Γ t1 = some .int ∧ Term.typeCheck ufs Γ t2 = some .int ∧ τ = .int := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> {
    simp only [Term.typeCheck] at h
    revert h
    cases h1 : Term.typeCheck ufs Γ t1 with
    | none => simp [bind, Option.bind]
    | some ty1 =>
      cases h2 : Term.typeCheck ufs Γ t2 with
      | none => simp [bind, Option.bind]
      | some ty2 =>
        simp only [bind, Option.bind]
        intro h'
        split at h' <;> simp_all
  }

private theorem tc_intCmp_inv {Γ : List TermVar} {ufs : UFCtx} {op : Op.Num}
    {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.num op) [t1, t2] rty) = some τ)
    (hop : op = .le ∨ op = .lt ∨ op = .ge ∨ op = .gt) :
    Term.typeCheck ufs Γ t1 = some .int ∧ Term.typeCheck ufs Γ t2 = some .int ∧ τ = .bool := by
  rcases hop with rfl | rfl | rfl | rfl <;> {
    simp only [Term.typeCheck] at h
    revert h
    cases h1 : Term.typeCheck ufs Γ t1 with
    | none => simp [bind, Option.bind]
    | some ty1 =>
      cases h2 : Term.typeCheck ufs Γ t2 with
      | none => simp [bind, Option.bind]
      | some ty2 =>
        simp only [bind, Option.bind]
        intro h'
        split at h' <;> simp_all
  }

private theorem tc_distinct_inv {Γ : List TermVar} {ufs : UFCtx} {ts : List Term}
    {rty τ : TermType}
    (h : Term.typeCheck ufs Γ (.app (.core .distinct) ts rty) = some τ) :
    τ = .bool := by
  simp only [Term.typeCheck] at h
  revert h
  cases hts : Term.typeCheckAllSame ufs Γ ts with
  | none => simp [bind, Option.bind]
  | some _ => simp [bind, Option.bind]; intro h'; exact h'.symm

private theorem tc_quant_inv {Γ : List TermVar} {ufs : UFCtx} {k : Strata.SMT.QuantifierKind}
    {vs : List TermVar} {body : Term} {τ : TermType}
    (h : Term.typeCheck ufs Γ (.quant k vs [] body) = some τ) :
    Term.typeCheck ufs (vs ++ Γ) body = some .bool ∧ τ = .bool := by
  simp only [Term.typeCheck] at h
  revert h
  cases hb : Term.typeCheck ufs (vs ++ Γ) body with
  | none => simp [bind, Option.bind]
  | some tyb =>
    simp only [bind, Option.bind]
    intro h'
    split at h' <;> simp_all

/-- Total denotation of a type-checked SMT term. -/
noncomputable def SMTTerm.denote
    {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp ufs) (env : SMTVarEnv Γ)
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
    cast (by rw [← heq]) (env v hmem)
  | .app (.core (.uf uf)) [] _ =>
    let ⟨hmem, hty⟩ := tc_uf_inv h
    cast (by rw [← hty]) (ufInterp uf hmem)
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
  | .quant k vs [] body =>
    let ⟨hbody, heq⟩ := tc_quant_inv h
    let combinedEnv (ext : SMTVarEnv vs) : SMTVarEnv (vs ++ Γ) :=
      fun v hmem =>
        if hv : v ∈ vs then ext v hv
        else env v (by
          have := List.mem_append.mp hmem
          exact this.resolve_left hv)
    cast (by rw [heq]) (@decide
      (match k with
       | .all => ∀ (ext : SMTVarEnv vs), denote ufInterp (combinedEnv ext) body .bool hbody = true
       | .exist => ∃ (ext : SMTVarEnv vs), denote ufInterp (combinedEnv ext) body .bool hbody = true)
      (Classical.propDecidable _))
  | .app (.core .distinct) _ts _ =>
    have heq := tc_distinct_inv h
    cast (by rw [heq]) true
  | .none _ => False.elim (by simp only [Term.typeCheck] at h; exact absurd h nofun)
  | .some _ => False.elim (by simp only [Term.typeCheck] at h; exact absurd h nofun)

/-! ## Semantic soundness of `toSMTTerm` -/

theorem tyDenote_eq_smtTyDenote {τ : LMonoTy} {smtTy : TermType}
    (hbase : LExpr.MonoTyIsBase τ) (h : monoTyToTermType τ = some smtTy) :
    Lambda.TyDenote simpTcInterp simpTyVarVal τ = SMTTyDenote smtTy := by
  cases hbase with
  | bool => simp [monoTyToTermType] at h; subst h; rfl
  | int => simp [monoTyToTermType] at h; subst h; rfl
  | string => simp [monoTyToTermType] at h; subst h; rfl
  | bitvec => simp [monoTyToTermType] at h; subst h; rfl

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

/-- Correspondence between LExpr bound variable environment and SMT variable environment. -/
def BVarEnvCorresponds
    {Δ : List LMonoTy} {bvs : BoundVars} {ufs : UFCtx}
    (hwf : BVarCtxWF Δ bvs ufs)
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

/-- If monoTyToTermType returns some, the type is base. -/
private theorem monoTyToTermType_isBase {τ : LMonoTy} {sty : TermType}
    (h : monoTyToTermType τ = some sty) : LExpr.MonoTyIsBase τ := by
  cases τ with
  | tcons name args =>
    simp [monoTyToTermType] at h
    split at h <;> simp_all
    all_goals (first | exact .bool | exact .int | exact .string)
  | bitvec n => exact .bitvec
  | _ => simp [monoTyToTermType] at h

/-- Correspondence between LExpr free variable valuation and UF interpretation. -/
def UFEnvCorresponds
    {Φ : FVarCtx} {ufs : UFCtx}
    (huwf : UFCtxWF Φ ufs)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (ufInterp : UFInterp ufs) : Prop :=
  ∀ i (hi : i < Φ.length),
    let hufs : i < ufs.length := huwf.len_eq ▸ hi
    let τ := (Φ[i]).2
    let hty : monoTyToTermType τ = some (ufs[i]'hufs).out := huwf.ty_eq i hi
    cast (tyDenote_eq_smtTyDenote (monoTyToTermType_isBase hty) hty)
      (fvarVal ⟨(Φ[i]).1, ()⟩ (τ.substTyVars simpTyVarVal))
      = ufInterp (ufs[i]'hufs) (List.getElem_mem hufs)

private theorem subst_heq {α : Sort u} {P : α → Sort v} {a b : α}
    (h : a = b) (x : P b) : HEq (h ▸ x) x := by subst h; exact HEq.rfl

/-- SMTTerm.denote for a variable is HEq to the environment lookup. -/
private theorem SMTTerm_denote_var_heq {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp ufs) (env : SMTVarEnv Γ)
    (v : TermVar) (τ : TermType) (htc : Term.typeCheck ufs Γ (.var v) = some τ) :
    HEq (SMTTerm.denote ufInterp env (.var v) τ htc) (env v (tc_var_inv htc).1) := by
  unfold SMTTerm.denote
  obtain ⟨hmem, heq⟩ := tc_var_inv htc
  simp only
  exact cast_heq _ _

/-- SMTTerm.denote for a nullary UF is HEq to the ufInterp lookup. -/
private theorem SMTTerm_denote_uf_heq {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp ufs) (env : SMTVarEnv Γ)
    (uf : UF) (rty τ : TermType)
    (htc : Term.typeCheck ufs Γ (.app (.core (.uf uf)) [] rty) = some τ) :
    HEq (SMTTerm.denote ufInterp env (.app (.core (.uf uf)) [] rty) τ htc)
      (ufInterp uf (tc_uf_inv htc).1) := by
  unfold SMTTerm.denote
  obtain ⟨hmem, hty⟩ := tc_uf_inv htc
  simp only
  exact cast_heq _ _

/-- If two UFs have equal fields, ufInterp applied to them gives HEq results. -/
private theorem ufInterp_heq {ufs : UFCtx} (ufInterp : UFInterp ufs)
    {uf1 uf2 : UF} (hid : uf1.id = uf2.id) (hargs : uf1.args = uf2.args) (hout : uf1.out = uf2.out)
    (hmem1 : uf1 ∈ ufs) (hmem2 : uf2 ∈ ufs) :
    HEq (ufInterp uf1 hmem1) (ufInterp uf2 hmem2) := by
  cases uf1; cases uf2; simp only at hid hargs hout; subst hid; subst hargs; subst hout
  exact heq_of_eq (congrArg (ufInterp _) (proof_irrel _ _))

/-- The choose from MonoTyIsBase_monoTyToTermType gives back the same smtTy as monoTyToTermType. -/
private theorem choose_eq_of_hτ {τ : LMonoTy} {smtTy : TermType}
    (hbase : LExpr.MonoTyIsBase τ) (hτ : monoTyToTermType τ = some smtTy) :
    (MonoTyIsBase_monoTyToTermType hbase).choose = smtTy := by
  have h := (MonoTyIsBase_monoTyToTermType hbase).choose_spec
  rw [h] at hτ; exact Option.some.inj hτ

/-- Convert an IH with opaque `choose` smtTy to one with explicit `smtTy`. -/
private theorem ih_convert_smtTy {Γ : List TermVar} {ufs : UFCtx}
    {ufInterp : UFInterp ufs} {env : SMTVarEnv Γ}
    {tm : Term} {smtTy1 smtTy2 : TermType}
    (h_eq : smtTy1 = smtTy2)
    {x : SMTTyDenote smtTy1} {htc1 : Term.typeCheck ufs Γ tm = some smtTy1}
    (ih : x = SMTTerm.denote ufInterp env tm smtTy1 htc1)
    : HEq x (SMTTerm.denote ufInterp env tm smtTy2 (h_eq ▸ htc1)) := by
  subst h_eq; exact heq_of_eq ih

/-- Helper: cast-wrapped bif corresponds to bif when conditions and branches match via HEq. -/
private theorem bif_heq_of_cond_branches {α β : Type} {b1 : Bool} {b2 : Bool}
    {t1 e1 : α} {t2 e2 : β} (h_ty : α = β)
    (hb : b1 = b2) (ht : HEq t1 t2) (he : HEq e1 e2) :
    cast h_ty (bif b1 then t1 else e1) = (bif b2 then t2 else e2) := by
  subst h_ty; subst hb; cases ht; cases he; cases b1 <;> rfl

/-- Unfolding lemma for SMTTerm.denote on ite. -/
private noncomputable def SMTTerm_denote_ite {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp ufs) (env : SMTVarEnv Γ)
    (c t e : Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck ufs Γ (.app (.core .ite) [c, t, e] rty) = some τ) :
    SMTTerm.denote ufInterp env (.app (.core .ite) [c, t, e] rty) τ htc =
      bif SMTTerm.denote ufInterp env c .bool (tc_ite_inv htc).1
      then SMTTerm.denote ufInterp env t τ (tc_ite_inv htc).2.1
      else SMTTerm.denote ufInterp env e τ (tc_ite_inv htc).2.2 := by
  simp only [SMTTerm.denote]
  obtain ⟨hc, ht, he⟩ := tc_ite_inv htc
  rfl

/-- Unfolding lemma for SMTTerm.denote on eq. -/
private noncomputable def SMTTerm_denote_eq_unfold {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp ufs) (env : SMTVarEnv Γ)
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

/-- SMTTerm.denote is invariant under change of type index when the types are provably equal. -/
private theorem SMTTerm_denote_cast {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp ufs) (env : SMTVarEnv Γ)
    (tm : Term) (τ τ' : TermType)
    (h : Term.typeCheck ufs Γ tm = some τ) (h' : Term.typeCheck ufs Γ tm = some τ')
    (heq : τ = τ') :
    HEq (SMTTerm.denote ufInterp env tm τ h) (SMTTerm.denote ufInterp env tm τ' h') := by
  subst heq; exact heq_of_eq (congrArg (SMTTerm.denote ufInterp env tm τ) (proof_irrel h h'))

/-- Extension lemma for BVarEnvCorresponds. -/
theorem BVarEnvCorresponds_cons
    {Δ : List LMonoTy} {bvs : BoundVars} {ufs : UFCtx}
    {hbwf : BVarCtxWF Δ bvs ufs}
    {bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ}
    {smtEnv : SMTVarEnv bvs}
    (henv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    {qty : LMonoTy} {v : TermVar}
    (hbase : LExpr.MonoTyIsBase qty)
    (hty : monoTyToTermType qty = some v.ty)
    (x : Lambda.TyDenote simpTcInterp simpTyVarVal qty)
    {smtEnv' : SMTVarEnv (v :: bvs)}
    (hnew : smtEnv' v (List.Mem.head _) = cast (tyDenote_eq_smtTyDenote hbase hty) x)
    (hold : ∀ w (hmem : w ∈ bvs), smtEnv' w (List.Mem.tail _ hmem) = smtEnv w hmem)
    (hbwf' : BVarCtxWF (qty :: Δ) (v :: bvs) ufs)
    : BVarEnvCorresponds hbwf' (.cons x bvarVal) smtEnv' := by
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
      have := hbwf.len_eq; have := (List.getElem?_eq_some_iff.mp hlook).1; omega
    have hj1_lt : j + 1 < (v :: bvs).length := by simp; omega
    have hrhs : smtEnv' ((v :: bvs)[j + 1]'hj1_lt)
        (List.getElem_mem hj1_lt)
      = smtEnv (bvs[j]'hj_lt) (List.getElem_mem hj_lt) :=
      hold _ (List.getElem_mem hj_lt)
    rw [hrhs]
    exact henv_j

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

/-- Helper for the app1 case of toSMTTerm_sound. -/
private theorem toSMTTerm_sound_app1
    {Φ : FVarCtx} {ufs : UFCtx} {Δ : List LMonoTy} {bvs : BoundVars}
    (huwf : UFCtxWF Φ ufs) (hbwf : BVarCtxWF Δ bvs ufs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (hop : OpInterpConsistent opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (ufInterp : UFInterp ufs) (smtEnv : SMTVarEnv bvs)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    {o : CoreLParams.Identifier} {arg : Expression.Expr} {aty rty : LMonoTy}
    (hop_ty : LExpr.OpIsSimp1 (CoreOp.ofString o.name) aty rty)
    (h_arg_ty : LExpr.HasSimpType Φ Δ arg aty)
    (ih_arg : ∀ {bvs : BoundVars} (hbwf : BVarCtxWF Δ bvs ufs)
      (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
      (smtEnv : SMTVarEnv bvs),
      BVarEnvCorresponds hbwf bvarVal smtEnv →
      ∀ (tm : Term) (h_ok : toSMTTerm ufs bvs arg = .ok tm),
        let smtTy := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg_ty)).choose
        let hτ := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg_ty)).choose_spec
        let htc := toSMTTerm_typeChecks huwf hbwf arg aty smtTy h_arg_ty tm h_ok hτ
        cast (tyDenote_eq_smtTyDenote (HasSimpType_result_isBase h_arg_ty) hτ)
          (simpDenote opInterp fvarVal bvarVal arg aty (HasSimpType_implies_HasTypeA h_arg_ty))
        = SMTTerm.denote ufInterp smtEnv tm smtTy htc)
    (tm : Term)
    (h_ok : toSMTTerm ufs bvs (.app () (.op () o (some (.tcons "arrow" [aty, rty]))) arg) = .ok tm)
    (hbase_rty : LExpr.MonoTyIsBase rty)
    (smtTy : TermType)
    (hτ : monoTyToTermType rty = some smtTy)
    (htc : Term.typeCheck ufs bvs tm = some smtTy)
    (h_typing : LExpr.HasTypeA Δ (.app () (.op () o (some (.tcons "arrow" [aty, rty]))) arg) rty)
    : cast (tyDenote_eq_smtTyDenote hbase_rty hτ)
        (simpDenote opInterp fvarVal bvarVal _ rty h_typing)
      = SMTTerm.denote ufInterp smtEnv tm smtTy htc := by
  simp only [toSMTTerm] at h_ok
  revert h_ok htc
  generalize hcop : CoreOp.ofString o.name = cop at hop_ty ⊢
  intro h_ok htc
  cases hop_ty with
  | intNeg =>
    simp [corePredefinedOpToSMTOp] at h_ok
    revert h_ok
    cases h_arg_ok : toSMTTerm ufs bvs arg with
    | error _ => simp [bind, Except.bind]
    | ok t_arg =>
      simp [bind, Except.bind]
      intro h_tm; subst h_tm
      have hchoose_arg : (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg_ty)).choose = .int :=
        choose_eq_of_hτ (HasSimpType_result_isBase h_arg_ty) rfl
      specialize ih_arg hbwf bvarVal smtEnv hbenv t_arg h_arg_ok
      simp only at ih_arg
      have hop_neg := hop.neg o.name hcop
      simp only [simpDenote]
      have h_app := HasTypeA.app_inv h_typing
      rw [Lambda.denote_app bvarVal h_app.2.1 h_app.2.2 h_typing]
      rw [Lambda.denote_op simpTcInterp opInterp fvarVal simpTyVarVal bvarVal h_app.2.1]
      obtain ⟨aty', h_fn_ty, h_arg_ty'⟩ := h_app
      simp only at *
      have h_opi := HasTypeA.op_inv h_fn_ty
      simp only [LMonoTy.arrow] at h_opi
      have h_aty : aty' = .tcons "int" [] := (LMonoTy.tcons.inj h_opi).2 |> List.cons.inj |>.1
      subst h_aty
      have h_opi_rfl : HasTypeA.op_inv h_fn_ty = rfl := rfl
      rw [h_opi_rfl]
      simp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map] at hop_neg ⊢
      rw [hop_neg]
      have h_intUn := tc_intUn_inv htc
      have h_smtTy_eq : smtTy = .int := h_intUn.2
      subst h_smtTy_eq
      apply eq_of_heq
      refine HEq.trans (cast_heq _ _) ?_
      have h_rhs_eq : SMTTerm.denote ufInterp smtEnv (.app Op.neg [t_arg] .int) .int htc =
          cast (by rw [(tc_intUn_inv htc).2])
            (-(SMTTerm.denote ufInterp smtEnv t_arg .int (tc_intUn_inv htc).1)) := by
        simp only [SMTTerm.denote]
        obtain ⟨ht, heq⟩ := tc_intUn_inv htc
        rfl
      have h_rhs_heq : HEq (SMTTerm.denote ufInterp smtEnv (.app Op.neg [t_arg] .int) .int htc)
          (-(SMTTerm.denote ufInterp smtEnv t_arg .int (tc_intUn_inv htc).1)) := by
        rw [h_rhs_eq]; exact cast_heq _ _
      refine HEq.trans ?_ h_rhs_heq.symm
      simp only [simpDenote] at ih_arg
      have h_arg_heq : HEq (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal arg
          (.tcons "int" []) h_arg_ty') (SMTTerm.denote ufInterp smtEnv t_arg .int (tc_intUn_inv htc).1) :=
        (cast_heq _ _).symm.trans (ih_convert_smtTy hchoose_arg ih_arg)
      exact congrArg (fun x : Int => -x) (eq_of_heq h_arg_heq) |> heq_of_eq
  | boolNot =>
    simp [corePredefinedOpToSMTOp] at h_ok
    revert h_ok
    cases h_arg_ok : toSMTTerm ufs bvs arg with
    | error _ => simp [bind, Except.bind]
    | ok t_arg =>
      simp [bind, Except.bind]
      intro h_tm; subst h_tm
      have hchoose_arg : (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg_ty)).choose = .bool :=
        choose_eq_of_hτ (HasSimpType_result_isBase h_arg_ty) rfl
      specialize ih_arg hbwf bvarVal smtEnv hbenv t_arg h_arg_ok
      simp only at ih_arg
      have hop_not := hop.not o.name hcop
      simp only [simpDenote]
      have h_app := HasTypeA.app_inv h_typing
      rw [Lambda.denote_app bvarVal h_app.2.1 h_app.2.2 h_typing]
      rw [Lambda.denote_op simpTcInterp opInterp fvarVal simpTyVarVal bvarVal h_app.2.1]
      obtain ⟨aty', h_fn_ty, h_arg_ty'⟩ := h_app
      simp only at *
      have h_opi := HasTypeA.op_inv h_fn_ty
      simp only [LMonoTy.arrow] at h_opi
      have h_aty : aty' = .tcons "bool" [] := (LMonoTy.tcons.inj h_opi).2 |> List.cons.inj |>.1
      subst h_aty
      have h_opi_rfl : HasTypeA.op_inv h_fn_ty = rfl := rfl
      rw [h_opi_rfl]
      simp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map] at hop_not ⊢
      rw [hop_not]
      have h_not_inv := tc_not_inv htc
      have h_smtTy_eq : smtTy = .bool := h_not_inv.2
      subst h_smtTy_eq
      have h_rhs_eq : SMTTerm.denote ufInterp smtEnv (.app (.core .not) [t_arg] .bool) .bool htc =
          cast (by rw [(tc_not_inv htc).2])
            (!(SMTTerm.denote ufInterp smtEnv t_arg .bool (tc_not_inv htc).1)) := by
        simp only [SMTTerm.denote]
        obtain ⟨ht, heq⟩ := tc_not_inv htc
        rfl
      have h_rhs_heq : HEq (SMTTerm.denote ufInterp smtEnv (.app (.core .not) [t_arg] .bool) .bool htc)
          (!(SMTTerm.denote ufInterp smtEnv t_arg .bool (tc_not_inv htc).1)) := by
        rw [h_rhs_eq]; exact cast_heq _ _
      apply eq_of_heq
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans ?_ h_rhs_heq.symm
      simp only [simpDenote] at ih_arg
      have h_arg_heq : HEq (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal arg
          (.tcons "bool" []) h_arg_ty') (SMTTerm.denote ufInterp smtEnv t_arg .bool (tc_not_inv htc).1) :=
        (cast_heq _ _).symm.trans (ih_convert_smtTy hchoose_arg ih_arg)
      exact congrArg (fun x : Bool => !x) (eq_of_heq h_arg_heq) |> heq_of_eq

/-- Helper for the app2 case of toSMTTerm_sound. -/
private theorem toSMTTerm_sound_app2
    {Φ : FVarCtx} {ufs : UFCtx} {Δ : List LMonoTy} {bvs : BoundVars}
    (huwf : UFCtxWF Φ ufs) (hbwf : BVarCtxWF Δ bvs ufs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (hop : OpInterpConsistent opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (ufInterp : UFInterp ufs) (smtEnv : SMTVarEnv bvs)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    {o : CoreLParams.Identifier} {arg1 arg2 : Expression.Expr} {aty1 aty2 rty : LMonoTy}
    (hop_ty : LExpr.OpIsSimp2 (CoreOp.ofString o.name) aty1 aty2 rty)
    (h_arg1_ty : LExpr.HasSimpType Φ Δ arg1 aty1)
    (h_arg2_ty : LExpr.HasSimpType Φ Δ arg2 aty2)
    (ih_arg1 : ∀ {bvs : BoundVars} (hbwf : BVarCtxWF Δ bvs ufs)
      (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
      (smtEnv : SMTVarEnv bvs),
      BVarEnvCorresponds hbwf bvarVal smtEnv →
      ∀ (tm : Term) (h_ok : toSMTTerm ufs bvs arg1 = .ok tm),
        let smtTy := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg1_ty)).choose
        let hτ := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg1_ty)).choose_spec
        let htc := toSMTTerm_typeChecks huwf hbwf arg1 aty1 smtTy h_arg1_ty tm h_ok hτ
        cast (tyDenote_eq_smtTyDenote (HasSimpType_result_isBase h_arg1_ty) hτ)
          (simpDenote opInterp fvarVal bvarVal arg1 aty1 (HasSimpType_implies_HasTypeA h_arg1_ty))
        = SMTTerm.denote ufInterp smtEnv tm smtTy htc)
    (ih_arg2 : ∀ {bvs : BoundVars} (hbwf : BVarCtxWF Δ bvs ufs)
      (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
      (smtEnv : SMTVarEnv bvs),
      BVarEnvCorresponds hbwf bvarVal smtEnv →
      ∀ (tm : Term) (h_ok : toSMTTerm ufs bvs arg2 = .ok tm),
        let smtTy := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg2_ty)).choose
        let hτ := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg2_ty)).choose_spec
        let htc := toSMTTerm_typeChecks huwf hbwf arg2 aty2 smtTy h_arg2_ty tm h_ok hτ
        cast (tyDenote_eq_smtTyDenote (HasSimpType_result_isBase h_arg2_ty) hτ)
          (simpDenote opInterp fvarVal bvarVal arg2 aty2 (HasSimpType_implies_HasTypeA h_arg2_ty))
        = SMTTerm.denote ufInterp smtEnv tm smtTy htc)
    (tm : Term)
    (h_ok : toSMTTerm ufs bvs (.app () (.app () (.op () o (some (.tcons "arrow" [aty1, .tcons "arrow" [aty2, rty]]))) arg1) arg2) = .ok tm)
    (hbase_rty : LExpr.MonoTyIsBase rty)
    (smtTy : TermType)
    (hτ : monoTyToTermType rty = some smtTy)
    (htc : Term.typeCheck ufs bvs tm = some smtTy)
    (h_typing : LExpr.HasTypeA Δ (.app () (.app () (.op () o (some (.tcons "arrow" [aty1, .tcons "arrow" [aty2, rty]]))) arg1) arg2) rty)
    : cast (tyDenote_eq_smtTyDenote hbase_rty hτ)
        (simpDenote opInterp fvarVal bvarVal _ rty h_typing)
      = SMTTerm.denote ufInterp smtEnv tm smtTy htc := by
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
    cases h1_ok : toSMTTerm ufs bvs arg1 with
    | error _ => simp [bind, Except.bind]
    | ok t1 =>
      cases h2_ok : toSMTTerm ufs bvs arg2 with
      | error _ => simp [bind, Except.bind]
      | ok t2 =>
        simp [bind, Except.bind]
        intro h_tm; subst h_tm
        specialize ih_arg1 hbwf bvarVal smtEnv hbenv t1 h1_ok
        specialize ih_arg2 hbwf bvarVal smtEnv hbenv t2 h2_ok
        simp only at ih_arg1 ih_arg2
        simp only [simpDenote]
        apply eq_of_heq
        refine HEq.trans (cast_heq _ _) ?_
        have h_app_outer := HasTypeA.app_inv h_typing
        rw [Lambda.denote_app bvarVal h_app_outer.2.1 h_app_outer.2.2 h_typing]
        have h_app_inner := HasTypeA.app_inv h_app_outer.2.1
        rw [Lambda.denote_app bvarVal h_app_inner.2.1 h_app_inner.2.2 h_app_outer.2.1]
        rw [Lambda.denote_op simpTcInterp opInterp fvarVal simpTyVarVal bvarVal h_app_inner.2.1]
        obtain ⟨aty1', h_op_ty, h_arg1_ty'⟩ := h_app_inner
        obtain ⟨aty2', h_inner_fn_ty, h_arg2_ty'⟩ := h_app_outer
        simp only at *
        have h_opi := HasTypeA.op_inv h_op_ty
        simp only [LMonoTy.arrow] at h_opi
        have h_inj := LMonoTy.tcons.inj h_opi
        have h_args := h_inj.2
        have h_aty1_eq : aty1' = _ := (List.cons.inj h_args).1
        subst h_aty1_eq
        have h_tail := (List.cons.inj h_args).2
        have h_aty2_tcons := (List.cons.inj h_tail).1
        have h_aty2_inj := LMonoTy.tcons.inj h_aty2_tcons
        have h_aty2_eq : aty2' = _ := (List.cons.inj h_aty2_inj.2).1
        subst h_aty2_eq
        have h_opi_rfl : HasTypeA.op_inv h_op_ty = rfl := rfl
        rw [h_opi_rfl]
        simp only [simpDenote] at ih_arg1 ih_arg2
        simp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map]
        have h1_heq := (cast_heq _ _).symm.trans
          (ih_convert_smtTy (choose_eq_of_hτ (HasSimpType_result_isBase h_arg1_ty) rfl) ih_arg1)
        have h2_heq := (cast_heq _ _).symm.trans
          (ih_convert_smtTy (choose_eq_of_hτ (HasSimpType_result_isBase h_arg2_ty) rfl) ih_arg2)
        first
        | (-- intAdd
           have hsmtTy : smtTy = .int := (tc_intBin_inv htc (.inl rfl)).2.2
           subst hsmtTy; rw [hop.add o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.add [t1, t2] .int) .int htc =
               SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inl rfl)).1 +
               SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inl rfl)).2.1 := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intSub
           have hsmtTy : smtTy = .int := (tc_intBin_inv htc (.inr (.inl rfl))).2.2
           subst hsmtTy; rw [hop.sub o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.sub [t1, t2] .int) .int htc =
               SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inl rfl))).1 -
               SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inl rfl))).2.1 := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intMul
           have hsmtTy : smtTy = .int := (tc_intBin_inv htc (.inr (.inr (.inl rfl)))).2.2
           subst hsmtTy; rw [hop.mul o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.mul [t1, t2] .int) .int htc =
               SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inl rfl)))).1 *
               SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1 := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intDiv / intSafeDiv
           have hsmtTy : smtTy = .int := (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2
           subst hsmtTy; first | rw [hop.div o.name hcop] | rw [hop.safeDiv o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.div [t1, t2] .int) .int htc =
               SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1 /
               SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1 := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intMod / intSafeMod
           have hsmtTy : smtTy = .int := (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2
           subst hsmtTy; first | rw [hop.mod_ o.name hcop] | rw [hop.safeMod o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.mod [t1, t2] .int) .int htc =
               SMTTerm.denote ufInterp smtEnv t1 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1 %
               SMTTerm.denote ufInterp smtEnv t2 .int (tc_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1 := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intLe
           have hsmtTy : smtTy = .bool := (tc_intCmp_inv htc (.inl rfl)).2.2
           subst hsmtTy; rw [hop.le o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.le [t1, t2] .bool) .bool htc =
               decide (SMTTerm.denote ufInterp smtEnv t1 .int (tc_intCmp_inv htc (.inl rfl)).1 ≤
                       SMTTerm.denote ufInterp smtEnv t2 .int (tc_intCmp_inv htc (.inl rfl)).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intLt
           have hsmtTy : smtTy = .bool := (tc_intCmp_inv htc (.inr (.inl rfl))).2.2
           subst hsmtTy; rw [hop.lt o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.lt [t1, t2] .bool) .bool htc =
               decide (SMTTerm.denote ufInterp smtEnv t1 .int (tc_intCmp_inv htc (.inr (.inl rfl))).1 <
                       SMTTerm.denote ufInterp smtEnv t2 .int (tc_intCmp_inv htc (.inr (.inl rfl))).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intGe
           have hsmtTy : smtTy = .bool := (tc_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.2
           subst hsmtTy; rw [hop.ge o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.ge [t1, t2] .bool) .bool htc =
               decide (SMTTerm.denote ufInterp smtEnv t1 .int (tc_intCmp_inv htc (.inr (.inr (.inl rfl)))).1 ≥
                       SMTTerm.denote ufInterp smtEnv t2 .int (tc_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- intGt
           have hsmtTy : smtTy = .bool := (tc_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.2
           subst hsmtTy; rw [hop.gt o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.gt [t1, t2] .bool) .bool htc =
               decide (SMTTerm.denote ufInterp smtEnv t1 .int (tc_intCmp_inv htc (.inr (.inr (.inr rfl)))).1 >
                       SMTTerm.denote ufInterp smtEnv t2 .int (tc_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- boolAnd
           have hsmtTy : smtTy = .bool := (tc_boolBin_inv htc (.inl rfl)).2.2
           subst hsmtTy; rw [hop.and_ o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.and [t1, t2] .bool) .bool htc =
               (SMTTerm.denote ufInterp smtEnv t1 .bool (tc_boolBin_inv htc (.inl rfl)).1 &&
                SMTTerm.denote ufInterp smtEnv t2 .bool (tc_boolBin_inv htc (.inl rfl)).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- boolOr
           have hsmtTy : smtTy = .bool := (tc_boolBin_inv htc (.inr (.inl rfl))).2.2
           subst hsmtTy; rw [hop.or_ o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.or [t1, t2] .bool) .bool htc =
               (SMTTerm.denote ufInterp smtEnv t1 .bool (tc_boolBin_inv htc (.inr (.inl rfl))).1 ||
                SMTTerm.denote ufInterp smtEnv t2 .bool (tc_boolBin_inv htc (.inr (.inl rfl))).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- boolImplies
           have hsmtTy : smtTy = .bool := (tc_boolBin_inv htc (.inr (.inr rfl))).2.2
           subst hsmtTy; rw [hop.implies o.name hcop]
           have hrhs : SMTTerm.denote ufInterp smtEnv (.app Op.implies [t1, t2] .bool) .bool htc =
               (!SMTTerm.denote ufInterp smtEnv t1 .bool (tc_boolBin_inv htc (.inr (.inr rfl))).1 ||
                SMTTerm.denote ufInterp smtEnv t2 .bool (tc_boolBin_inv htc (.inr (.inr rfl))).2.1) := by
             simp only [SMTTerm.denote]; split; rfl
           rw [hrhs]; exact heq_of_eq (by congr 1 <;> exact eq_of_heq ‹_›))
        | (-- boolEquiv (maps to Op.eq / core eq)
           have hsmtTy : smtTy = .bool := (tc_eq_inv htc).2.2.2
           subst hsmtTy; rw [hop.equiv o.name hcop]
           rw [SMTTerm_denote_eq_unfold]
           apply heq_of_eq; simp only [cast_eq]
           have hτ' : (tc_eq_inv htc).1 = .bool := by
             have h1tc := (tc_eq_inv htc).2.1
             have := toSMTTerm_typeChecks huwf hbwf arg1 _ _ h_arg1_ty t1 h1_ok
                       (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase h_arg1_ty)).choose_spec
             simp only [choose_eq_of_hτ (HasSimpType_result_isBase h_arg1_ty) rfl] at this
             exact Option.some.inj (h1tc.symm.trans this)
           have h1_eq := eq_of_heq h1_heq
           have h2_eq := eq_of_heq h2_heq
           simp only [h1_eq, h2_eq]
           have hd1 := SMTTerm_denote_cast ufInterp smtEnv t1 .bool (tc_eq_inv htc).1
             (by exact (tc_eq_inv htc).2.1 ▸ (by simp [hτ']))
             (tc_eq_inv htc).2.1 hτ'.symm
           have hd2 := SMTTerm_denote_cast ufInterp smtEnv t2 .bool (tc_eq_inv htc).1
             (by exact (tc_eq_inv htc).2.2.1 ▸ (by simp [hτ']))
             (tc_eq_inv htc).2.2.1 hτ'.symm
           congr 1; apply propext; constructor
           · intro heq'; exact eq_of_heq (hd1.symm.trans (heq' ▸ hd2))
           · intro heq'; exact eq_of_heq (hd1.trans (heq' ▸ hd2.symm)))

/-- Helper for the quant case of toSMTTerm_sound. -/
private theorem toSMTTerm_sound_quant
    {Φ : FVarCtx} {ufs : UFCtx} {Δ : List LMonoTy} {bvs : BoundVars}
    (huwf : UFCtxWF Φ ufs) (hbwf : BVarCtxWF Δ bvs ufs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (ufInterp : UFInterp ufs) (smtEnv : SMTVarEnv bvs)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    (qty : LMonoTy) (k : Lambda.QuantifierKind) (name : String)
    (body : Expression.Expr)
    (hbase : LExpr.MonoTyIsBase qty)
    (he_body : LExpr.HasSimpType Φ (qty :: Δ) body (.tcons "bool" []))
    (smtQTy : TermType) (hqty : monoTyToTermType qty = some smtQTy)
    (bodyTm : Term)
    (v : TermVar) (hv : v = ⟨s!"$__bv{bvs.length}", smtQTy⟩)
    (hbwf' : BVarCtxWF (qty :: Δ) (v :: bvs) ufs)
    (hbody_tc : Term.typeCheck ufs (v :: bvs) bodyTm = some .bool)
    (body_eq : ∀ x : Lambda.TyDenote simpTcInterp simpTyVarVal qty,
        ∀ (smtEnv' : SMTVarEnv (v :: bvs)),
        BVarEnvCorresponds hbwf' (.cons x bvarVal) smtEnv' →
        (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal
          (.cons x bvarVal) body (.tcons "bool" [])
          (HasSimpType_implies_HasTypeA he_body) : Bool) =
        SMTTerm.denote ufInterp smtEnv' bodyTm .bool hbody_tc)
    (h_ok : toSMTTerm ufs bvs (.quant () k name (some qty) (.const () (.boolConst true)) body) =
      .ok (.quant (match k with | .all => .all | .exist => .exist)
        [v] [] bodyTm))
    : let he := LExpr.HasSimpType.quant hbase he_body
      let smtTy := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase he)).choose
      let hτ := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase he)).choose_spec
      let htc := toSMTTerm_typeChecks huwf hbwf _ _ smtTy he _ h_ok hτ
      cast (tyDenote_eq_smtTyDenote (HasSimpType_result_isBase he) hτ)
        (simpDenote opInterp fvarVal bvarVal
          (.quant () k name (some qty) (.const () (.boolConst true)) body)
          (.tcons "bool" []) (HasSimpType_implies_HasTypeA he))
      = SMTTerm.denote ufInterp smtEnv
          (.quant (match k with | .all => .all | .exist => .exist)
            [v] [] bodyTm) smtTy htc := by
  subst hv
  cases k <;> {
    intro he smtTy hτ htc
    simp only [simpDenote]
    apply eq_of_heq
    apply HEq.trans (cast_heq _ _)
    unfold LExpr.denote SMTTerm.denote
    dsimp only []
    obtain ⟨_, _, _, h_body_inv⟩ := HasTypeA.quant_inv (HasSimpType_implies_HasTypeA he)
    obtain ⟨hbody_inv, heq_inv⟩ := tc_quant_inv htc
    dsimp only []
    apply HEq.trans _ (cast_heq _ _).symm
    apply heq_of_eq
    congr 1
    apply propext
    let v : TermVar := ⟨s!"$__bv{bvs.length}", smtQTy⟩
    have h_pi1 : h_body_inv = HasSimpType_implies_HasTypeA he_body := proof_irrel _ _
    have h_pi2 : hbody_inv = hbody_tc := proof_irrel _ _
    rw [h_pi1, h_pi2]
    let v : TermVar := ⟨s!"$__bv{bvs.length}", smtQTy⟩
    have nat_toString_inj : ∀ a b : Nat, toString a = toString b → a = b := by
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
    have bv_str_inj : ∀ a b : Nat, s!"$__bv{a}" = s!"$__bv{b}" → a = b := by
      intro a b h
      have h1 : ("$__bv" ++ toString a).toList = ("$__bv" ++ toString b).toList :=
        congrArg String.toList h
      rw [String.toList_append, String.toList_append] at h1
      exact nat_toString_inj a b (String.ext_iff.mpr (List.append_cancel_left h1))
    have hv_notin : v ∉ bvs := by
      intro hmem
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
      have hid := hbwf.id_scheme i hi
      have hveq : (bvs[i]'hi).id = v.id := congrArg TermVar.id hget
      rw [hid] at hveq
      have := bv_str_inj _ _ hveq
      omega
    have h_ty_eq := tyDenote_eq_smtTyDenote hbase hqty
    have bridge : ∀ (x : Lambda.TyDenote simpTcInterp simpTyVarVal qty)
        (ext : SMTVarEnv [v])
        (hxy : ext v (List.Mem.head _) = cast h_ty_eq x),
        (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal
          (.cons x bvarVal) body (.tcons "bool" [])
          (HasSimpType_implies_HasTypeA he_body) : Bool) = true ↔
        SMTTerm.denote ufInterp (fun w hmem => if hv : w ∈ [v] then ext w hv
          else smtEnv w (by cases hmem; exact absurd (List.Mem.head _) hv; assumption))
          bodyTm .bool hbody_tc = true := by
      intro x ext hxy
      let smtEnv' : SMTVarEnv (v :: bvs) := fun w hmem =>
        if hv : w ∈ [v] then ext w hv
        else smtEnv w (by cases hmem; exact absurd (List.Mem.head _) hv; assumption)
      have hcorr : BVarEnvCorresponds hbwf' (.cons x bvarVal) smtEnv' :=
        BVarEnvCorresponds_cons hbenv hbase hqty x
          (show smtEnv' v (List.Mem.head _) = cast h_ty_eq x by
            simp only [smtEnv', show (v ∈ [v]) = True from by simp, dite_true]
            exact hxy)
          (show ∀ w (hmem : w ∈ bvs), smtEnv' w (List.Mem.tail _ hmem) = smtEnv w hmem by
            intro w hmem; simp only [smtEnv']
            have : ¬(w ∈ [v]) := by
              simp []
              intro heq; exact absurd (heq ▸ hmem) hv_notin
            simp [this])
          hbwf'
      have hbody := body_eq x smtEnv' hcorr
      constructor
      · intro hlhs
        change SMTTerm.denote ufInterp smtEnv' bodyTm .bool hbody_tc = true
        rw [← hbody]; exact hlhs
      · intro hrhs
        rw [hbody]; exact hrhs
    constructor
    · first
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
    · first
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

/-- Semantic soundness of toSMTTerm. -/
theorem toSMTTerm_sound
    {Φ : FVarCtx} {ufs : UFCtx} {Δ : List LMonoTy} {bvs : BoundVars}
    (huwf : UFCtxWF Φ ufs) (hbwf : BVarCtxWF Δ bvs ufs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (hop : OpInterpConsistent opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (ufInterp : UFInterp ufs) (smtEnv : SMTVarEnv bvs)
    (hfenv : UFEnvCorresponds huwf fvarVal ufInterp)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    (e : Expression.Expr) (τ : LMonoTy)
    (he : LExpr.HasSimpType Φ Δ e τ)
    (tm : Term) (h_ok : toSMTTerm ufs bvs e = .ok tm)
    : let smtTy := (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase he)).choose
      let hτ : monoTyToTermType τ = some smtTy :=
        (MonoTyIsBase_monoTyToTermType (HasSimpType_result_isBase he)).choose_spec
      let htc : Term.typeCheck ufs bvs tm = some smtTy :=
        toSMTTerm_typeChecks huwf hbwf e τ smtTy he tm h_ok hτ
      cast (tyDenote_eq_smtTyDenote (HasSimpType_result_isBase he) hτ)
        (simpDenote opInterp fvarVal bvarVal e τ (HasSimpType_implies_HasTypeA he))
      = SMTTerm.denote ufInterp smtEnv tm smtTy htc := by
  induction he generalizing bvs tm with
  | @const Δ' c hbase =>
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
      simp only [simpDenote, LExpr.denote]
      have hcorr := hbenv i τ' hbase hlook
      apply eq_of_heq
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans ?_ (SMTTerm_denote_var_heq _ _ _ _ _).symm
      exact (cast_heq _ _).symm.trans (heq_of_eq hcorr)
    · next hni =>
      exfalso; revert h_ok; simp (config := { decide := true })
  | fvar hmemΦ hbase =>
    simp only [toSMTTerm] at h_ok
    obtain ⟨smtTy_fv, hty_fv⟩ := MonoTyIsBase_monoTyToTermType hbase
    rw [hty_fv] at h_ok; simp only at h_ok
    have huf_mem := UFCtxWF_mem huwf hmemΦ hty_fv
    simp only [huf_mem, ite_true, Except.ok.injEq] at h_ok
    subst h_ok
    intro smtTy hτ htc
    obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hmemΦ
    have hufs_idx : idx < ufs.length := huwf.len_eq ▸ hidx
    have hgf : (Φ[idx]).1 = _ := congrArg Prod.fst hget
    have hgs : (Φ[idx]).2 = _ := congrArg Prod.snd hget
    simp only at hgf hgs
    -- UFEnvCorresponds gives us the connection
    have hfenv_idx := hfenv idx hidx
    -- Field equalities for ufs[idx]
    have hufs_out : (ufs[idx]'hufs_idx).out = smtTy_fv := by
      have htyeq := huwf.ty_eq idx hidx
      rw [hgs, hty_fv] at htyeq; simp at htyeq; exact htyeq.symm
    -- The proof strategy: use cast_eq_iff_heq style reasoning
    -- Both sides are casts of underlying values; show they're heq
    apply eq_of_heq
    -- LHS: cast (tyDenote_eq ...) (simpDenote ...) ≍ simpDenote ...
    refine (cast_heq _ _).trans ?_
    -- RHS: SMTTerm.denote ... ≍ ufInterp ⟨f.name,[],smtTy_fv⟩ hmem
    refine HEq.trans ?_ (SMTTerm_denote_uf_heq ufInterp smtEnv _ _ _ htc).symm
    -- After unfolding simpDenote at fvar:
    simp only [simpDenote, LExpr.denote]
    -- Goal: fvarVal f (τ.substTyVars simpTyVarVal) ≍ ufInterp ⟨f.name,[],smtTy_fv⟩ (tc_uf_inv htc).1
    -- From hfenv_idx: cast ... (fvarVal ⟨Φ[idx].1,()⟩ (Φ[idx].2.substTyVars ...)) = ufInterp ufs[idx] hmem
    -- Rewrite Φ[idx].1 → f.name and Φ[idx].2 → τ using hgf/hgs (dependent rewrite!)
    -- We can't rewrite inside the cast directly. Instead use HEq.
    -- From hfenv_idx (strip cast):
    --   fvarVal ⟨Φ[idx].1,()⟩ (Φ[idx].2.substTyVars ...) ≍ ufInterp (ufs[idx]) hmem
    have h_to_uf := (cast_heq _ _).symm.trans (heq_of_eq hfenv_idx)
    -- Use hget to rewrite Φ[idx] in h_to_uf
    rw [hget] at h_to_uf
    -- h_to_uf : fvarVal ⟨f.name,()⟩ (τ.substTyVars ...) ≍ ufInterp (ufs[idx]) hmem
    -- Build full UF equality
    have hufs_id : (ufs[idx]'hufs_idx).id = (Φ[idx]).1 := (huwf.id_eq idx hidx).symm
    have hufs_args : (ufs[idx]'hufs_idx).args = [] := huwf.nullary idx hufs_idx
    rw [hgf] at hufs_id
    -- h_to_uf : fvarVal ... ≍ ufInterp ufs[idx] (List.getElem_mem hufs_idx)
    -- Goal: fvarVal ... ≍ ufInterp ⟨f.name,[],smtTy_fv⟩ (tc_uf_inv htc).1
    -- Transport via ufInterp_heq helper
    exact h_to_uf.trans (ufInterp_heq ufInterp hufs_id hufs_args hufs_out _ _)
  | app1 hop_ty h_arg_ty ih_arg =>
    have he' := LExpr.HasSimpType.app1 hop_ty h_arg_ty
    have hbase' := HasSimpType_result_isBase he'
    have hτ' := (MonoTyIsBase_monoTyToTermType hbase').choose_spec
    have htc' := toSMTTerm_typeChecks huwf hbwf _ _ _ he' tm h_ok hτ'
    exact toSMTTerm_sound_app1 huwf hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv hbenv
      hop_ty h_arg_ty ih_arg tm h_ok hbase' _ hτ' htc' (HasSimpType_implies_HasTypeA he')
  | app2 hop_ty h_arg1_ty h_arg2_ty ih_arg1 ih_arg2 =>
    have he' := LExpr.HasSimpType.app2 hop_ty h_arg1_ty h_arg2_ty
    have hbase' := HasSimpType_result_isBase he'
    have hτ' := (MonoTyIsBase_monoTyToTermType hbase').choose_spec
    have htc' := toSMTTerm_typeChecks huwf hbwf _ _ _ he' tm h_ok hτ'
    exact toSMTTerm_sound_app2 huwf hbwf opInterp hop fvarVal bvarVal ufInterp smtEnv hbenv
      hop_ty h_arg1_ty h_arg2_ty ih_arg1 ih_arg2 tm h_ok hbase' _ hτ' htc'
      (HasSimpType_implies_HasTypeA he')
  | @ite _ _ _ τ' _ hc_ty ht_ty he_ty ihc iht ihe =>
    rename_i Δ' c_expr t_expr e_expr
    have h_ok' := h_ok
    simp only [toSMTTerm, bind, Except.bind] at h_ok'
    revert h_ok h_ok'
    cases hc_ok : toSMTTerm ufs bvs c_expr with
    | error _ => simp [toSMTTerm, bind, Except.bind]
    | ok ct =>
      cases ht_ok : toSMTTerm ufs bvs t_expr with
      | error _ => simp [toSMTTerm, bind, Except.bind]
      | ok tt_tm =>
        cases he_ok : toSMTTerm ufs bvs e_expr with
        | error _ => simp [toSMTTerm, bind, Except.bind]
        | ok et =>
          intro h_ok h_ok'
          have htm : tm = Term.app (.core .ite) [ct, tt_tm, et] (Term.typeOf tt_tm) := by
            simp [toSMTTerm, bind, Except.bind, hc_ok, ht_ok, he_ok] at h_ok
            exact h_ok.symm
          subst htm
          intro smtTy hτ htc
          specialize ihc hbwf bvarVal smtEnv hbenv ct hc_ok
          specialize iht hbwf bvarVal smtEnv hbenv tt_tm ht_ok
          specialize ihe hbwf bvarVal smtEnv hbenv et he_ok
          simp only at ihc iht ihe
          have h_ite_unfold := Lambda.denote_ite (T := CoreLParams) (tcInterp := simpTcInterp)
            (opInterp := opInterp) (fvarVal := fvarVal) (vt := simpTyVarVal)
            bvarVal
            (HasSimpType_implies_HasTypeA hc_ty)
            (HasSimpType_implies_HasTypeA ht_ty)
            (HasSimpType_implies_HasTypeA he_ty)
            (HasSimpType_implies_HasTypeA (LExpr.HasSimpType.ite hc_ty ht_ty he_ty))
          simp only [simpDenote] at ihc iht ihe ⊢
          rw [h_ite_unfold]
          rw [SMTTerm_denote_ite]
          apply bif_heq_of_cond_branches
          · have hc_eq := choose_eq_of_hτ (HasSimpType_result_isBase hc_ty)
              (show monoTyToTermType (.tcons "bool" []) = some TermType.bool from rfl)
            exact eq_of_heq ((cast_heq _ _).symm.trans (ih_convert_smtTy hc_eq ihc))
          · have ht_eq := choose_eq_of_hτ (HasSimpType_result_isBase ht_ty) hτ
            exact (cast_heq _ _).symm.trans (ih_convert_smtTy ht_eq iht)
          · have he_eq := choose_eq_of_hτ (HasSimpType_result_isBase he_ty) hτ
            exact (cast_heq _ _).symm.trans (ih_convert_smtTy he_eq ihe)
  | eq hbase he1_ty he2_ty ih1 ih2 =>
    rename_i τ_eq Δ' e1_expr e2_expr
    have h_ok' := h_ok
    simp only [toSMTTerm, bind, Except.bind] at h_ok'
    revert h_ok h_ok'
    cases h1_ok : toSMTTerm ufs bvs e1_expr with
    | error _ => simp [toSMTTerm, bind, Except.bind]
    | ok t1 =>
      cases h2_ok : toSMTTerm ufs bvs e2_expr with
      | error _ => simp [toSMTTerm, bind, Except.bind]
      | ok t2 =>
        intro h_ok h_ok'
        have htm : tm = Term.app (.core .eq) [t1, t2] .bool := by
          simp [toSMTTerm, bind, Except.bind, h1_ok, h2_ok] at h_ok
          exact h_ok.symm
        subst htm
        intro smtTy hτ htc
        specialize ih1 hbwf bvarVal smtEnv hbenv t1 h1_ok
        specialize ih2 hbwf bvarVal smtEnv hbenv t2 h2_ok
        simp only at ih1 ih2
        simp only [simpDenote] at ih1 ih2 ⊢
        rw [SMTTerm_denote_eq_unfold]
        obtain ⟨τ'_smt, htc1_inv, htc2_inv, heq_bool⟩ := tc_eq_inv htc
        have hτ_sub_spec := (MonoTyIsBase_monoTyToTermType hbase).choose_spec
        have htc1_ih := toSMTTerm_typeChecks huwf hbwf e1_expr τ_eq _ he1_ty t1 h1_ok hτ_sub_spec
        have htc2_ih := toSMTTerm_typeChecks huwf hbwf e2_expr τ_eq _ he2_ty t2 h2_ok hτ_sub_spec
        have hτ'_eq : τ'_smt = (MonoTyIsBase_monoTyToTermType hbase).choose :=
          Option.some.inj (htc1_inv.symm.trans htc1_ih)
        subst hτ'_eq
        by_cases heq_vals : LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
            e1_expr τ_eq (HasSimpType_implies_HasTypeA he1_ty) =
          LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
            e2_expr τ_eq (HasSimpType_implies_HasTypeA he2_ty)
        · have h_lhs : LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
              (.eq () e1_expr e2_expr) (.tcons "bool" [])
              (HasSimpType_implies_HasTypeA (LExpr.HasSimpType.eq hbase he1_ty he2_ty)) = true :=
            Lambda.denote_eq_true bvarVal
              (HasSimpType_implies_HasTypeA he1_ty)
              (HasSimpType_implies_HasTypeA he2_ty)
              (HasSimpType_implies_HasTypeA (LExpr.HasSimpType.eq hbase he1_ty he2_ty))
              heq_vals
          rw [h_lhs]
          have hw_eq : SMTTerm.denote ufInterp smtEnv t1 _ htc1_inv =
              SMTTerm.denote ufInterp smtEnv t2 _ htc2_inv := by
            exact ih1.symm.trans (congrArg _ heq_vals |>.trans ih2)
          simp only [hw_eq, decide_true]; rfl
        · have h_lhs : LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
              (.eq () e1_expr e2_expr) (.tcons "bool" [])
              (HasSimpType_implies_HasTypeA (LExpr.HasSimpType.eq hbase he1_ty he2_ty)) = false :=
            Lambda.denote_eq_false bvarVal
              (HasSimpType_implies_HasTypeA he1_ty)
              (HasSimpType_implies_HasTypeA he2_ty)
              (HasSimpType_implies_HasTypeA (LExpr.HasSimpType.eq hbase he1_ty he2_ty))
              heq_vals
          rw [h_lhs]
          have hw_neq : SMTTerm.denote ufInterp smtEnv t1 _ htc1_inv ≠
              SMTTerm.denote ufInterp smtEnv t2 _ htc2_inv := by
            intro hw
            apply heq_vals
            have hcast : cast (tyDenote_eq_smtTyDenote hbase hτ_sub_spec)
                (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
                  e1_expr τ_eq (HasSimpType_implies_HasTypeA he1_ty)) =
              cast (tyDenote_eq_smtTyDenote hbase hτ_sub_spec)
                (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
                  e2_expr τ_eq (HasSimpType_implies_HasTypeA he2_ty)) :=
              ih1.trans (hw.trans ih2.symm)
            have hinj : ∀ {α β : Type} (h : α = β) (a b : α), cast h a = cast h b → a = b :=
              fun h _ _ heq => by cases h; exact heq
            exact hinj _ _ _ hcast
          simp only [hw_neq, decide_false]; rfl
  | quant hbase he_body ih_body =>
    obtain ⟨smtQTy, hqty⟩ := MonoTyIsBase_monoTyToTermType hbase
    simp only [toSMTTerm, hqty, bind, Except.bind] at h_ok
    revert h_ok
    cases hbody_ok : toSMTTerm ufs (⟨s!"$__bv{bvs.length}", smtQTy⟩ :: bvs) _ with
    | error _ => simp
    | ok bodyTm =>
      simp only [Except.ok.injEq]
      intro h_tm; subst h_tm
      let v : TermVar := ⟨s!"$__bv{bvs.length}", smtQTy⟩
      have hbwf' : BVarCtxWF (_ :: _) (v :: bvs) ufs :=
        ⟨congrArg (· + 1) hbwf.len_eq, fun i hi => by
          cases i with
          | zero => exact hqty
          | succ j =>
            simp only [List.length, Nat.succ_lt_succ_iff] at hi
            simp only [List.getElem_cons_succ]
            exact hbwf.ty_eq j hi,
         fun i hi => by
          cases i with
          | zero => simp [v, List.length]
          | succ j =>
            simp only [List.getElem_cons_succ, List.length] at hi ⊢
            have hj_lt : j < bvs.length := by omega
            have := hbwf.id_scheme j hj_lt
            rw [this]; simp; congr 1; omega,
         hbwf.no_shadow⟩
      have hbody_tc : Term.typeCheck ufs (v :: bvs) bodyTm = some .bool :=
        toSMTTerm_typeChecks huwf hbwf' _ (.tcons "bool" []) .bool he_body bodyTm hbody_ok rfl
      have body_eq : ∀ x : Lambda.TyDenote simpTcInterp simpTyVarVal _,
          ∀ (smtEnv' : SMTVarEnv (v :: bvs)),
          BVarEnvCorresponds hbwf' (.cons x bvarVal) smtEnv' →
          (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal
            (.cons x bvarVal) _ (.tcons "bool" [])
            (HasSimpType_implies_HasTypeA he_body) : Bool) =
          SMTTerm.denote ufInterp smtEnv' bodyTm .bool hbody_tc := by
        intro x smtEnv' henv'
        have ih := ih_body hbwf' (.cons x bvarVal) smtEnv' henv' bodyTm hbody_ok
        simp only [simpDenote] at ih
        have hchoose : (MonoTyIsBase_monoTyToTermType
            (HasSimpType_result_isBase he_body)).choose = .bool :=
          choose_eq_of_hτ (HasSimpType_result_isBase he_body) rfl
        have ih_eq : (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal
            (.cons x bvarVal) _ (.tcons "bool" [])
            (HasSimpType_implies_HasTypeA he_body) : Bool) =
            SMTTerm.denote ufInterp smtEnv' bodyTm .bool hbody_tc := by
          have h_eq_heq := ih_convert_smtTy hchoose ih
          exact eq_of_heq ((cast_heq _ _).symm.trans h_eq_heq)
        exact ih_eq
      cases ‹Lambda.QuantifierKind› with
      | all =>
        exact toSMTTerm_sound_quant huwf hbwf opInterp fvarVal bvarVal ufInterp smtEnv hbenv
          _ _ _ _ hbase he_body smtQTy hqty bodyTm _ rfl hbwf' hbody_tc body_eq h_ok
      | exist =>
        exact toSMTTerm_sound_quant huwf hbwf opInterp fvarVal bvarVal ufInterp smtEnv hbenv
          _ _ _ _ hbase he_body smtQTy hqty bodyTm _ rfl hbwf' hbody_tc body_eq h_ok
