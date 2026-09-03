/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public meta import Lean.Elab.Command
import all Strata.Languages.Core.PrototypeSMTGen.FunDef
import all Strata.Languages.Core.Factory
import all Strata.Languages.Core.CoreOp
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst
-- The `CoreOp.ofString` inverses (§4) reason through the slice-based `String` parser; these stdlib
-- `import all`s expose the non-`public` `startsWith_iff` / `drop` / `nextn` reduction lemmas they need.
import all Init.Data.String.Lemmas.Pattern.String.ForwardPattern
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.Basic

/-!
# `OpInterpConsistent` for the default `Core.Factory` builtins

Connector 1b support: this file proves that any `opInterp` consistent with `Core.Factory` (via
`Factory.InterpConsistent`) interprets each predefined operator as its concrete Lean function —
i.e. it constructs the `OpInterpConsistent` structure. Connector 1b
(`opInterpConsistent_of_factoryConsistent`) then obtains this for the reconstructed `c.F`, which
extends `Core.Factory` by `SeedWF`.

The bool operators (`And`, `Or`, `Implies`, `Equiv`, `Not`) and the non-guarded integer operators
(`Add`, `Sub`, `Mul`, `Neg`, `Lt`, `Le`, `Gt`, `Ge`) are interpreted via per-arity generic lemmas
(`binBoolInterp` / `unBoolInterp` / `binIntInterp` / `unIntInterp` / `binIntCmpInterp`), each fed
the factory-field facts and the operator's `concreteEval` behaviour on constant arguments.

The guarded division/modulo operators (`Div`, `Mod`) use the SMT-LIB-faithful div-by-zero model:
the `binaryOp … (· != 0)` guard makes `concreteEval` fold to `none` at divisor `0`, so consistency
constrains `opInterp` only at nonzero divisor and the at-zero value is model-chosen.
`OpInterpConsistent` carries explicit `divByZero`/`modByZero` functions (avoiding an unsound
`x / 0 = 0`) and its div/mod fields are conditional (`fun x y => if y = 0 then divByZero x else x / y`);
this connector chooses `divByZero := fun x => opInterp "Int.Div" _ x 0` (and mod), so the `y = 0`
branch is reflexivity and the `y ≠ 0` branch is the factory's guarded behaviour.

Key definitions: `LFunc.InterpConsistentEvalReduce`, the const projections `constBool?` /
`constInt?`, and the generic per-operator interpretation lemmas. Key results: `ofString_bool`,
`ofString_numeric_int`, `opInterpConsistent_of_coreFactory`.
-/

open Lambda Core

namespace Core.BuiltinConsistent

set_option maxHeartbeats 4000000

/-! ## §1. The kernel-reducible restatement of `InterpConsistentEval` -/

/-- Unconditional `subst = substCore`. Upstream's `LMonoTy.subst_eq_substCore` carries a
    `hasEmptyScopes S = false` side condition; we recover the guard-free form via
    `subst_unfold`/`substCore` case analysis so the ground-type reductions below still fire
    definitionally. -/
theorem LMonoTy.subst_eq_substCore' (S : Subst) (ty : LMonoTy) :
    LMonoTy.subst S ty = LMonoTy.substCore S ty := by
  induction ty with
  | ftvar x => rw [LMonoTy.subst_unfold]; rfl
  | bitvec n => rw [LMonoTy.subst_unfold]; rfl
  | tcons name ltys ih =>
    rw [LMonoTy.subst_unfold]
    simp only [LMonoTy.substCore, LMonoTys.substCore_eq_map]
    exact congrArg _ (List.map_congr_left ih)

/-- `InterpConsistentEval` restated with `LMonoTy.substCore` (structural, no well-founded guard)
    so that ground-type instantiations reduce definitionally in the kernel. -/
def LFunc.InterpConsistentEvalReduce
    {T : LExprParams}
    (tcInterp : TyConstrInterp) (opInterp : OpInterp tcInterp)
    (f : LFunc T) (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) : Prop :=
  ∀ (vt : TyVarVal) (fvarVal : FreeVarVal T tcInterp)
    (md : T.Metadata) (tySubst : Subst)
    (argExprs : List (LExpr T.mono)) (resultExpr : LExpr T.mono),
  ceval md argExprs = some resultExpr →
  let instInputTys := (List.map Prod.snd f.inputs).map (LMonoTy.substCore tySubst)
  let instOutputTy := LMonoTy.substCore tySubst f.output
  let inputSorts := instInputTys.map (LMonoTy.substTyVars vt)
  let outputSort := LMonoTy.substTyVars vt instOutputTy
  let fullSort := LSort.mkArrow outputSort inputSorts
  ∀ (h_args : List.Forall₂ (LExpr.HasTypeA []) argExprs instInputTys)
    (h_result : LExpr.HasTypeA [] resultExpr instOutputTy),
  LExpr.denote tcInterp opInterp fvarVal vt .nil resultExpr instOutputTy h_result =
    SortDenote.applyArgs tcInterp (opInterp f.name.name fullSort)
      (denoteArgs tcInterp opInterp fvarVal vt .nil argExprs instInputTys h_args)

/-- Bridge `InterpConsistentEval` → `InterpConsistentEvalReduce` (cast-heavy; done once). -/
theorem InterpConsistentEval_to_Simple
    {T : LExprParams} [DecidableEq T.IDMeta]
    (tcInterp : TyConstrInterp) (opInterp : OpInterp tcInterp)
    (f : LFunc T) (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
    (h : LFunc.InterpConsistentEval tcInterp opInterp f ceval)
    : LFunc.InterpConsistentEvalReduce tcInterp opInterp f ceval := by
  unfold Lambda.LFunc.InterpConsistentEval at h
  unfold LFunc.InterpConsistentEvalReduce
  intros vt fvarVal md tySubst argExprs resultExprs hceval instInputTys
    instOutputTy inputSorts outputSorts fullSort
  subst instOutputTy
  intros h_args
  have heq := LMonoTy.subst_eq_substCore' tySubst f.output
  intros h_result
  have hty2 : LExpr.HasTypeA [] resultExprs (LMonoTy.subst tySubst f.output) := by rw [heq]; assumption
  rw [denote_cast_ty (h_eq := heq.symm) (h₂ := hty2)]
  have heq2 : instInputTys = List.map (LMonoTy.subst tySubst) (List.map Prod.snd f.inputs) := by
    subst instInputTys
    induction (List.map Prod.snd f.inputs)
    · simp
    · rw [List.map_cons, List.map_cons]; congr 1; rw [LMonoTy.subst_eq_substCore']
  have hty3 : List.Forall₂ (LExpr.HasTypeA []) argExprs
      (List.map (LMonoTy.subst tySubst) (List.map Prod.snd f.inputs)) := by
    rw [← heq2]; assumption
  rw [denoteArgs_cast_ty (h_eq := heq2) (h₂ := hty3)]
  specialize (h vt fvarVal md tySubst argExprs resultExprs hceval hty3 hty2)
  rw [h]
  rw [applyArgs_cast_ty (h_args := heq2.symm) (h_ret := heq)]
  grind

/-! ## §2. Small helpers avoiding the `DecidableEq (LExpr CoreLParams.mono)` native-IR gap

Comparing full Core `LExpr`s by `native_decide` fails — the derived `DecidableEq (LExpr
CoreLParams.mono)` has no compiled native IR and the kernel cannot reduce it either. These helpers
compare only bare `LMonoTy`/`Nat`/`String`/`Bool` values and project `ceval` results to a
`Bool`/`Int` via `constBool?`/`constInt?`, lifting back to exact-`LExpr` equality via
`opt_eq_of_bind`. -/

/-- Reconstruct a length-2 list from its two `getD` projections (lets us establish
    `inputs.map snd = [.bool, .bool]` without deciding `LMonoTy`-list equality). -/
theorem list_eq_of_len2 {α} (l : List α) (a b : α) (d : α)
    (hlen : l.length = 2) (h0 : l.getD 0 d = a) (h1 : l.getD 1 d = b) : l = [a, b] := by
  match l with
  | [] => simp at hlen
  | [x] => simp at hlen
  | [x, y] => simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
                Option.getD_some] at h0 h1; rw [h0, h1]
  | x :: y :: z :: rest => simp at hlen

/-- Reconstruct a length-1 list from its single `getD` projection (for the unary `Bool.Not`). -/
theorem list_eq_of_len1 {α} (l : List α) (a : α) (d : α)
    (hlen : l.length = 1) (h0 : l.getD 0 d = a) : l = [a] := by
  match l with
  | [] => simp at hlen
  | [x] => simp only [List.getD, List.getElem?_cons_zero, Option.getD_some] at h0; rw [h0]
  | x :: y :: rest => simp at hlen

/-- Bool projection of a const-bool expression. -/
def constBool? : Expression.Expr → Option Bool
  | .const _ (.boolConst b) => some b
  | _ => none

/-- `constBool? e = some b` pins `e` to `.const () (.boolConst b)` (metadata is `Unit`). -/
theorem eq_const_of_constBool? {e : Expression.Expr} {b : Bool} (h : constBool? e = some b) :
    e = .const () (.boolConst b) := by
  unfold constBool? at h; split at h
  · cases h; rfl
  · exact absurd h (by simp)

/-- Lift `o.bind constBool? = some b` (decidable over `Bool`) back to the exact-`LExpr` equality. -/
theorem opt_eq_of_bind {o : Option Expression.Expr} {b : Bool}
    (hsome : o.isSome = true) (h : o.bind constBool? = some b) :
    o = some (.const () (.boolConst b)) := by
  cases o with
  | none => simp at hsome
  | some e => simp only [Option.bind] at h; rw [eq_const_of_constBool? h]

/-- Int projection of a const-int expression (the `constBool?` analog for integers). -/
def constInt? : Expression.Expr → Option Int
  | .const _ (.intConst n) => some n
  | _ => none

/-- `constInt? e = some n` pins `e` to `.const () (.intConst n)` (metadata is `Unit`). -/
theorem eq_const_of_constInt? {e : Expression.Expr} {n : Int} (h : constInt? e = some n) :
    e = .const () (.intConst n) := by
  unfold constInt? at h; split at h
  · cases h; rfl
  · exact absurd h (by simp)

/-- Lift `o.bind constInt? = some n` (decidable over `Int`) back to the exact-`LExpr` equality. -/
theorem opt_eq_of_bind_int {o : Option Expression.Expr} {n : Int}
    (hsome : o.isSome = true) (h : o.bind constInt? = some n) :
    o = some (.const () (.intConst n)) := by
  cases o with
  | none => simp at hsome
  | some e => simp only [Option.bind] at h; rw [eq_const_of_constInt? h]

/-! ## §3. Reverse-membership machinery for `Factory.append`/`ofArray`

Base members survive; a name-unique array element lands in the result. Feeds the int-op
factory-identity step (`int{Op}_lookup`). -/

variable {T : LExprParams}

theorem mem_push (F : Lambda.Factory T) (fn g : LFunc T) (h : ¬ g.name.name ∈ F)
    (hm : fn ∈ F.toArray) : fn ∈ (F.push g h).toArray := by
  show fn ∈ (F.toArray.push g); rw [Array.mem_push]; exact Or.inl hm

theorem mem_pushIfNew_of_mem (F : Lambda.Factory T) (fn g : LFunc T)
    (hm : fn ∈ F.toArray) : fn ∈ (F.pushIfNew g).toArray := by
  unfold Factory.pushIfNew; split
  · exact hm
  · exact mem_push F fn g _ hm

theorem mem_pushIfNew_self (F : Lambda.Factory T) (g : LFunc T)
    (h : ¬ g.name.name ∈ F) : g ∈ (F.pushIfNew g).toArray := by
  unfold Factory.pushIfNew; rw [dif_neg h]
  show g ∈ (F.toArray.push g); rw [Array.mem_push]; exact Or.inr rfl

theorem mem_append_of_mem_base (F : Lambda.Factory T) (a : Array (LFunc T)) (fn : LFunc T)
    (hm : fn ∈ F.toArray) : fn ∈ (F.append a).toArray := by
  unfold Factory.append
  apply Array.foldl_induction (init := F) (f := Factory.pushIfNew)
    (motive := fun _ m => fn ∈ m.toArray)
  · exact hm
  · intro i m hmem; exact mem_pushIfNew_of_mem m fn a[i] hmem

theorem name_mem_pushIfNew {F : Lambda.Factory T} {g : LFunc T} {s : String}
    (h : s ∈ (F.pushIfNew g)) : s ∈ F ∨ s = g.name.name := by
  unfold Factory.pushIfNew at h; split at h
  · exact Or.inl h
  · rw [Factory.push_mem_iff] at h; exact h.symm

/-- A name-unique element of `a` lands in `(F.append a).toArray` (given `F` lacks its name and no
    earlier `a`-element shares it). -/
theorem mem_append_getElem (F : Lambda.Factory T) (a : Array (LFunc T)) (idx : Nat) (hidx : idx < a.size)
    (hnewF : ¬ (a[idx]).name.name ∈ F)
    (hbefore : ∀ j (hj : j < a.size), j < idx → (a[j]).name.name ≠ (a[idx]).name.name) :
    (a[idx]) ∈ (F.append a).toArray := by
  unfold Factory.append
  have key := Array.foldl_induction (as := a) (init := F) (f := Factory.pushIfNew)
    (motive := fun i m =>
      (a[idx]) ∈ m.toArray ∨
      (idx ≥ i ∧ (∀ s, s ∈ m → s ∈ F ∨ ∃ j, ∃ (hj : j < a.size), j < i ∧ (a[j]).name.name = s)))
    ?base ?step
  case base =>
    refine Or.inr ⟨Nat.zero_le _, ?_⟩
    intro s hs; exact Or.inl hs
  case step =>
    intro ⟨i, hi⟩ m ih
    rcases ih with hin | ⟨hge, hnames⟩
    · exact Or.inl (mem_pushIfNew_of_mem m (a[idx]) a[i] hin)
    · by_cases heq : i = idx
      · subst heq
        have hnew : ¬ (a[i]).name.name ∈ m := by
          intro hmem
          rcases hnames (a[i]).name.name hmem with h | ⟨j, hj, hji, hjn⟩
          · exact hnewF h
          · exact hbefore j hj hji hjn
        left; exact mem_pushIfNew_self m a[i] hnew
      · have hlt : i < idx := Nat.lt_of_le_of_ne hge heq
        refine Or.inr ⟨hlt, ?_⟩
        intro s hs
        rcases name_mem_pushIfNew hs with h | h
        · rcases hnames s h with h' | ⟨j, hj, hji, hjn⟩
          · exact Or.inl h'
          · exact Or.inr ⟨j, hj, Nat.lt_succ_of_lt hji, hjn⟩
        · exact Or.inr ⟨i, hi, Nat.lt_succ_self i, h.symm⟩
  rcases key with hin | ⟨hge, _⟩
  · exact hin
  · omega

/-! ## §4. `CoreOp.ofString` inverse lemmas

Pin a parsed operator kind back to its canonical source name: `ofString_bool` gives `"Bool." ++ k`
and `ofString_numeric_int` gives `"Int." ++ k`, by peeling the parser's `match`/`if` cascade. -/

/-- `lookupKind` inversion: a hit `lookupKind names s = some k` means `(k, s)` is in the table. -/
theorem lookupKind_inv {α : Type} {β} [BEq β] [LawfulBEq β]
    (names : List (α × β)) (s : β) (k : α)
    (h : Core.lookupKind names s = some k) : (k, s) ∈ names := by
  unfold Core.lookupKind at h
  split at h
  · rename_i pr hf
    injection h with hk
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    simp only [beq_iff_eq] at hpred
    subst hk; subst hpred; exact hmem
  · simp at h

/-- A `BoolOpKind.ofString?` hit pins the suffix string to the kind's canonical name. -/
theorem boolSuffix (s : String) (k : BoolOpKind)
    (h : BoolOpKind.ofString? s = some k) : s = BoolOpKind.toString k := by
  have hmem := lookupKind_inv BoolOpKind.names s k h
  cases k <;>
    simp only [BoolOpKind.names, List.mem_cons, Prod.mk.injEq,
      reduceCtorEq, false_and, List.not_mem_nil, or_false, false_or, true_and] at hmem <;>
    (subst hmem; rfl)

open String in
/-- Split witness for `"Bool." ++ t` at position 5 (built by peeling the 5 prefix chars). -/
theorem builtSplitSlice (t : String) :
    let s := ("Bool." ++ t).toSlice
    ∃ (h0 : s.startPos ≠ s.endPos)
      (h1 : (s.startPos.next h0) ≠ s.endPos)
      (h2 : ((s.startPos.next h0).next h1) ≠ s.endPos)
      (h3 : (((s.startPos.next h0).next h1).next h2) ≠ s.endPos)
      (h4 : ((((s.startPos.next h0).next h1).next h2).next h3) ≠ s.endPos),
      (((((s.startPos.next h0).next h1).next h2).next h3).next h4).Splits "Bool." t := by
  intro s
  have e1 : s.copy = String.singleton 'B' ++ (String.singleton 'o' ++
      (String.singleton 'o' ++ (String.singleton 'l' ++ (String.singleton '.' ++ t)))) := by
    show ("Bool." ++ t).toSlice.copy = _
    rw [String.copy_toSlice]
    simp only [← String.append_assoc]; congr 1
  have g0 : s.startPos.Splits "" s.copy := String.Slice.splits_startPos s
  rw [e1] at g0
  have g5 := g0.next.next.next.next.next
  have e2 : ("" ++ String.singleton 'B' ++ String.singleton 'o' ++ String.singleton 'o'
      ++ String.singleton 'l' ++ String.singleton '.' : String) = "Bool." := by decide
  rw [e2] at g5
  exact ⟨_, _, _, _, _, g5⟩

/-- `("Bool." ++ t).drop 5 = t` (the crux; manual position arithmetic, kernel string ops do not reduce). -/
theorem cruxBool (t : String) : (("Bool." ++ t).drop 5).toString = t := by
  show (("Bool." ++ t).toSlice.sliceFrom (("Bool." ++ t).toSlice.startPos.nextn 5)).copy = t
  obtain ⟨h0, h1, h2, h3, h4, hspl⟩ := builtSplitSlice t
  have hnextn : ("Bool." ++ t).toSlice.startPos.nextn 5
      = (((((("Bool." ++ t).toSlice.startPos.next h0).next h1).next h2).next h3).next h4) := by
    rw [String.Slice.Pos.nextn, dif_pos h0, String.Slice.Pos.nextn, dif_pos h1,
        String.Slice.Pos.nextn, dif_pos h2, String.Slice.Pos.nextn, dif_pos h3,
        String.Slice.Pos.nextn, dif_pos h4, String.Slice.Pos.nextn]
  rw [hnextn]
  exact hspl.copy_sliceFrom_eq

/-- A `"Bool."`-prefixed name equals `"Bool." ++ (its 5-drop)`. -/
theorem boolPrefix (name : String) (h : name.startsWith "Bool." = true) :
    name = "Bool." ++ (name.drop 5).toString := by
  have h2 := String.Slice.Pattern.ForwardSliceSearcher.startsWith_iff
    (pat := "Bool.".toSlice) (s := name.toSlice)
  simp only [String.copy_toSlice] at h2
  obtain ⟨t, ht⟩ := h2.mp h
  rw [ht, cruxBool t]

open String in
/-- Split witness for `"Int." ++ t` at position 4. -/
theorem builtSplitSliceInt (t : String) :
    let s := ("Int." ++ t).toSlice
    ∃ (h0 : s.startPos ≠ s.endPos)
      (h1 : (s.startPos.next h0) ≠ s.endPos)
      (h2 : ((s.startPos.next h0).next h1) ≠ s.endPos)
      (h3 : (((s.startPos.next h0).next h1).next h2) ≠ s.endPos),
      ((((s.startPos.next h0).next h1).next h2).next h3).Splits "Int." t := by
  intro s
  have e1 : s.copy = String.singleton 'I' ++ (String.singleton 'n' ++
      (String.singleton 't' ++ (String.singleton '.' ++ t))) := by
    show ("Int." ++ t).toSlice.copy = _
    rw [String.copy_toSlice]; simp only [← String.append_assoc]; congr 1
  have g0 : s.startPos.Splits "" s.copy := String.Slice.splits_startPos s
  rw [e1] at g0
  have g4 := g0.next.next.next.next
  have e2 : ("" ++ String.singleton 'I' ++ String.singleton 'n' ++ String.singleton 't'
      ++ String.singleton '.' : String) = "Int." := by decide
  rw [e2] at g4
  exact ⟨_, _, _, _, g4⟩

/-- `("Int." ++ t).drop 4 = t`. -/
theorem cruxInt (t : String) : (("Int." ++ t).drop 4).toString = t := by
  show (("Int." ++ t).toSlice.sliceFrom (("Int." ++ t).toSlice.startPos.nextn 4)).copy = t
  obtain ⟨h0, h1, h2, h3, hspl⟩ := builtSplitSliceInt t
  have hnextn : ("Int." ++ t).toSlice.startPos.nextn 4
      = ((((("Int." ++ t).toSlice.startPos.next h0).next h1).next h2).next h3) := by
    rw [String.Slice.Pos.nextn, dif_pos h0, String.Slice.Pos.nextn, dif_pos h1,
        String.Slice.Pos.nextn, dif_pos h2, String.Slice.Pos.nextn, dif_pos h3,
        String.Slice.Pos.nextn]
  rw [hnextn]
  exact hspl.copy_sliceFrom_eq

/-- An `"Int."`-prefixed name equals `"Int." ++ (its 4-drop)`. -/
theorem intPrefix (name : String) (h : name.startsWith "Int." = true) :
    name = "Int." ++ (name.drop 4).toString := by
  have h2 := String.Slice.Pattern.ForwardSliceSearcher.startsWith_iff
    (pat := "Int.".toSlice) (s := name.toSlice)
  simp only [String.copy_toSlice] at h2
  obtain ⟨t, ht⟩ := h2.mp h
  rw [ht, cruxInt t]

/-- A `NumericOpKind.ofString?` hit pins the suffix string to the kind's canonical name. -/
theorem numSuffix (s : String) (k : NumericOpKind)
    (h : NumericOpKind.ofString? s = some k) : s = NumericOpKind.toString k := by
  have hmem := lookupKind_inv NumericOpKind.names s k h
  cases k <;>
    simp only [NumericOpKind.names, List.mem_cons, Prod.mk.injEq,
      reduceCtorEq, false_and, List.not_mem_nil, or_false, false_or, true_and] at hmem <;>
    (subst hmem; rfl)

theorem parseBvOp_not_bool (name : String) (k : BoolOpKind) :
    Core.parseBvOp? name ≠ some (.bool k) := by
  intro hc
  unfold Core.parseBvOp? Core.parseBvExtract? at hc
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hc
  obtain ⟨_, _, _, _, _, _, hc⟩ := hc
  repeat' split at hc
  all_goals simp_all [Option.bind_eq_some_iff]

theorem numLookup_not_bool (name : String) (k : BoolOpKind) :
    ([("Int.", NumericType.int), ("Real.", NumericType.real)].findSome? fun (pfx, ty) =>
      if name.startsWith pfx then
        match NumericOpKind.ofString? (name.drop pfx.length).toString with
        | some kind => some (CoreOp.numeric ⟨ty, kind⟩)
        | none => none
      else none) ≠ some (.bool k) := by
  intro hc
  simp only [List.findSome?] at hc
  by_cases hi : name.startsWith "Int." <;>
  by_cases hr : name.startsWith "Real." <;>
    simp only [hi, hr, if_true] at hc <;>
    (try cases hd : NumericOpKind.ofString? (name.drop "Int.".length).toString <;>
      simp_all) <;>
    (cases hd : NumericOpKind.ofString? (name.drop "Real.".length).toString <;> simp_all)

/-- **`ofString` inverse (bool).** `CoreOp.ofString name = .bool k` pins `name` to the canonical
    `"Bool." ++ k`. Peels the parser's `match`/`if` cascade: `parseBvOp?`/numeric branches contradict
    a `.bool` result, and the surviving `"Bool."` branch gives `startsWith` + `ofString?`, closed by
    `boolPrefix` + `boolSuffix`. -/
theorem ofString_bool (name : String) (k : BoolOpKind)
    (h : CoreOp.ofString name = .bool k) :
    name = "Bool." ++ BoolOpKind.toString k := by
  unfold CoreOp.ofString at h
  simp only [] at h
  split at h
  · rename_i op hbv; subst h; exact absurd hbv (parseBvOp_not_bool name _)
  split at h
  · split at h <;> simp_all
  split at h
  · rename_i op hnum; subst h; exact absurd hnum (numLookup_not_bool name _)
  split at h
  · rename_i hb
    split at h
    · rename_i hk; injection h with hk'; subst hk'
      rw [boolPrefix _ hb, boolSuffix _ _ hk]
    · simp_all
  all_goals (exfalso; repeat' split at h) <;> simp_all

theorem parseBvOp_not_numeric (name : String) (op : NumericOp) :
    Core.parseBvOp? name ≠ some (.numeric op) := by
  intro hc
  unfold Core.parseBvOp? Core.parseBvExtract? at hc
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hc
  obtain ⟨_, _, _, _, _, _, hc⟩ := hc
  repeat' split at hc
  all_goals simp_all [Option.bind_eq_some_iff]

theorem numLookup_int_inv (name : String) (k : NumericOpKind)
    (h : ([("Int.", NumericType.int), ("Real.", NumericType.real)].findSome? fun (pfx, ty) =>
      if name.startsWith pfx then
        match NumericOpKind.ofString? (name.drop pfx.length).toString with
        | some kind => some (CoreOp.numeric ⟨ty, kind⟩)
        | none => none
      else none) = some (.numeric ⟨.int, k⟩)) :
    name.startsWith "Int." = true ∧
      NumericOpKind.ofString? (name.drop "Int.".length).toString = some k := by
  simp only [List.findSome?] at h
  by_cases hi : name.startsWith "Int." <;>
  by_cases hr : name.startsWith "Real." <;>
    simp only [hi, hr, if_true] at h <;>
    (try cases hd : NumericOpKind.ofString? (name.drop "Int.".length).toString <;> simp_all) <;>
    (cases hd : NumericOpKind.ofString? (name.drop "Real.".length).toString <;> simp_all)

/-- **`ofString` inverse (int-numeric).** `CoreOp.ofString name = .numeric ⟨.int, k⟩` pins `name` to
    `"Int." ++ k`. Same cascade peel, closed by `intPrefix` + `numSuffix`. -/
theorem ofString_numeric_int (name : String) (k : NumericOpKind)
    (h : CoreOp.ofString name = .numeric ⟨.int, k⟩) :
    name = "Int." ++ NumericOpKind.toString k := by
  unfold CoreOp.ofString at h
  simp only [] at h
  split at h
  · rename_i op hbv; subst h; exact absurd hbv (parseBvOp_not_numeric name _)
  split at h
  · split at h <;> simp_all
  split at h
  · rename_i op hnum; subst h
    obtain ⟨hpre, hk⟩ := numLookup_int_inv name k hnum
    have : ("Int." : String).length = 4 := by decide
    rw [this] at hk
    rw [intPrefix _ hpre, numSuffix _ _ hk]
  all_goals (exfalso; repeat' split at h) <;> simp_all

/-! ## §5. Per-operator interpretation lemmas over `Core.Factory` -/

private abbrev boolBinSort : LSort :=
  .tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]]
private abbrev boolUnSort : LSort :=
  .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]
private abbrev intBinSort : LSort :=
  .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]]
private abbrev intUnSort : LSort :=
  .tcons "arrow" [.tcons "int" [], .tcons "int" []]
private abbrev intCmpSort : LSort :=
  .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]]

/-- **Generic binary-bool interpretation.** Given the factory-field facts for a bool binary op
    `nm` (membership, ceval-some, name, output, input-types) and its ceval's behaviour on constant
    booleans (`hbeh`, established per op by `native_decide` via the `constBool?` projection), any
    factory-consistent model interprets `nm` at the bool-binary sort as `op`. -/
theorem binBoolInterp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [inst : TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory)
    (nm : String) (op : Bool → Bool → Bool)
    (hmem : nm ∈ Core.Factory)
    (hceval : (Core.Factory[nm]'hmem).concreteEval.isSome = true)
    (hname : (Core.Factory[nm]'hmem).name.name = nm)
    (houtput : (Core.Factory[nm]'hmem).output = .bool)
    (hinput : List.map Prod.snd (Core.Factory[nm]'hmem).inputs = [LMonoTy.bool, LMonoTy.bool])
    (hbeh : ∀ (b1 b2 : Bool),
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.boolConst b1), .const () (.boolConst b2)])).isSome = true ∧
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.boolConst b1), .const () (.boolConst b2)])).bind constBool?
        = some (op b1 b2)) :
    opInterp nm boolBinSort = fun (p q : Bool) => op p q := by
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hceval
  have h_ic := InterpConsistentEval_to_Simple tcInterp opInterp _ ceval
    (hIC.2 nm hmem ceval h_ceval_eq)
  unfold LFunc.InterpConsistentEvalReduce at h_ic
  rw [hinput, houtput, hname] at h_ic
  funext p q
  have h_eval : ceval () [.const () (.boolConst p), .const () (.boolConst q)]
      = some (.const () (.boolConst (op p q))) := by
    obtain ⟨hs, hb⟩ := hbeh p q
    rw [h_ceval_eq] at hs hb
    exact opt_eq_of_bind hs hb
  have h_vt : TyVarVal := fun _ => .tcons "bool" []
  have h_fv : FreeVarVal CoreLParams tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited tcInterp inst s)
  have h_inst := h_ic h_vt h_fv () Subst.empty
      [.const () (.boolConst p), .const () (.boolConst q)]
      (.const () (.boolConst (op p q))) h_eval
  have h_args : List.Forall₂ (LExpr.HasTypeA (T := CoreLParams) [])
      [.const () (.boolConst p), .const () (.boolConst q)]
      [.tcons "bool" [], .tcons "bool" []] := .cons .const (.cons .const .nil)
  have h_result : LExpr.HasTypeA (T := CoreLParams) [] (.const () (.boolConst (op p q))) (.tcons "bool" []) := .const
  have h_eq := h_inst h_args h_result
  change (op p q) = opInterp nm boolBinSort p q at h_eq
  exact h_eq.symm

/-- **Generic unary-bool interpretation** (for `Bool.Not`), the arity-1 analog of `binBoolInterp`. -/
theorem unBoolInterp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [inst : TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory)
    (nm : String) (op : Bool → Bool)
    (hmem : nm ∈ Core.Factory)
    (hceval : (Core.Factory[nm]'hmem).concreteEval.isSome = true)
    (hname : (Core.Factory[nm]'hmem).name.name = nm)
    (houtput : (Core.Factory[nm]'hmem).output = .bool)
    (hinput : List.map Prod.snd (Core.Factory[nm]'hmem).inputs = [LMonoTy.bool])
    (hbeh : ∀ (b : Bool),
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.boolConst b)])).isSome = true ∧
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.boolConst b)])).bind constBool?
        = some (op b)) :
    opInterp nm boolUnSort = fun (p : Bool) => op p := by
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hceval
  have h_ic := InterpConsistentEval_to_Simple tcInterp opInterp _ ceval
    (hIC.2 nm hmem ceval h_ceval_eq)
  unfold LFunc.InterpConsistentEvalReduce at h_ic
  rw [hinput, houtput, hname] at h_ic
  funext p
  have h_eval : ceval () [.const () (.boolConst p)]
      = some (.const () (.boolConst (op p))) := by
    obtain ⟨hs, hb⟩ := hbeh p
    rw [h_ceval_eq] at hs hb
    exact opt_eq_of_bind hs hb
  have h_vt : TyVarVal := fun _ => .tcons "bool" []
  have h_fv : FreeVarVal CoreLParams tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited tcInterp inst s)
  have h_inst := h_ic h_vt h_fv () Subst.empty
      [.const () (.boolConst p)] (.const () (.boolConst (op p))) h_eval
  have h_args : List.Forall₂ (LExpr.HasTypeA (T := CoreLParams) [])
      [.const () (.boolConst p)] [.tcons "bool" []] := .cons .const .nil
  have h_result : LExpr.HasTypeA (T := CoreLParams) [] (.const () (.boolConst (op p))) (.tcons "bool" []) := .const
  have h_eq := h_inst h_args h_result
  change (op p) = opInterp nm boolUnSort p at h_eq
  exact h_eq.symm

/-- **Generic binary-int interpretation.** The `Int → Int → Int` analog of `binBoolInterp`:
    given the factory-field facts for a binary int op `nm` and its ceval's behaviour on constant
    integers (`hbeh`, via the `constInt?` projection), any factory-consistent model interprets `nm`
    at the int-binary sort as `op`. -/
theorem binIntInterp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [inst : TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory)
    (nm : String) (op : Int → Int → Int)
    (hmem : nm ∈ Core.Factory)
    (hceval : (Core.Factory[nm]'hmem).concreteEval.isSome = true)
    (hname : (Core.Factory[nm]'hmem).name.name = nm)
    (houtput : (Core.Factory[nm]'hmem).output = .int)
    (hinput : List.map Prod.snd (Core.Factory[nm]'hmem).inputs = [LMonoTy.int, LMonoTy.int])
    (hbeh : ∀ (n1 n2 : Int),
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.intConst n1), .const () (.intConst n2)])).isSome = true ∧
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.intConst n1), .const () (.intConst n2)])).bind constInt?
        = some (op n1 n2)) :
    opInterp nm intBinSort = fun (p q : Int) => op p q := by
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hceval
  have h_ic := InterpConsistentEval_to_Simple tcInterp opInterp _ ceval
    (hIC.2 nm hmem ceval h_ceval_eq)
  unfold LFunc.InterpConsistentEvalReduce at h_ic
  rw [hinput, houtput, hname] at h_ic
  funext p q
  have h_eval : ceval () [.const () (.intConst p), .const () (.intConst q)]
      = some (.const () (.intConst (op p q))) := by
    obtain ⟨hs, hb⟩ := hbeh p q
    rw [h_ceval_eq] at hs hb
    exact opt_eq_of_bind_int hs hb
  have h_vt : TyVarVal := fun _ => .tcons "int" []
  have h_fv : FreeVarVal CoreLParams tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited tcInterp inst s)
  have h_inst := h_ic h_vt h_fv () Subst.empty
      [.const () (.intConst p), .const () (.intConst q)]
      (.const () (.intConst (op p q))) h_eval
  have h_args : List.Forall₂ (LExpr.HasTypeA (T := CoreLParams) [])
      [.const () (.intConst p), .const () (.intConst q)]
      [.tcons "int" [], .tcons "int" []] := .cons .const (.cons .const .nil)
  have h_result : LExpr.HasTypeA (T := CoreLParams) [] (.const () (.intConst (op p q))) (.tcons "int" []) := .const
  have h_eq := h_inst h_args h_result
  change (op p q) = opInterp nm intBinSort p q at h_eq
  exact h_eq.symm

/-- **Generic GUARDED binary-int interpretation** (for `Int.Div`/`Int.Mod`). The `binaryOp … (· != 0)`
    guard makes `concreteEval` fold to `none` at divisor `0`, so consistency pins `opInterp nm` only
    at NONZERO second argument: `hbeh` is required (and the conclusion holds) only for `q ≠ 0`. The
    at-zero value of `opInterp nm` is model-chosen and left unconstrained here — the SMT `divByZero`/
    `modByZero` faithfully represents it. -/
theorem binIntGuardedInterp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [inst : TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory)
    (nm : String) (op : Int → Int → Int)
    (hmem : nm ∈ Core.Factory)
    (hceval : (Core.Factory[nm]'hmem).concreteEval.isSome = true)
    (hname : (Core.Factory[nm]'hmem).name.name = nm)
    (houtput : (Core.Factory[nm]'hmem).output = .int)
    (hinput : List.map Prod.snd (Core.Factory[nm]'hmem).inputs = [LMonoTy.int, LMonoTy.int])
    (hbeh : ∀ (n1 n2 : Int), n2 ≠ 0 →
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.intConst n1), .const () (.intConst n2)])).isSome = true ∧
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.intConst n1), .const () (.intConst n2)])).bind constInt?
        = some (op n1 n2)) :
    ∀ (p q : Int), q ≠ 0 → opInterp nm intBinSort p q = op p q := by
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hceval
  have h_ic := InterpConsistentEval_to_Simple tcInterp opInterp _ ceval
    (hIC.2 nm hmem ceval h_ceval_eq)
  unfold LFunc.InterpConsistentEvalReduce at h_ic
  rw [hinput, houtput, hname] at h_ic
  intro p q hq
  have h_eval : ceval () [.const () (.intConst p), .const () (.intConst q)]
      = some (.const () (.intConst (op p q))) := by
    obtain ⟨hs, hb⟩ := hbeh p q hq
    rw [h_ceval_eq] at hs hb
    exact opt_eq_of_bind_int hs hb
  have h_vt : TyVarVal := fun _ => .tcons "int" []
  have h_fv : FreeVarVal CoreLParams tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited tcInterp inst s)
  have h_inst := h_ic h_vt h_fv () Subst.empty
      [.const () (.intConst p), .const () (.intConst q)]
      (.const () (.intConst (op p q))) h_eval
  have h_args : List.Forall₂ (LExpr.HasTypeA (T := CoreLParams) [])
      [.const () (.intConst p), .const () (.intConst q)]
      [.tcons "int" [], .tcons "int" []] := .cons .const (.cons .const .nil)
  have h_result : LExpr.HasTypeA (T := CoreLParams) [] (.const () (.intConst (op p q))) (.tcons "int" []) := .const
  have h_eq := h_inst h_args h_result
  change (op p q) = opInterp nm intBinSort p q at h_eq
  exact h_eq.symm

/-- **Generic unary-int interpretation** (for `Int.Neg`), the arity-1 int analog of `unBoolInterp`. -/
theorem unIntInterp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [inst : TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory)
    (nm : String) (op : Int → Int)
    (hmem : nm ∈ Core.Factory)
    (hceval : (Core.Factory[nm]'hmem).concreteEval.isSome = true)
    (hname : (Core.Factory[nm]'hmem).name.name = nm)
    (houtput : (Core.Factory[nm]'hmem).output = .int)
    (hinput : List.map Prod.snd (Core.Factory[nm]'hmem).inputs = [LMonoTy.int])
    (hbeh : ∀ (n : Int),
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.intConst n)])).isSome = true ∧
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.intConst n)])).bind constInt?
        = some (op n)) :
    opInterp nm intUnSort = fun (p : Int) => op p := by
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hceval
  have h_ic := InterpConsistentEval_to_Simple tcInterp opInterp _ ceval
    (hIC.2 nm hmem ceval h_ceval_eq)
  unfold LFunc.InterpConsistentEvalReduce at h_ic
  rw [hinput, houtput, hname] at h_ic
  funext p
  have h_eval : ceval () [.const () (.intConst p)]
      = some (.const () (.intConst (op p))) := by
    obtain ⟨hs, hb⟩ := hbeh p
    rw [h_ceval_eq] at hs hb
    exact opt_eq_of_bind_int hs hb
  have h_vt : TyVarVal := fun _ => .tcons "int" []
  have h_fv : FreeVarVal CoreLParams tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited tcInterp inst s)
  have h_inst := h_ic h_vt h_fv () Subst.empty
      [.const () (.intConst p)] (.const () (.intConst (op p))) h_eval
  have h_args : List.Forall₂ (LExpr.HasTypeA (T := CoreLParams) [])
      [.const () (.intConst p)] [.tcons "int" []] := .cons .const .nil
  have h_result : LExpr.HasTypeA (T := CoreLParams) [] (.const () (.intConst (op p))) (.tcons "int" []) := .const
  have h_eq := h_inst h_args h_result
  change (op p) = opInterp nm intUnSort p at h_eq
  exact h_eq.symm

/-- **Generic binary-int→bool interpretation** (for the comparisons `Int.Lt`/`Le`/`Gt`/`Ge`):
    the `Int → Int → Bool` analog of `binIntInterp`. The folded result is a bool const, so `hbeh`
    projects via `constBool?`, and the output type/sort is `bool`. -/
theorem binIntCmpInterp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [inst : TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory)
    (nm : String) (op : Int → Int → Bool)
    (hmem : nm ∈ Core.Factory)
    (hceval : (Core.Factory[nm]'hmem).concreteEval.isSome = true)
    (hname : (Core.Factory[nm]'hmem).name.name = nm)
    (houtput : (Core.Factory[nm]'hmem).output = .bool)
    (hinput : List.map Prod.snd (Core.Factory[nm]'hmem).inputs = [LMonoTy.int, LMonoTy.int])
    (hbeh : ∀ (n1 n2 : Int),
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.intConst n1), .const () (.intConst n2)])).isSome = true ∧
        ((Core.Factory[nm]'hmem).concreteEval.bind
          (fun f => f () [.const () (.intConst n1), .const () (.intConst n2)])).bind constBool?
        = some (op n1 n2)) :
    opInterp nm intCmpSort = fun (p q : Int) => op p q := by
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hceval
  have h_ic := InterpConsistentEval_to_Simple tcInterp opInterp _ ceval
    (hIC.2 nm hmem ceval h_ceval_eq)
  unfold LFunc.InterpConsistentEvalReduce at h_ic
  rw [hinput, houtput, hname] at h_ic
  funext p q
  have h_eval : ceval () [.const () (.intConst p), .const () (.intConst q)]
      = some (.const () (.boolConst (op p q))) := by
    obtain ⟨hs, hb⟩ := hbeh p q
    rw [h_ceval_eq] at hs hb
    exact opt_eq_of_bind hs hb
  have h_vt : TyVarVal := fun _ => .tcons "int" []
  have h_fv : FreeVarVal CoreLParams tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited tcInterp inst s)
  have h_inst := h_ic h_vt h_fv () Subst.empty
      [.const () (.intConst p), .const () (.intConst q)]
      (.const () (.boolConst (op p q))) h_eval
  have h_args : List.Forall₂ (LExpr.HasTypeA (T := CoreLParams) [])
      [.const () (.intConst p), .const () (.intConst q)]
      [.tcons "int" [], .tcons "int" []] := .cons .const (.cons .const .nil)
  have h_result : LExpr.HasTypeA (T := CoreLParams) [] (.const () (.boolConst (op p q))) (.tcons "bool" []) := .const
  have h_eq := h_inst h_args h_result
  change (op p q) = opInterp nm intCmpSort p q at h_eq
  exact h_eq.symm

meta section

-- Factory membership facts as top-level lemmas (so the field `native_decide`s below have CLOSED
-- goals — a local `have hmem := by native_decide` would make them depend on a free `hmem`).
theorem and_mem : "Bool.And" ∈ Core.Factory := by native_decide
theorem or_mem : "Bool.Or" ∈ Core.Factory := by native_decide
theorem implies_mem : "Bool.Implies" ∈ Core.Factory := by native_decide
theorem equiv_mem : "Bool.Equiv" ∈ Core.Factory := by native_decide
theorem not_mem : "Bool.Not" ∈ Core.Factory := by native_decide

theorem and_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Bool.And" boolBinSort = fun (p q : Bool) => (p && q) := by
  refine binBoolInterp hIC "Bool.And" (· && ·) and_mem ?_ ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · refine list_eq_of_len2 _ _ _ LMonoTy.bool ?_ ?_ ?_ <;> native_decide
  · intro b1 b2; constructor <;> (cases b1 <;> cases b2 <;> native_decide)

theorem or_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Bool.Or" boolBinSort = fun (p q : Bool) => (p || q) := by
  refine binBoolInterp hIC "Bool.Or" (· || ·) or_mem ?_ ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · refine list_eq_of_len2 _ _ _ LMonoTy.bool ?_ ?_ ?_ <;> native_decide
  · intro b1 b2; constructor <;> (cases b1 <;> cases b2 <;> native_decide)

theorem implies_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Bool.Implies" boolBinSort = fun (p q : Bool) => (!p || q) := by
  refine binBoolInterp hIC "Bool.Implies" (fun p q => !p || q) implies_mem ?_ ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · refine list_eq_of_len2 _ _ _ LMonoTy.bool ?_ ?_ ?_ <;> native_decide
  · intro b1 b2; constructor <;> (cases b1 <;> cases b2 <;> native_decide)

theorem equiv_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Bool.Equiv" boolBinSort = fun (p q : Bool) => decide (p = q) := by
  refine binBoolInterp hIC "Bool.Equiv" (fun p q => decide (p = q)) equiv_mem ?_ ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · refine list_eq_of_len2 _ _ _ LMonoTy.bool ?_ ?_ ?_ <;> native_decide
  · intro b1 b2; constructor <;> (cases b1 <;> cases b2 <;> native_decide)

theorem not_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Bool.Not" boolUnSort = fun (p : Bool) => !p := by
  refine unBoolInterp hIC "Bool.Not" (fun p => !p) not_mem ?_ ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · refine list_eq_of_len1 _ _ LMonoTy.bool ?_ ?_ <;> native_decide
  · intro b; constructor <;> (cases b <;> native_decide)

-- Factory membership fact for the int add op.
theorem intAdd_mem : "Int.Add" ∈ Core.Factory := by native_decide

/-- **The factory identity for `Int.Add`.**
    `Core.Factory["Int.Add"]?` is the *named* `intAddFunc` record's underlying `LFunc`. Proven by
    head-peeling `intAddFunc`'s membership in `WFFactoryArray` (never forcing the 200-element tail),
    then the `ofArray`/name-nodup lookup bridge. -/
theorem intAdd_lookup :
    Core.Factory["Int.Add"]? = some (intAddFunc (T := CoreLParams)).func := by
  have hmem_wf : (intAddFunc (T := CoreLParams)) ∈ Core.WFFactoryArray := by
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_self
  have hmem : (intAddFunc (T := CoreLParams)).func
      ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨intAddFunc (T := CoreLParams), hmem_wf, rfl⟩
  have hnodup : List.Nodup
      ((Core.WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    Core.WFFactoryArray_func_name_nodup
  have hname : (intAddFunc (T := CoreLParams)).func.name.name = "Int.Add" := by
    native_decide
  have hlk := Lambda.Factory.get?_ofArray_of_mem hmem hnodup
  rw [hname] at hlk
  simpa [Core.Factory, Core.WFFactory, Lambda.WFLFactory.ofArray] using hlk

/-- getElem form of `intAdd_lookup`: identifies the looked-up function with `intAddFunc.func`. -/
theorem intAdd_getElem :
    Core.Factory["Int.Add"]'intAdd_mem = (intAddFunc (T := CoreLParams)).func :=
  Lambda.Factory.getElem?_some_getElem intAdd_lookup

theorem add_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Int.Add" intBinSort = fun (p q : Int) => p + q := by
  refine binIntInterp hIC "Int.Add" (· + ·) intAdd_mem ?_ ?_ ?_ ?_ ?_
  · rw [intAdd_getElem]; rfl
  · rw [intAdd_getElem]; rfl
  · rw [intAdd_getElem]; rfl
  · rw [intAdd_getElem]; rfl
  · intro n1 n2
    rw [intAdd_getElem]
    refine ⟨?_, ?_⟩ <;>
      simp only [intAddFunc, binaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
        LExpr.denoteInt, LExpr.intConst, Option.bind, constInt?, if_true,
        Option.isSome_some, Int.add_def]

-- ── Int.Sub (WFFactoryArray index 1) ──
theorem intSub_mem : "Int.Sub" ∈ Core.Factory := by native_decide

theorem intSub_lookup :
    Core.Factory["Int.Sub"]? = some (intSubFunc (T := CoreLParams)).func := by
  have hmem_wf : (intSubFunc (T := CoreLParams)) ∈ Core.WFFactoryArray := by
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hmem : (intSubFunc (T := CoreLParams)).func
      ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨intSubFunc (T := CoreLParams), hmem_wf, rfl⟩
  have hnodup : List.Nodup
      ((Core.WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    Core.WFFactoryArray_func_name_nodup
  have hname : (intSubFunc (T := CoreLParams)).func.name.name = "Int.Sub" := by
    native_decide
  have hlk := Lambda.Factory.get?_ofArray_of_mem hmem hnodup
  rw [hname] at hlk
  simpa [Core.Factory, Core.WFFactory, Lambda.WFLFactory.ofArray] using hlk

theorem intSub_getElem :
    Core.Factory["Int.Sub"]'intSub_mem = (intSubFunc (T := CoreLParams)).func :=
  Lambda.Factory.getElem?_some_getElem intSub_lookup

theorem sub_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Int.Sub" intBinSort = fun (p q : Int) => p - q := by
  refine binIntInterp hIC "Int.Sub" (· - ·) intSub_mem ?_ ?_ ?_ ?_ ?_
  · rw [intSub_getElem]; rfl
  · rw [intSub_getElem]; rfl
  · rw [intSub_getElem]; rfl
  · rw [intSub_getElem]; rfl
  · intro n1 n2
    rw [intSub_getElem]
    refine ⟨?_, ?_⟩ <;>
      (simp only [intSubFunc, binaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
        LExpr.denoteInt, LExpr.intConst, Option.bind, constInt?, if_true,
        Option.isSome_some]; try rfl)

-- ── Int.Mul (WFFactoryArray index 2) ──
theorem intMul_mem : "Int.Mul" ∈ Core.Factory := by native_decide

theorem intMul_lookup :
    Core.Factory["Int.Mul"]? = some (intMulFunc (T := CoreLParams)).func := by
  have hmem_wf : (intMulFunc (T := CoreLParams)) ∈ Core.WFFactoryArray := by
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hmem : (intMulFunc (T := CoreLParams)).func
      ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨intMulFunc (T := CoreLParams), hmem_wf, rfl⟩
  have hnodup : List.Nodup
      ((Core.WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    Core.WFFactoryArray_func_name_nodup
  have hname : (intMulFunc (T := CoreLParams)).func.name.name = "Int.Mul" := by
    native_decide
  have hlk := Lambda.Factory.get?_ofArray_of_mem hmem hnodup
  rw [hname] at hlk
  simpa [Core.Factory, Core.WFFactory, Lambda.WFLFactory.ofArray] using hlk

theorem intMul_getElem :
    Core.Factory["Int.Mul"]'intMul_mem = (intMulFunc (T := CoreLParams)).func :=
  Lambda.Factory.getElem?_some_getElem intMul_lookup

theorem mul_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Int.Mul" intBinSort = fun (p q : Int) => p * q := by
  refine binIntInterp hIC "Int.Mul" (· * ·) intMul_mem ?_ ?_ ?_ ?_ ?_
  · rw [intMul_getElem]; rfl
  · rw [intMul_getElem]; rfl
  · rw [intMul_getElem]; rfl
  · rw [intMul_getElem]; rfl
  · intro n1 n2
    rw [intMul_getElem]
    refine ⟨?_, ?_⟩ <;>
      simp only [intMulFunc, binaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
        LExpr.denoteInt, LExpr.intConst, Option.bind, constInt?, if_true,
        Option.isSome_some, Int.mul_def]

-- ── Int.Neg (unary, WFFactoryArray index 11) ──
theorem intNeg_mem : "Int.Neg" ∈ Core.Factory := by native_decide

theorem intNeg_lookup :
    Core.Factory["Int.Neg"]? = some (intNegFunc (T := CoreLParams)).func := by
  have hmem_wf : (intNegFunc (T := CoreLParams)) ∈ Core.WFFactoryArray := by
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))
  have hmem : (intNegFunc (T := CoreLParams)).func
      ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨intNegFunc (T := CoreLParams), hmem_wf, rfl⟩
  have hnodup : List.Nodup
      ((Core.WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    Core.WFFactoryArray_func_name_nodup
  have hname : (intNegFunc (T := CoreLParams)).func.name.name = "Int.Neg" := by
    native_decide
  have hlk := Lambda.Factory.get?_ofArray_of_mem hmem hnodup
  rw [hname] at hlk
  simpa [Core.Factory, Core.WFFactory, Lambda.WFLFactory.ofArray] using hlk

theorem intNeg_getElem :
    Core.Factory["Int.Neg"]'intNeg_mem = (intNegFunc (T := CoreLParams)).func :=
  Lambda.Factory.getElem?_some_getElem intNeg_lookup

theorem neg_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Int.Neg" intUnSort = fun (p : Int) => -p := by
  refine unIntInterp hIC "Int.Neg" (fun p => -p) intNeg_mem ?_ ?_ ?_ ?_ ?_
  · rw [intNeg_getElem]; rfl
  · rw [intNeg_getElem]; rfl
  · rw [intNeg_getElem]; rfl
  · rw [intNeg_getElem]; rfl
  · intro n
    rw [intNeg_getElem]
    refine ⟨?_, ?_⟩ <;>
      (simp only [intNegFunc, unaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
        LExpr.denoteInt, LExpr.intConst, Option.bind, constInt?,
        Option.isSome_some]; try rfl)

-- ── Int.Lt (comparison → bool, WFFactoryArray index 12) ──
theorem intLt_mem : "Int.Lt" ∈ Core.Factory := by native_decide

theorem intLt_lookup :
    Core.Factory["Int.Lt"]? = some (intLtFunc (T := CoreLParams)).func := by
  have hmem_wf : (intLtFunc (T := CoreLParams)) ∈ Core.WFFactoryArray := by
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))))))))))
  have hmem : (intLtFunc (T := CoreLParams)).func
      ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨intLtFunc (T := CoreLParams), hmem_wf, rfl⟩
  have hnodup : List.Nodup
      ((Core.WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    Core.WFFactoryArray_func_name_nodup
  have hname : (intLtFunc (T := CoreLParams)).func.name.name = "Int.Lt" := by
    native_decide
  have hlk := Lambda.Factory.get?_ofArray_of_mem hmem hnodup
  rw [hname] at hlk
  simpa [Core.Factory, Core.WFFactory, Lambda.WFLFactory.ofArray] using hlk

theorem intLt_getElem :
    Core.Factory["Int.Lt"]'intLt_mem = (intLtFunc (T := CoreLParams)).func :=
  Lambda.Factory.getElem?_some_getElem intLt_lookup

theorem lt_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Int.Lt" intCmpSort = fun (p q : Int) => decide (p < q) := by
  refine binIntCmpInterp hIC "Int.Lt" (fun p q => decide (p < q)) intLt_mem ?_ ?_ ?_ ?_ ?_
  · rw [intLt_getElem]; rfl
  · rw [intLt_getElem]; rfl
  · rw [intLt_getElem]; rfl
  · rw [intLt_getElem]; rfl
  · intro n1 n2
    rw [intLt_getElem]
    refine ⟨?_, ?_⟩ <;>
      simp only [intLtFunc, binaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
        LExpr.denoteInt, LExpr.boolConst, Option.bind, constBool?,
        if_true, Option.isSome_some]

-- ── Int.Le (comparison → bool, WFFactoryArray index 13) ──
theorem intLe_mem : "Int.Le" ∈ Core.Factory := by native_decide

theorem intLe_lookup :
    Core.Factory["Int.Le"]? = some (intLeFunc (T := CoreLParams)).func := by
  have hmem_wf : (intLeFunc (T := CoreLParams)) ∈ Core.WFFactoryArray := by
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))))))))))
  have hmem : (intLeFunc (T := CoreLParams)).func
      ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨intLeFunc (T := CoreLParams), hmem_wf, rfl⟩
  have hnodup : List.Nodup
      ((Core.WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    Core.WFFactoryArray_func_name_nodup
  have hname : (intLeFunc (T := CoreLParams)).func.name.name = "Int.Le" := by
    native_decide
  have hlk := Lambda.Factory.get?_ofArray_of_mem hmem hnodup
  rw [hname] at hlk
  simpa [Core.Factory, Core.WFFactory, Lambda.WFLFactory.ofArray] using hlk

theorem intLe_getElem :
    Core.Factory["Int.Le"]'intLe_mem = (intLeFunc (T := CoreLParams)).func :=
  Lambda.Factory.getElem?_some_getElem intLe_lookup

theorem le_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Int.Le" intCmpSort = fun (p q : Int) => decide (p ≤ q) := by
  refine binIntCmpInterp hIC "Int.Le" (fun p q => decide (p ≤ q)) intLe_mem ?_ ?_ ?_ ?_ ?_
  · rw [intLe_getElem]; rfl
  · rw [intLe_getElem]; rfl
  · rw [intLe_getElem]; rfl
  · rw [intLe_getElem]; rfl
  · intro n1 n2
    rw [intLe_getElem]
    refine ⟨?_, ?_⟩ <;>
      simp only [intLeFunc, binaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
        LExpr.denoteInt, LExpr.boolConst, Option.bind, constBool?,
        if_true, Option.isSome_some]

-- ── Int.Gt (comparison → bool, WFFactoryArray index 14) ──
theorem intGt_mem : "Int.Gt" ∈ Core.Factory := by native_decide

theorem intGt_lookup :
    Core.Factory["Int.Gt"]? = some (intGtFunc (T := CoreLParams)).func := by
  have hmem_wf : (intGtFunc (T := CoreLParams)) ∈ Core.WFFactoryArray := by
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))))))
  have hmem : (intGtFunc (T := CoreLParams)).func
      ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨intGtFunc (T := CoreLParams), hmem_wf, rfl⟩
  have hnodup : List.Nodup
      ((Core.WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    Core.WFFactoryArray_func_name_nodup
  have hname : (intGtFunc (T := CoreLParams)).func.name.name = "Int.Gt" := by
    native_decide
  have hlk := Lambda.Factory.get?_ofArray_of_mem hmem hnodup
  rw [hname] at hlk
  simpa [Core.Factory, Core.WFFactory, Lambda.WFLFactory.ofArray] using hlk

theorem intGt_getElem :
    Core.Factory["Int.Gt"]'intGt_mem = (intGtFunc (T := CoreLParams)).func :=
  Lambda.Factory.getElem?_some_getElem intGt_lookup

theorem gt_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Int.Gt" intCmpSort = fun (p q : Int) => decide (p > q) := by
  refine binIntCmpInterp hIC "Int.Gt" (fun p q => decide (p > q)) intGt_mem ?_ ?_ ?_ ?_ ?_
  · rw [intGt_getElem]; rfl
  · rw [intGt_getElem]; rfl
  · rw [intGt_getElem]; rfl
  · rw [intGt_getElem]; rfl
  · intro n1 n2
    rw [intGt_getElem]
    refine ⟨?_, ?_⟩ <;>
      simp only [intGtFunc, binaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
        LExpr.denoteInt, LExpr.boolConst, Option.bind, constBool?,
        if_true, Option.isSome_some]

-- ── Int.Ge (comparison → bool, WFFactoryArray index 15) ──
theorem intGe_mem : "Int.Ge" ∈ Core.Factory := by native_decide

theorem intGe_lookup :
    Core.Factory["Int.Ge"]? = some (intGeFunc (T := CoreLParams)).func := by
  have hmem_wf : (intGeFunc (T := CoreLParams)) ∈ Core.WFFactoryArray := by
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))))))))))))))
  have hmem : (intGeFunc (T := CoreLParams)).func
      ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨intGeFunc (T := CoreLParams), hmem_wf, rfl⟩
  have hnodup : List.Nodup
      ((Core.WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    Core.WFFactoryArray_func_name_nodup
  have hname : (intGeFunc (T := CoreLParams)).func.name.name = "Int.Ge" := by
    native_decide
  have hlk := Lambda.Factory.get?_ofArray_of_mem hmem hnodup
  rw [hname] at hlk
  simpa [Core.Factory, Core.WFFactory, Lambda.WFLFactory.ofArray] using hlk

theorem intGe_getElem :
    Core.Factory["Int.Ge"]'intGe_mem = (intGeFunc (T := CoreLParams)).func :=
  Lambda.Factory.getElem?_some_getElem intGe_lookup

theorem ge_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    opInterp "Int.Ge" intCmpSort = fun (p q : Int) => decide (p ≥ q) := by
  refine binIntCmpInterp hIC "Int.Ge" (fun p q => decide (p ≥ q)) intGe_mem ?_ ?_ ?_ ?_ ?_
  · rw [intGe_getElem]; rfl
  · rw [intGe_getElem]; rfl
  · rw [intGe_getElem]; rfl
  · rw [intGe_getElem]; rfl
  · intro n1 n2
    rw [intGe_getElem]
    refine ⟨?_, ?_⟩ <;>
      simp only [intGeFunc, binaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
        LExpr.denoteInt, LExpr.boolConst, Option.bind, constBool?,
        if_true, Option.isSome_some]

-- ── Int.Div (GUARDED, WFFactoryArray index 3) ──
theorem intDiv_mem : "Int.Div" ∈ Core.Factory := by native_decide

theorem intDiv_lookup :
    Core.Factory["Int.Div"]? = some (intDivFunc (T := CoreLParams)).func := by
  have hmem_wf : (intDivFunc (T := CoreLParams)) ∈ Core.WFFactoryArray := by
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))
  have hmem : (intDivFunc (T := CoreLParams)).func
      ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨intDivFunc (T := CoreLParams), hmem_wf, rfl⟩
  have hnodup : List.Nodup
      ((Core.WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    Core.WFFactoryArray_func_name_nodup
  have hname : (intDivFunc (T := CoreLParams)).func.name.name = "Int.Div" := by
    native_decide
  have hlk := Lambda.Factory.get?_ofArray_of_mem hmem hnodup
  rw [hname] at hlk
  simpa [Core.Factory, Core.WFFactory, Lambda.WFLFactory.ofArray] using hlk

theorem intDiv_getElem :
    Core.Factory["Int.Div"]'intDiv_mem = (intDivFunc (T := CoreLParams)).func :=
  Lambda.Factory.getElem?_some_getElem intDiv_lookup

theorem div_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    ∀ (p q : Int), q ≠ 0 → opInterp "Int.Div" intBinSort p q = p / q := by
  refine binIntGuardedInterp hIC "Int.Div" (· / ·) intDiv_mem ?_ ?_ ?_ ?_ ?_
  · rw [intDiv_getElem]; rfl
  · rw [intDiv_getElem]; rfl
  · rw [intDiv_getElem]; rfl
  · rw [intDiv_getElem]; rfl
  · intro n1 n2 hn2
    rw [intDiv_getElem]
    refine ⟨?_, ?_⟩ <;>
      simp only [intDivFunc, binaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
        LExpr.denoteInt, LExpr.intConst, Option.bind, constInt?,
        bne_iff_ne, if_pos hn2, Option.isSome_some]

-- ── Int.Mod (GUARDED, WFFactoryArray index 5) ──
theorem intMod_mem : "Int.Mod" ∈ Core.Factory := by native_decide

theorem intMod_lookup :
    Core.Factory["Int.Mod"]? = some (intModFunc (T := CoreLParams)).func := by
  have hmem_wf : (intModFunc (T := CoreLParams)) ∈ Core.WFFactoryArray := by
    rw [Array.mem_def]
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  have hmem : (intModFunc (T := CoreLParams)).func
      ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨intModFunc (T := CoreLParams), hmem_wf, rfl⟩
  have hnodup : List.Nodup
      ((Core.WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    Core.WFFactoryArray_func_name_nodup
  have hname : (intModFunc (T := CoreLParams)).func.name.name = "Int.Mod" := by
    native_decide
  have hlk := Lambda.Factory.get?_ofArray_of_mem hmem hnodup
  rw [hname] at hlk
  simpa [Core.Factory, Core.WFFactory, Lambda.WFLFactory.ofArray] using hlk

theorem intMod_getElem :
    Core.Factory["Int.Mod"]'intMod_mem = (intModFunc (T := CoreLParams)).func :=
  Lambda.Factory.getElem?_some_getElem intMod_lookup

theorem mod_interp
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    [TyConstrInterp.AllInhabited tcInterp]
    (hIC : Lambda.Factory.InterpConsistent tcInterp opInterp Core.Factory) :
    ∀ (p q : Int), q ≠ 0 → opInterp "Int.Mod" intBinSort p q = p % q := by
  refine binIntGuardedInterp hIC "Int.Mod" (· % ·) intMod_mem ?_ ?_ ?_ ?_ ?_
  · rw [intMod_getElem]; rfl
  · rw [intMod_getElem]; rfl
  · rw [intMod_getElem]; rfl
  · rw [intMod_getElem]; rfl
  · intro n1 n2 hn2
    rw [intMod_getElem]
    refine ⟨?_, ?_⟩ <;>
      simp only [intModFunc, binaryOp, LambdaLeanType.cevalTy, LambdaLeanType.mkConst,
        LExpr.denoteInt, LExpr.intConst, Option.bind, constInt?,
        bne_iff_ne, if_pos hn2, Option.isSome_some]

/-- **`Int.Div` field shape**: `opInterp "Int.Div"` equals the conditional-fn `if y = 0 then
    divByZero x else x / y`, where `divByZero` is the model-chosen `opInterp "Int.Div" _ x 0`. The
    `y = 0` branch is reflexivity (the chosen value), the `y ≠ 0` branch is `div_interp`. Stated with
    `fun (x y : Int)` so the `SortDenote` field type unifies definitionally. -/
theorem div_field_interp
    {opInterp : OpInterp simpTcInterp}
    (hIC : Lambda.Factory.InterpConsistent simpTcInterp opInterp Core.Factory) :
    opInterp "Int.Div" intBinSort
      = fun (x y : Int) => if y = 0 then opInterp "Int.Div" intBinSort x (0 : Int) else x / y := by
  funext (x : Int) (y : Int)
  by_cases hy : y = (0 : Int)
  · rw [hy, if_pos rfl]
  · rw [if_neg hy]; exact div_interp hIC x y hy

/-- **`Int.Mod` field shape**, the `%` analog of `div_field_interp`. -/
theorem mod_field_interp
    {opInterp : OpInterp simpTcInterp}
    (hIC : Lambda.Factory.InterpConsistent simpTcInterp opInterp Core.Factory) :
    opInterp "Int.Mod" intBinSort
      = fun (x y : Int) => if y = 0 then opInterp "Int.Mod" intBinSort x (0 : Int) else x % y := by
  funext (x : Int) (y : Int)
  by_cases hy : y = (0 : Int)
  · rw [hy, if_pos rfl]
  · rw [if_neg hy]; exact mod_interp hIC x y hy

end -- meta section

/-! ## §6. Assembling `OpInterpConsistent` for `Core.Factory` -/

/-- **CONNECTOR 1b (for the default factory).** Any model consistent with `Core.Factory` yields the
    `OpInterpConsistent` structure (at `simpTcInterp`, as connector 1b needs). Each BOOL field converts
    its arbitrary `name` (with `CoreOp.ofString name = .bool k`) to the canonical `"Bool.{k}"` via the
    `ofString_bool_*` inverses, then applies the corresponding `*_interp` lemma.

    The non-guarded INTEGER fields (Neg, Add, Sub, Mul, Lt, Le, Gt, Ge) are likewise PROVEN, each via
    `ofString_numeric_int` + the corresponding `*_interp` lemma (which reduces `concreteEval` on
    symbolic args after the reduction-free `int{Op}_getElem` factory identity).

    The GUARDED div/mod fields (Div, Mod) are also PROVEN, now that `OpInterpConsistent` carries
    explicit `divByZero`/`modByZero`: this connector CHOOSES them as `opInterp "Int.{Div,Mod}" _ x 0`
    (the model's own at-zero value), so the conditional-fn fields close via `div_field_interp`/
    `mod_field_interp` (reflexivity at `y = 0`, `binIntGuardedInterp` at `y ≠ 0`). -/
theorem opInterpConsistent_of_coreFactory
    {opInterp : OpInterp simpTcInterp}
    (hIC : Lambda.Factory.InterpConsistent simpTcInterp opInterp Core.Factory) :
    OpInterpConsistent
      (fun x => opInterp "Int.Div" intBinSort x (0 : Int))
      (fun x => opInterp "Int.Mod" intBinSort x (0 : Int))
      opInterp where
  -- ── bool fields (proven) ──
  and_ := fun name h => by
    rw [show name = "Bool.And" from ofString_bool name .And h]; exact and_interp hIC
  or_ := fun name h => by
    rw [show name = "Bool.Or" from ofString_bool name .Or h]; exact or_interp hIC
  not := fun name h => by
    rw [show name = "Bool.Not" from ofString_bool name .Not h]; exact not_interp hIC
  implies := fun name h => by
    rw [show name = "Bool.Implies" from ofString_bool name .Implies h]; exact implies_interp hIC
  equiv := fun name h => by
    rw [show name = "Bool.Equiv" from ofString_bool name .Equiv h]; exact equiv_interp hIC
  -- ── int arithmetic fields (proven) ──
  neg := fun name h => by
    rw [show name = "Int.Neg" from ofString_numeric_int name .Neg h]; exact neg_interp hIC
  add := fun name h => by
    rw [show name = "Int.Add" from ofString_numeric_int name .Add h]; exact add_interp hIC
  sub := fun name h => by
    rw [show name = "Int.Sub" from ofString_numeric_int name .Sub h]; exact sub_interp hIC
  mul := fun name h => by
    rw [show name = "Int.Mul" from ofString_numeric_int name .Mul h]; exact mul_interp hIC
  -- ── GUARDED div/mod fields (PROVEN, via the model-chosen at-zero value) ──
  --  divByZero/modByZero are CHOSEN as `opInterp "Int.{Div,Mod}" _ x 0`, so the `y = 0` branch of
  --  the conditional-fn field is definitional (`rfl`); the `y ≠ 0` branch is the factory's guarded
  --  behaviour, supplied by `div_interp`/`mod_interp` (`binIntGuardedInterp`).
  div := fun name h => by
    rw [show name = "Int.Div" from ofString_numeric_int name .Div h]
    exact div_field_interp hIC
  mod_ := fun name h => by
    rw [show name = "Int.Mod" from ofString_numeric_int name .Mod h]
    exact mod_field_interp hIC
  -- ── int comparisons (proven) ──
  lt := fun name h => by
    rw [show name = "Int.Lt" from ofString_numeric_int name .Lt h]; exact lt_interp hIC
  le := fun name h => by
    rw [show name = "Int.Le" from ofString_numeric_int name .Le h]; exact le_interp hIC
  gt := fun name h => by
    rw [show name = "Int.Gt" from ofString_numeric_int name .Gt h]; exact gt_interp hIC
  ge := fun name h => by
    rw [show name = "Int.Ge" from ofString_numeric_int name .Ge h]; exact ge_interp hIC

end Core.BuiltinConsistent
