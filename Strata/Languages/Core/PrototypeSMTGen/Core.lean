/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
import all Strata.Languages.Core.PrototypeSMTGen.ModelTransfer
import all Strata.DL.SMT.DenoteTyped
import all Strata.Languages.Core.PrototypeSMTGen.Construct
import all Strata.Languages.Core.Statement
import all Strata.Languages.Core.Program
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.Denote.LExprDenoteSubst
import all Strata.DL.Lambda.Denote.CallOfLFuncDenote
-- `import all` exposes `Map.ofList`'s definition body locally, so `funcBvarSubst_eq_map` reduces by
-- `rfl`. `Map.ofList` lacks `@[expose]`, so it is otherwise opaque across module boundaries.
import all Strata.Util.ListMap

open Core Lambda Imperative Std Core.Construct Core.ModelTransfer
open Strata.SMT.DenoteTyped
set_option linter.unusedVariables false

/-!
# Layer 1 of the interpreted-function SMT encoder: preprocessed Core program → `OblProgram`

This file gives the seam from a preprocessed Core `Program` to the per-obligation `OblProgram`s of
the SMT layer, following a prefix-fold design: well-formedness and emission are both left folds over
`Program.decls`, so each procedure sees exactly the declarations before it (declare-before-use).

Design choices:
- **Declaration position matters.** Well-formedness (`Program.WF`) is a prefix fold over
  `Program.decls`, the Core-`Decl`-level analog of `OblProgramWFfrom`; "the collection up to a
  procedure" is the context accumulated at that proc.
- **Factory reconstruction.** Stepping a `.func` pushes it into a reconstructed `Factory` (seeded
  with the default `Core.Factory`), keeping each function's `concreteEval` (which `FnDef` discards),
  so validity reuses Core's `Factory.InterpConsistent` directly on the reconstructed factory.
- **Topological order assumed.** The input `.func` decls arrive callee-before-caller, so `declWF`
  types each `.func` body at the prefix `Ψ`; emission preserves that order by filtering the
  (topological) factory array to the reachable subset.
- **Minimality via reachability.** Only functions transitively referenced by an obligation are
  emitted, at per-assertion granularity: each emitted `OblProgram` carries only the functions its
  obligation (plus its path assumptions and globals) transitively needs.

Key definitions: `Statements.Preprocessed`, `PStep` / `PStepStar` (the small-step semantics),
`CoreCtx` (the prefix-fold context), `Program.WF`, `toOblPrograms` (the emitter), `Program.Valid`.
Key results: `toOblPrograms_wf`, `program_valid_of_oblProgramsValid` (Layer-1 soundness).
-/

namespace Core.Preprocessed

/-! ## SMT-free decidability of `IsPredefinedOp`

`IsPredefinedOp` is an existential `Prop` over `CoreOpHasType`. A recognizer mirroring the
`CoreOpHasType` table decides it computably and SMT-free, keeping decidability on the LExpr/Core
side so the whole emitter stays computable. -/

/-- Computable, SMT-free recognizer for a predefined operator: `true` on exactly the `CoreOp`s that
    head a `CoreOpHasType` constructor. -/
def isPredefinedOpCore : CoreOp → Bool
  | .bool .And | .bool .Or | .bool .Not | .bool .Implies | .bool .Equiv => true
  | .numeric ⟨.int, .Neg⟩ | .numeric ⟨.int, .Add⟩ | .numeric ⟨.int, .Sub⟩
  | .numeric ⟨.int, .Mul⟩ | .numeric ⟨.int, .Div⟩ | .numeric ⟨.int, .Mod⟩
  | .numeric ⟨.int, .Lt⟩ | .numeric ⟨.int, .Le⟩ | .numeric ⟨.int, .Gt⟩
  | .numeric ⟨.int, .Ge⟩ => true
  | _ => false

/-- The recognizer agrees with `IsPredefinedOp`. -/
theorem isPredefinedOpCore_iff {name : String} :
    IsPredefinedOp name ↔ isPredefinedOpCore (CoreOp.ofString name) = true := by
  rw [IsPredefinedOp]
  generalize CoreOp.ofString name = op
  constructor
  · rintro ⟨acc, rty, hcot⟩; cases hcot <;> rfl
  · intro h
    cases op with
    | numeric nop =>
      obtain ⟨ty, kind⟩ := nop
      cases ty <;> cases kind <;>
        first
          | exact ⟨_, _, by constructor⟩
          | simp [isPredefinedOpCore] at h
    | bool kind => cases kind <;>
        first
          | exact ⟨_, _, by constructor⟩
          | simp [isPredefinedOpCore] at h
    | _ => simp [isPredefinedOpCore] at h

instance (name : String) : Decidable (IsPredefinedOp name) :=
  decidable_of_iff _ isPredefinedOpCore_iff.symm


/-! ## Function-signature and formals-context helpers -/

/-- The `FnCtx` signature contributed by a function: its name paired with the arrow type
    `a₁ → ⋯ → aₙ → out` (the shape `FnDef.sig` / `HasSimpType`'s `.fnOp` head consume). -/
def funcSig (f : LFunc CoreLParams) : String × LMonoTy :=
  (f.name.name, List.foldr LMonoTy.arrow f.output (f.inputs.toList.map Prod.snd))

/-- A `map`-nodup list has injective `f` on its members: two members with equal `f`-image are
    equal. General list utility used to invert `fnCtx`/`factoryNames` membership. -/
theorem map_nodup_inj {α β} (f : α → β) : ∀ (l : List α), (l.map f).Nodup →
    ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons hd tl ih =>
    intro hnd a ha b hb hfab
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hhead, htl⟩ := hnd
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd (hfab ▸ List.mem_map_of_mem (f := f) hb') hhead
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd (hfab.symm ▸ List.mem_map_of_mem (f := f) ha') hhead
      · exact ih htl a ha' b hb' hfab

/-- The function context `Ψ` read off a Factory `F`: one `funcSig` per factory function, in the
    factory's array (declaration/topological) order. Name-nodup is free from `Factory.name_nodup`,
    so `Ψ` needs no separate well-formedness assumption. -/
def Lambda.Factory.fnCtx (F : Lambda.Factory CoreLParams) : FnCtx :=
  F.toArray.toList.map funcSig

/-- A function's formals as a free-variable context: input names paired with their types. At the
    source (`LFunc`) level a body references its formals as free variables; the fvar→bvar lift to
    `FnDef` is connector 1a. So a body type-checks in this `Φ`, bvar context `[]`. -/
def funcFVarCtx (f : LFunc CoreLParams) : FVarCtx :=
  f.inputs.toList.map (fun (id, ty) => (id.name, ty))

/-! ## The preprocessed body relation (`Statements.Preprocessed`)

The `init` rules grow `Φ` with the declared program variable; a proc body's obligations are the
`assert`s reached under it. The fvar→bvar lift is a function-definition concern, handled in the
emitter. -/

/-- **A preprocessed Core body**, context-indexed by the fixed function context `Ψ` and the
    growing free-variable context `Φ`. Merges admissible shape and declare-before-use typing. -/
inductive Statements.Preprocessed (Ψ : FnCtx) : FVarCtx → Statements → Prop where
  /-- Empty body. -/
  | nil (Φ : FVarCtx) : Statements.Preprocessed Ψ Φ []
  /-- A path assumption (bool-typed); `Φ` unchanged for the rest. -/
  | assume (Φ : FVarCtx) (l : String) (b : Expression.Expr) (md : MetaData Expression)
           (rest : Statements)
           (hb : LExpr.HasSimpType Φ Ψ [] b (.tcons "bool" []))
           (hrest : Statements.Preprocessed Ψ Φ rest) :
           Statements.Preprocessed Ψ Φ (Statement.assume l b md :: rest)
  /-- A proof obligation (bool-typed); `Φ` unchanged for the rest. -/
  | assert (Φ : FVarCtx) (l : String) (b : Expression.Expr) (md : MetaData Expression)
           (rest : Statements)
           (hb : LExpr.HasSimpType Φ Ψ [] b (.tcons "bool" []))
           (hrest : Statements.Preprocessed Ψ Φ rest) :
           Statements.Preprocessed Ψ Φ (Statement.assert l b md :: rest)
  /-- A deterministic binding (`.det e`) → a `varDef`: the defining expression `e` type-checks at
      the declared (mono) type `mτ` in the current `Φ` (no self-reference), and the rest continues
      with `(name, mτ)` added to `Φ`. -/
  | initDet (Φ : FVarCtx) (name : Expression.Ident) (ty : Expression.Ty) (mτ : LMonoTy)
            (e : Expression.Expr) (md : MetaData Expression) (rest : Statements)
            (hmono : ty.toMonoType? = some mτ)
            (he : LExpr.HasSimpType Φ Ψ [] e mτ)
            -- Freshness (declare-before-use / distinct names): the introduced program variable is
            -- fresh against the free-vars so far, the function names, and the reserved `$__bv{n}`
            -- namespace — exactly what the emitted `.varDef`'s `cmdWF` requires. (Established by
            -- Layer 0, which α-renames `init` variables to globally-fresh names.)
            (hfreshΦ : name.name ∉ Φ.map (·.1))
            (hfreshΨ : name.name ∉ Ψ.map (·.1))
            (hnres : ∀ n : Nat, name.name ≠ s!"$__bv{n}")
            (hrest : Statements.Preprocessed Ψ (Φ ++ [(name.name, mτ)]) rest) :
            Statements.Preprocessed Ψ Φ (Statement.init name ty (.det e) md :: rest)
  /-- A non-deterministic binding (havoc, `.nondet`) → an `fvarDecl`: the declared (mono) type is
      SMT-encodable (`MonoTyIsSimp`), and the rest continues with `(name, mτ)` added to `Φ`. -/
  | initNondet (Φ : FVarCtx) (name : Expression.Ident) (ty : Expression.Ty) (mτ : LMonoTy)
               (md : MetaData Expression) (rest : Statements)
               (hmono : ty.toMonoType? = some mτ)
               (hsimp : LExpr.MonoTyIsSimp mτ)
               (hfreshΦ : name.name ∉ Φ.map (·.1))
               (hfreshΨ : name.name ∉ Ψ.map (·.1))
               (hnres : ∀ n : Nat, name.name ≠ s!"$__bv{n}")
               (hrest : Statements.Preprocessed Ψ (Φ ++ [(name.name, mτ)]) rest) :
               Statements.Preprocessed Ψ Φ (Statement.init name ty .nondet md :: rest)
  /-- Non-deterministic branching: both branches are preprocessed at the current `Φ`; the
      continuation `rest` resumes at the (unextended) pre-branch `Φ`. -/
  | ite (Φ : FVarCtx) (thenb elseb : Statements) (md : MetaData Expression) (rest : Statements)
        (hthen : Statements.Preprocessed Ψ Φ thenb)
        (helse : Statements.Preprocessed Ψ Φ elseb)
        (hrest : Statements.Preprocessed Ψ Φ rest) :
        Statements.Preprocessed Ψ Φ (Stmt.ite .nondet thenb elseb md :: rest)

/-! ## Expression/function references and the factory node set -/


/-- **The non-predefined function symbols applied in `e`** (structural scan; stays out of function
    bodies). A head `.op o _` contributes `o.name` when `¬IsPredefinedOp o.name` — i.e. it is a
    user/factory function resolved through `Ψ` rather than a built-in SMT operator (which types via
    `CoreOpHasType`). The `¬IsPredefinedOp` filter is essential: a built-in-operator function is a
    default member of `F`, so collecting its name would make the closure wrongly emit it as a
    `.fnOp` function rather than leave it a native SMT op. Computable via the SMT-free
    `Decidable (IsPredefinedOp …)` instance above. -/
def exprFnRefs : Expression.Expr → List String
  | .op _ o _        => if IsPredefinedOp o.name then [] else [o.name]
  | .app _ fn e      => exprFnRefs fn ++ exprFnRefs e
  | .ite _ c t e     => exprFnRefs c ++ exprFnRefs t ++ exprFnRefs e
  | .eq _ e1 e2      => exprFnRefs e1 ++ exprFnRefs e2
  | .abs _ _ _ e     => exprFnRefs e
  | .quant _ _ _ _ tr e => exprFnRefs tr ++ exprFnRefs e
  | .const _ _       => []
  | .bvar _ _        => []
  | .fvar _ _ _      => []

/-- The function references a factory function `f` makes: the non-predefined applied heads in its
    body (if any) and in each of its axioms. The per-function transitive step of the closure —
    scanning bodies and axioms, since an axiom referencing a function must keep that function
    declared. -/
def funcFnRefs (f : LFunc CoreLParams) : List String :=
  (f.body.map exprFnRefs |>.getD []) ++ f.axioms.flatMap exprFnRefs

mutual
/-- **A well-typed expression's function references are all declared in `Ψ`.** Every non-predefined
    applied head `n ∈ exprFnRefs e` of a `HasSimpType Φ Ψ Δ e τ`-typed `e` has some `(n, σ) ∈ Ψ`.
    `HasSimpType`/`AppSpine` consult `Ψ` positively only at `AppSpine.fnOp` — exactly the head that
    `exprFnRefs` collects (`¬IsPredefinedOp o.name`) — so every collected ref is a witnessed `Ψ`
    membership. This is the semantic half of the topological argument: it turns `g`'s prefix-precise
    body typing (bodies type against the factory-array prefix `Ψ`) into "each callee sits earlier in
    the array". Mutual structural recursion over the derivation. -/
theorem HasSimpType_fnRefs_mem {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {τ : LMonoTy} (he : LExpr.HasSimpType Φ Ψ Δ e τ) :
    ∀ n ∈ exprFnRefs e, ∃ σ, (n, σ) ∈ Ψ := by
  match he with
  | .const c _ => intro n hn; simp only [exprFnRefs, List.not_mem_nil] at hn
  | .bvar i t _ _ => intro n hn; simp only [exprFnRefs, List.not_mem_nil] at hn
  | .app fn arg rty hspine => exact AppSpine_fnRefs_mem hspine
  | .fvarNullary f t rty hspine => exact AppSpine_fnRefs_mem hspine
  | .ite c t t' d hc ht he_ =>
    intro n hn
    simp only [exprFnRefs, List.mem_append] at hn
    rcases hn with (h | h) | h
    · exact HasSimpType_fnRefs_mem hc n h
    · exact HasSimpType_fnRefs_mem ht n h
    · exact HasSimpType_fnRefs_mem he_ n h
  | .eq e1 e2 t _ he1 he2 =>
    intro n hn
    simp only [exprFnRefs, List.mem_append] at hn
    rcases hn with h | h
    · exact HasSimpType_fnRefs_mem he1 n h
    · exact HasSimpType_fnRefs_mem he2 n h
  | .quant qty qbody qk qname qtr qτtr _ htr hbody =>
    intro n hn
    -- `exprFnRefs (.quant … tr body) = exprFnRefs tr ++ exprFnRefs body`; refs from either side
    simp only [exprFnRefs, List.mem_append] at hn
    rcases hn with h | h
    · exact HasSimpType_fnRefs_mem htr n h
    · exact HasSimpType_fnRefs_mem hbody n h

theorem AppSpine_fnRefs_mem {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {acc : List LMonoTy} {rty : LMonoTy} (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    ∀ n ∈ exprFnRefs e, ∃ σ, (n, σ) ∈ Ψ := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    intro n hn
    simp only [exprFnRefs, List.mem_append] at hn
    rcases hn with h | h
    · exact AppSpine_fnRefs_mem hrest n h
    · exact HasSimpType_fnRefs_mem harg n h
  | .fvar f t acc' rty _ _ _ => intro n hn; simp only [exprFnRefs, List.not_mem_nil] at hn
  | .op o oty acc' rty hop hcollect =>
    -- predefined head ⇒ `IsPredefinedOp o.name` ⇒ `exprFnRefs = []`
    intro n hn
    have hpre : IsPredefinedOp o.name := ⟨acc', rty, hop⟩
    simp only [exprFnRefs, hpre, if_true, List.not_mem_nil] at hn
  | .fnOp o oty acc' rty hmem hnpre hcollect hbase =>
    -- non-predefined head ⇒ `exprFnRefs = [o.name]`; witness `σ = oty`
    intro n hn
    simp only [exprFnRefs, hnpre, if_false, List.mem_singleton] at hn
    exact ⟨oty, hn ▸ hmem⟩
termination_by structural hspine
end

/-- All factory-function names in `F` — the finite universe the reachability closure lives in.
    `Nodup` by `Factory.name_nodup`; membership decides the termination measure below. -/
def factoryNames (F : Lambda.Factory CoreLParams) : List String :=
  F.toArray.toList.map (·.name.name)

/-! ## Reachability: `funcDeps` and worklist closure

Minimality of the emitted function set: only functions transitively referenced by an obligation are
collected. -/

/-- Reachability edges: the emittable callees `g`'s body/axioms reference (`funcFnRefs`), kept only
    if they are themselves factory functions. Decides which functions to emit (`reachableFuncs`);
    cycles allowed. `g ∉ F` (an fvar) has no callees. -/
def funcDeps (F : Lambda.Factory CoreLParams) (g : String) : List String :=
  match F[g]? with
  | some f => (funcFnRefs f).filter (· ∈ factoryNames F)
  | none   => []

/-- A factory-node name resolves: `g ∈ factoryNames F ⇒ F[g]?` is `some`. (`factoryNames` are
    exactly the `nameMap` keys, on which `get?` succeeds.) -/
theorem factoryNames_getElem?_isSome (F : Lambda.Factory CoreLParams) {g : String}
    (hnode : g ∈ factoryNames F) : (F[g]?).isSome := by
  have hmemF : g ∈ F := by
    rw [Factory.mem_iff_mem_names]
    have hg : g ∈ F.toArray.toList.map (·.name.name) := hnode
    simp only [List.mem_map] at hg
    obtain ⟨e, hemem, hename⟩ := hg
    exact Array.mem_map.mpr ⟨e, Array.mem_def.mpr hemem, hename⟩
  change (Factory.get? F g).isSome
  unfold Factory.get?
  split
  · rename_i hnone
    -- `nameMap[g]? = none` contradicts `g ∈ F` (= `g ∈ nameMap`)
    exfalso
    have hcontains : g ∈ F.nameMap := hmemF
    rw [Std.HashMap.mem_iff_contains, Std.HashMap.contains_eq_isSome_getElem?, hnone] at hcontains
    simp at hcontains
  · rfl

/-- **`fnCtx` membership resolves.** An entry `(n, σ) ∈ fnCtx F` comes from a factory function `f`
    with `F[n]? = some f` and `funcSig f = (n, σ)` — and `n` is a factory node. The inverse of
    `fnCtx = toArray.map funcSig`: recovers the resolving function (using name-nodup to pin `F[n]?`
    to the very element `funcSig` came from). Bridges proc-`Ψ` membership to a resolved function. -/
theorem mem_fnCtx_resolves (F : Lambda.Factory CoreLParams) {n : String} {σ : LMonoTy}
    (hmem : (n, σ) ∈ Lambda.Factory.fnCtx F) :
    ∃ f, F[n]? = some f ∧ funcSig f = (n, σ) ∧ n ∈ factoryNames F := by
  -- `(n,σ) ∈ toArray.map funcSig` ⇒ some `f ∈ toArray` with `funcSig f = (n,σ)`
  simp only [Lambda.Factory.fnCtx, List.mem_map] at hmem
  obtain ⟨f, hfmem, hfsig⟩ := hmem
  -- `funcSig f = (n,σ)` ⇒ `f.name.name = n`
  have hfname : f.name.name = n := by rw [funcSig] at hfsig; exact (Prod.mk.injEq .. ▸ hfsig).1
  have hnode : n ∈ factoryNames F := by
    simp only [factoryNames, List.mem_map]; exact ⟨f, hfmem, hfname⟩
  -- resolution: `F[n]?` is some `f'` with `f'.name.name = n = f.name.name`; nodup ⇒ `f' = f`
  obtain ⟨f', hf'⟩ := Option.isSome_iff_exists.mp (factoryNames_getElem?_isSome F hnode)
  have hf'mem : f' ∈ F.toArray := Factory.getElem?_is_some_implies_mem hf'
  have hf'name : f'.name.name = n := Factory.getElem?_name hf'
  have hff' : f' = f :=
    map_nodup_inj (·.name.name) F.toArray.toList (Factory.name_nodup F)
      f' (Array.mem_def.mp hf'mem) f hfmem (by simp only []; rw [hf'name, hfname])
  rw [hff'] at hf'
  exact ⟨f, hf', hfsig, hnode⟩

/-- `countP` strictly drops when an element satisfying `q` but not `p` (with `p ≤ q` pointwise) is
    present. Used to show the closure's `unseen`-count decreases. -/
theorem countP_lt_of_mem {α} {l : List α} {p q : α → Bool} {a : α}
    (hpq : ∀ x, p x → q x) (ha : a ∈ l) (hpa : p a = false) (hqa : q a = true) :
    l.countP p < l.countP q := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  -- `filter p l = filter p (filter q l)` (since `p ≤ q`), a sublist of `filter q l`
  have hsl : (l.filter p).Sublist (l.filter q) := by
    have hpp : l.filter p = (l.filter q).filter p := by
      rw [List.filter_filter]
      exact List.filter_congr (fun a _ => by cases hpa' : p a <;> simp [hpa', hpq a])
    rw [hpp]; exact List.filter_sublist
  refine Nat.lt_of_le_of_ne (List.Sublist.length_le hsl) (fun heq => ?_)
  have hmemq : a ∈ l.filter q := List.mem_filter.mpr ⟨ha, hqa⟩
  rw [← List.Sublist.eq_of_length hsl heq, List.mem_filter] at hmemq
  exact absurd hmemq.2 (by simp [hpa])

/-- Worker: process `worklist`, accumulating discovered factory-function names in `seen`. -/
def reachableFuncsGo (F : Lambda.Factory CoreLParams) :
    (seen : List String) → (worklist : List String) → List String
  | seen, [] => seen
  | seen, g :: rest =>
    if hg : g ∈ seen then
      reachableFuncsGo F seen rest
    else
      match hf : F[g]? with
      | none   => reachableFuncsGo F seen rest      -- unreachable for our restricted preprocessed program
      | some f =>
        -- Prepend only the not-yet-seen refs (filter against `g :: seen`, the set the recursive
        -- call carries): already-seen names had their own refs scheduled when they were added, so
        -- dropping them here loses no reachability but keeps the worklist small. Termination-neutral
        -- — this branch decreases the primary measure (`unseen`-count, via `Prod.Lex.left`), which
        -- ignores `worklist.length`, so the worklist may be filtered/reordered freely. The perf win
        -- scales with `seen`'s membership cost (O(1) once `seen` is a `HashSet`).
        reachableFuncsGo F (g :: seen) ((funcFnRefs f).filter (· ∉ g :: seen) ++ rest)
  termination_by seen worklist => ((factoryNames F).countP (· ∉ seen), worklist.length)
  decreasing_by
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)
    · -- productive step: `g` is an unseen factory function ⇒ `countP (∉ seen)` strictly drops
      refine Prod.Lex.left _ _ ?_
      have hmem : g ∈ factoryNames F := by
        simp only [factoryNames, List.mem_map]
        exact ⟨f, Array.mem_def.mp (Factory.getElem?_is_some_implies_mem hf),
               Factory.getElem?_name hf⟩
      exact countP_lt_of_mem
        (p := fun x => decide (x ∉ g :: seen)) (q := fun x => decide (x ∉ seen)) (a := g)
        (fun x hx => by
          simp only [decide_eq_true_eq] at hx ⊢
          exact fun h => hx (List.mem_cons_of_mem g h))
        hmem
        (by simp)
        (by simpa using hg)

/-- The set of factory-function names transitively reachable from `seeds` (the obligation-relevant
    function references). Runs the fuel-free worklist from an empty `seen`. -/
def reachableFuncs (F : Lambda.Factory CoreLParams) (seeds : List String) : List String :=
  reachableFuncsGo F [] seeds

/-- **The accumulator only grows**: every already-seen name survives to the output. Well-founded
    induction along `reachableFuncsGo`'s own recursion (`.induct`). -/
theorem reachableFuncsGo_seen_subset (F : Lambda.Factory CoreLParams) :
    ∀ (seen wl : List String), ∀ x ∈ seen, x ∈ reachableFuncsGo F seen wl := by
  intro seen wl
  induction seen, wl using reachableFuncsGo.induct F with
  | case1 seen => intro x hx; rw [reachableFuncsGo]; exact hx
  | case2 seen g rest hg ih =>
      intro x hx; rw [reachableFuncsGo]; simp only [hg, dif_pos]; exact ih x hx
  | case3 seen g rest hg hf ih =>
      intro x hx; rw [reachableFuncsGo]
      simp only [hg, dif_neg, not_false_iff]
      rw [hf]; exact ih x hx
  | case4 seen g rest hg f hf ih =>
      intro x hx; rw [reachableFuncsGo]
      simp only [hg, dif_neg, not_false_iff]
      rw [hf]
      -- recursive call carries `g :: seen`; `x ∈ seen ⊆ g :: seen`
      exact ih x (List.mem_cons_of_mem g hx)

/-- **A worklist element that is a factory node is reached**: any `g ∈ wl` with `g ∈ factoryNames F`
    lands in the output. The seed-inclusion half of the reachability closure — feeds connector-1c's
    "referenced ⊆ collected". -/
theorem mem_reachableFuncsGo_of_mem_wl (F : Lambda.Factory CoreLParams) :
    ∀ (seen wl : List String), ∀ g ∈ wl, g ∈ factoryNames F → g ∈ reachableFuncsGo F seen wl := by
  intro seen wl
  induction seen, wl using reachableFuncsGo.induct F with
  | case1 seen => intro g hg _; simp at hg
  | case2 seen g' rest hg' ih =>
      intro g hg hnode
      rw [reachableFuncsGo]; simp only [hg', dif_pos]
      rcases List.mem_cons.mp hg with h | h
      · -- `g = g'`, already seen ⇒ survives
        subst h; exact reachableFuncsGo_seen_subset F seen rest g hg'
      · exact ih g h hnode
  | case3 seen g' rest hg' hf ih =>
      intro g hg hnode
      rw [reachableFuncsGo]; simp only [hg', dif_neg, not_false_iff]; rw [hf]
      rcases List.mem_cons.mp hg with h | h
      · -- `g = g'` but `F[g']? = none` contradicts `g'` being a node
        subst h
        exfalso
        have := factoryNames_getElem?_isSome F hnode
        rw [hf] at this; simp at this
      · exact ih g h hnode
  | case4 seen g' rest hg' f hf ih =>
      intro g hg hnode
      rw [reachableFuncsGo]; simp only [hg', dif_neg, not_false_iff]; rw [hf]
      rcases List.mem_cons.mp hg with h | h
      · -- `g = g'` is added to `seen` ⇒ survives
        subst h
        exact reachableFuncsGo_seen_subset F (g :: seen) _ g (List.mem_cons_self)
      · -- `g` still in `rest` ⊆ new worklist
        apply ih g _ hnode
        exact List.mem_append_right _ h

/-- Every `funcDeps` edge lands on a factory node (`funcDeps F g ⊆ factoryNames F`). -/
theorem funcDeps_subset (F : Lambda.Factory CoreLParams) (g : String) :
    ∀ h ∈ funcDeps F g, h ∈ factoryNames F := by
  intro h hh
  unfold funcDeps at hh
  split at hh
  · exact of_decide_eq_true (List.mem_filter.mp hh).2
  · exact absurd hh (by simp)

/-- **The worklist output is `funcDeps`-closed**, provided every already-`seen` name has its
    `funcDeps` scheduled (in `seen` or the worklist) — the loop invariant `I`. On processing a node
    `g`, its `funcDeps` are prepended to the worklist, so `I` is preserved; at the end (`wl = []`)
    `I` forces every seen node's deps to be seen, i.e. the result is closed. Concretely: for a node
    `g` in the output whose deps `funcDeps F g` we query, each dep is also in the output. -/
theorem reachableFuncsGo_closed (F : Lambda.Factory CoreLParams) :
    ∀ (seen wl : List String),
      (∀ x ∈ seen, ∀ y ∈ funcDeps F x, y ∈ seen ∨ y ∈ wl) →
      ∀ g ∈ reachableFuncsGo F seen wl, ∀ h ∈ funcDeps F g,
        h ∈ reachableFuncsGo F seen wl := by
  intro seen wl
  induction seen, wl using reachableFuncsGo.induct F with
  | case1 seen =>
      -- `wl = []`: `I` says seen's deps are in seen (∨ []); output = seen
      intro hI g hg h hh
      rw [reachableFuncsGo] at hg ⊢
      rcases hI g hg h hh with h' | h'
      · exact h'
      · simp at h'
  | case2 seen g' rest hg' ih =>
      -- `g' ∈ seen` already: worklist drops `g'`, `I` transfers (g''s deps were in seen ∨ g'::rest,
      -- and `g' ∈ seen` so any `∈ [g']` dep is in seen)
      intro hI g hg h hh
      rw [reachableFuncsGo] at hg ⊢; simp only [hg', dif_pos] at hg ⊢
      refine ih ?_ g hg h hh
      intro x hx y hy
      rcases hI x hx y hy with h' | h'
      · exact Or.inl h'
      · rcases List.mem_cons.mp h' with rfl | h''
        · exact Or.inl hg'
        · exact Or.inr h''
  | case3 seen g' rest hg' hf ih =>
      -- `F[g']? = none`: `g'` not a node, its `funcDeps = []`; worklist drops it, `I` transfers
      intro hI g hg h hh
      rw [reachableFuncsGo] at hg ⊢; simp only [hg', dif_neg, not_false_iff] at hg ⊢
      rw [hf] at hg ⊢
      refine ih ?_ g hg h hh
      intro x hx y hy
      rcases hI x hx y hy with h' | h'
      · exact Or.inl h'
      · rcases List.mem_cons.mp h' with heq | h''
        · -- `y = g'`, but `y ∈ funcDeps F x` ⇒ `y` is a node; yet `F[g']? = none` — so `y ≠ g'`.
          exfalso
          have := factoryNames_getElem?_isSome F (funcDeps_subset F x y hy)
          rw [heq, hf] at this; simp at this
        · exact Or.inr h''
  | case4 seen g' rest hg' f hf ih =>
      -- `g'` processed: added to seen, its (not-yet-seen) refs prepended. `I` preserved.
      intro hI g hg h hh
      rw [reachableFuncsGo] at hg ⊢; simp only [hg', dif_neg, not_false_iff] at hg ⊢
      rw [hf] at hg ⊢
      refine ih ?_ g hg h hh
      intro x hx y hy
      rcases List.mem_cons.mp hx with hxg | hxseen
      · -- `x = g'`: its deps `funcDeps F g' = (funcFnRefs f).filter (∈ nodes)`; prepended (filtered
        -- against `g'::seen`), so `y ∈ new-wl` unless already in `g'::seen`
        by_cases hyseen : y ∈ g' :: seen
        · rcases List.mem_cons.mp hyseen with hyg | h'
          · exact Or.inl (hyg ▸ List.mem_cons_self)
          · exact Or.inl (List.mem_cons_of_mem g' h')
        · refine Or.inr (List.mem_append_left _ ?_)
          -- `y ∈ funcDeps F x = funcDeps F g' = (funcFnRefs f).filter (∈ nodes)`; and `y ∉ g'::seen`
          rw [hxg, funcDeps, hf] at hy
          exact List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simpa using hyseen⟩
      · -- `x ∈ seen`: `I` gives `y ∈ seen ∨ y ∈ g'::rest`; relocate into `g'::seen` or new-wl
        rcases hI x hxseen y hy with h' | h'
        · exact Or.inl (List.mem_cons_of_mem g' h')
        · rcases List.mem_cons.mp h' with rfl | h''
          · exact Or.inl (List.mem_cons_self)
          · exact Or.inr (List.mem_append_right _ h'')

/-- **Seeds that are factory nodes are reached** (the `reachableFuncs` corollary). -/
theorem mem_reachableFuncs_of_seed (F : Lambda.Factory CoreLParams) (seeds : List String)
    {g : String} (hg : g ∈ seeds) (hnode : g ∈ factoryNames F) :
    g ∈ reachableFuncs F seeds :=
  mem_reachableFuncsGo_of_mem_wl F [] seeds g hg hnode

/-- **`reachableFuncs` is `funcDeps`-closed** (the corollary from the empty-`seen` base, whose loop
    invariant `I` holds vacuously). A reached node's `funcDeps` are all reached. -/
theorem reachableFuncs_closed (F : Lambda.Factory CoreLParams) (seeds : List String)
    {g : String} (hg : g ∈ reachableFuncs F seeds) {h : String} (hh : h ∈ funcDeps F g) :
    h ∈ reachableFuncs F seeds :=
  reachableFuncsGo_closed F [] seeds (fun x hx => absurd hx (by simp)) g hg h hh

/-- **`reachableFuncsGo` minimality**: the output is contained in any set `S` that already contains
    `seen`, contains every worklist node, and is `funcDeps`-closed. (Processing a node adds only its
    `funcDeps`, which `S` absorbs by closure; non-node worklist elements are dropped by the loop, so
    the node-scoped worklist premise suffices.) The upper-bound dual of the closure lemma. -/
theorem reachableFuncsGo_subset (F : Lambda.Factory CoreLParams) (S : List String)
    (hSclosed : ∀ x ∈ S, ∀ y ∈ funcDeps F x, y ∈ S) :
    ∀ (seen wl : List String), (∀ x ∈ seen, x ∈ S) →
      (∀ x ∈ wl, x ∈ factoryNames F → x ∈ S) →
      ∀ g ∈ reachableFuncsGo F seen wl, g ∈ S := by
  intro seen wl
  induction seen, wl using reachableFuncsGo.induct F with
  | case1 seen => intro hseen _ g hg; rw [reachableFuncsGo] at hg; exact hseen g hg
  | case2 seen g' rest hg' ih =>
      intro hseen hwl g hg
      rw [reachableFuncsGo] at hg; simp only [hg', dif_pos] at hg
      exact ih hseen (fun x hx => hwl x (List.mem_cons_of_mem g' hx)) g hg
  | case3 seen g' rest hg' hf ih =>
      intro hseen hwl g hg
      rw [reachableFuncsGo] at hg; simp only [hg', dif_neg, not_false_iff] at hg; rw [hf] at hg
      exact ih hseen (fun x hx => hwl x (List.mem_cons_of_mem g' hx)) g hg
  | case4 seen g' rest hg' f hf ih =>
      intro hseen hwl g hg
      rw [reachableFuncsGo] at hg; simp only [hg', dif_neg, not_false_iff] at hg; rw [hf] at hg
      -- `g'` resolves ⇒ it is a node; worklist head ⇒ `∈ S`.
      have hg'node : g' ∈ factoryNames F := by
        simp only [factoryNames, List.mem_map]
        exact ⟨f, Array.mem_def.mp (Factory.getElem?_is_some_implies_mem hf),
          Factory.getElem?_name hf⟩
      have hg'S : g' ∈ S := hwl g' List.mem_cons_self hg'node
      refine ih ?_ ?_ g hg
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hg'S
        · exact hseen x hx'
      · intro x hx hxnode
        rcases List.mem_append.mp hx with hxref | hxrest
        · -- filtered node-ref of `g'` ⇒ `x ∈ funcDeps F g'` ⇒ `x ∈ S` by closure
          have hxdep : x ∈ funcDeps F g' := by
            unfold funcDeps; rw [hf]
            exact List.mem_filter.mpr ⟨(List.mem_filter.mp hxref).1, decide_eq_true hxnode⟩
          exact hSclosed g' hg'S x hxdep
        · exact hwl x (List.mem_cons_of_mem g' hxrest) hxnode

/-- **`reachableFuncs` is monotone in seeds**: more seeds reach at least as much. Corollary of
    minimality at `S = reachableFuncs F seeds'` (which is `funcDeps`-closed and contains `seeds'`);
    a seed that is a node is reached in the larger set, non-node seeds are vacuous. -/
theorem reachableFuncs_mono (F : Lambda.Factory CoreLParams) {seeds seeds' : List String}
    (hsub : ∀ x ∈ seeds, x ∈ seeds') :
    ∀ g ∈ reachableFuncs F seeds, g ∈ reachableFuncs F seeds' :=
  reachableFuncsGo_subset F (reachableFuncs F seeds')
    (fun x hx y hy => reachableFuncs_closed F seeds' hx hy) [] seeds (by simp)
    (fun x hx hxnode => mem_reachableFuncs_of_seed F seeds' (hsub x hx) hxnode)

/-! ## Model denotation, small-step semantics, and failed-monotonicity -/

/-- **The closed bool expression `e` denotes to `b` under `(opInterp, fvarVal)`** (empty bvar
    context). Context-free (no `Φ`/`Ψ` — `simpDenote` does not consult them); existential over the
    typing derivation; functional in `b` by `proof_irrel` on the `Prop`-valued `HasTypeA`. -/
def Denotes (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (e : Expression.Expr) (b : Bool) : Prop :=
  ∃ (h : LExpr.HasTypeA [] e (.tcons "bool" [])),
    (simpDenote opInterp fvarVal .nil e (.tcons "bool" []) h : Bool) = b

/-- **`Denotes` is functional in the value.** `simpDenote` depends on its `HasTypeA` argument only up
    to `proof_irrel` (it is `Prop`-valued), so a closed bool expression cannot denote both `true` and
    `false`. The bridge that turns `OblProgram.Valid`'s `⟦obligation⟧ = true` against the
    `assertFail`'s `Denotes b false` into a contradiction. -/
theorem Denotes.functional {opInterp fvarVal} {e : Expression.Expr} {b b' : Bool}
    (h : Denotes opInterp fvarVal e b) (h' : Denotes opInterp fvarVal e b') : b = b' := by
  obtain ⟨ht, hb⟩ := h
  obtain ⟨ht', hb'⟩ := h'
  rw [← hb, ← hb']

/-- **`Denotes e true` gives the `simpDenote` value at any typing witness.** Proof-irrelevance on the
    `HasTypeA` argument lets a `Denotes` fact be reused at the specific witness a satisfaction
    predicate (`LambdaModelSatisfiesAsms`) supplies. -/
theorem Denotes.simpDenote_eq {opInterp fvarVal} {e : Expression.Expr}
    (h : Denotes opInterp fvarVal e true)
    (ht : LExpr.HasTypeA [] e (.tcons "bool" [])) :
    (simpDenote opInterp fvarVal .nil e (.tcons "bool" []) ht : Bool) = true := by
  obtain ⟨ht', hb⟩ := h
  rwa [proof_irrel ht ht']

/-! ## The small-step semantics (a `failed`-flag reachability over a fixed model)

The Layer-1 analog of the operational `hasFailure` flag, specialized to the preprocessed body and a
fixed Lambda model `M`. A configuration is just the remaining work (a `Statements` continuation)
plus a cumulative `failed : Bool` — no store, no `Φ`, no `Ψ` (`Φ` only certified typing, which is
discharged; expression meaning is `Denotes`/`simpDenote` under `M`). Bodies are loop-free trees, so
the reachable set from the initial config is finite.

`PStep M` transitions (path-local):
- `assume b` — steps only when `b` denotes `true` under `M`; a `false` assume has no successor (the
  path is pruned). So "reachable" means "the assumptions along the path held", giving conditional
  validity (assumptions ⟹ obligation) for free.
- `assert b` — `true` continues unchanged; `false` continues with `failed := true` (the only writer
  of the flag). Validity is then "no reachable config has `failed`".
- `cover b` — a no-op continuation: `cover`'s existential obligation is a different notion from the
  ∀-reachable-¬failed safety here, so it does not touch `failed`; handled separately.
- `init x := e` (`.det`) — steps only when the model pins `x` to `⟦e⟧`, i.e. exactly
  `VarDef.Consistent M ⟨x, mτ, e⟩`; otherwise the path is pruned. So a det-var behaves like
  `havoc x; assume (x = e)` — the pin ⟺ varDef equivalence.
- `init x := *` (`.nondet`, havoc) — a no-op: `x` is left free (the model already chose its value via
  `fvarVal`), exactly an `fvarDecl`.
- `ite .nondet t e` — terminal nondeterministic branching: three sibling rules stepping into `t`,
  `e`, or the continuation `rest` alone, each self-contained from the pre-branch config (branch
  declarations do not leak into `rest`). -/

/-- A small-step configuration: the remaining statements and the cumulative failure flag. No store
    or typing context — expression meaning is `Denotes`/`simpDenote` under the fixed model. -/
structure PConfig where
  work   : Statements
  failed : Bool

/-- **The Layer-1 small-step relation** over a fixed model `(opInterp, fvarVal)`. See the section
    header for the per-constructor semantics (assume/init-det prune; assert sets `failed`;
    havoc/cover no-op; ite branches). -/
inductive PStep (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) : PConfig → PConfig → Prop where
  /-- `assume b` on a live path (`b` denotes `true`); a false assume is pruned (no rule). -/
  | assumeLive (l : String) (b : Expression.Expr) (md : MetaData Expression)
               (rest : Statements) (f : Bool) (hb : Denotes opInterp fvarVal b true) :
      PStep opInterp fvarVal ⟨Statement.assume l b md :: rest, f⟩ ⟨rest, f⟩
  /-- `assert b` that holds: continue unchanged. -/
  | assertPass (l : String) (b : Expression.Expr) (md : MetaData Expression)
               (rest : Statements) (f : Bool) (hb : Denotes opInterp fvarVal b true) :
      PStep opInterp fvarVal ⟨Statement.assert l b md :: rest, f⟩ ⟨rest, f⟩
  /-- `assert b` that fails: continue with `failed := true`. -/
  | assertFail (l : String) (b : Expression.Expr) (md : MetaData Expression)
               (rest : Statements) (f : Bool) (hb : Denotes opInterp fvarVal b false) :
      PStep opInterp fvarVal ⟨Statement.assert l b md :: rest, f⟩ ⟨rest, true⟩
  /-- `init x := e` (`.det`) on a live path: the model pins `x` to `⟦e⟧` (exactly
      `VarDef.Consistent … ⟨x, mτ, e⟩`); a mismatching path is pruned (no rule). -/
  | initDetLive (x : Expression.Ident) (ty : Expression.Ty) (mτ : LMonoTy)
                (e : Expression.Expr) (md : MetaData Expression) (rest : Statements) (f : Bool)
                (hmono : ty.toMonoType? = some mτ)
                (h : LExpr.HasTypeA [] e mτ)
                (hpin : VarDef.Consistent opInterp fvarVal ⟨x.name, mτ, e⟩ h) :
      PStep opInterp fvarVal ⟨Statement.init x ty (.det e) md :: rest, f⟩ ⟨rest, f⟩
  /-- `init x := *` (havoc): no-op; `x` is left free (an `fvarDecl`). -/
  | initNondet (x : Expression.Ident) (ty : Expression.Ty) (md : MetaData Expression)
               (rest : Statements) (f : Bool) :
      PStep opInterp fvarVal ⟨Statement.init x ty .nondet md :: rest, f⟩ ⟨rest, f⟩
  -- `.ite .nondet` is terminal nondeterministic branching: the then-body, the else-body, and the
  -- continuation `rest` are explored as three independent paths from the pre-branch config — branch
  -- declarations/assumptions stay out of `rest`. So three sibling rules stepping into `t` / `e` /
  -- `rest` alone (not `t ++ rest`), making the reachable asserts exactly
  -- `(asserts in t) ∪ (asserts in e) ∪ (asserts in rest)`, matching `bodyObligations`'s `pfx→t`,
  -- `pfx→e`, `pfx→rest` sibling fan-out.
  /-- Non-deterministic branch into the then-body (self-contained). -/
  | iteLeft (thenb elseb : Statements) (md : MetaData Expression) (rest : Statements) (f : Bool) :
      PStep opInterp fvarVal ⟨Stmt.ite .nondet thenb elseb md :: rest, f⟩ ⟨thenb, f⟩
  /-- Non-deterministic branch into the else-body (self-contained). -/
  | iteRight (thenb elseb : Statements) (md : MetaData Expression) (rest : Statements) (f : Bool) :
      PStep opInterp fvarVal ⟨Stmt.ite .nondet thenb elseb md :: rest, f⟩ ⟨elseb, f⟩
  /-- The continuation `rest` after the branch, resumed from the pre-branch config. -/
  | iteRest (thenb elseb : Statements) (md : MetaData Expression) (rest : Statements) (f : Bool) :
      PStep opInterp fvarVal ⟨Stmt.ite .nondet thenb elseb md :: rest, f⟩ ⟨rest, f⟩

/-- Reflexive-transitive closure of `PStep` — multi-step reachability. -/
inductive PStepStar (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) : PConfig → PConfig → Prop where
  | refl (c : PConfig) : PStepStar opInterp fvarVal c c
  | tail (c₁ c₂ c₃ : PConfig) (h₁ : PStepStar opInterp fvarVal c₁ c₂)
         (h₂ : PStep opInterp fvarVal c₂ c₃) : PStepStar opInterp fvarVal c₁ c₃

/-- **`failed` is monotone under one step**: no step ever clears the flag (`assertFail` is the only
    writer, and it sets it to `true`; every other rule preserves it). So `c₁.failed ≤ c₂.failed`
    (Bool `≤`). Load-bearing for the soundness proof's first-failure extraction. -/
theorem PStep.failed_mono {opInterp fvarVal} {c₁ c₂ : PConfig}
    (h : PStep opInterp fvarVal c₁ c₂) : c₁.failed = true → c₂.failed = true := by
  cases h <;> simp_all

/-- **`failed` is monotone along a run.** The reflexive-transitive lift of `PStep.failed_mono`. -/
theorem PStepStar.failed_mono {opInterp fvarVal} {c₁ c₂ : PConfig}
    (h : PStepStar opInterp fvarVal c₁ c₂) : c₁.failed = true → c₂.failed = true := by
  induction h with
  | refl => exact id
  | tail _ _ _ hstep ih => exact fun hf => hstep.failed_mono (ih hf)

/-- **Contrapositive: `failed = false` is preserved backwards.** If a run ends with `failed = false`,
    it started with `failed = false`. Directly usable to reason about the `⟨ss, false⟩`-seeded runs
    in `Program.Valid`. -/
theorem PStepStar.not_failed_of_not_failed {opInterp fvarVal} {c₁ c₂ : PConfig}
    (h : PStepStar opInterp fvarVal c₁ c₂) (hc₂ : c₂.failed = false) : c₁.failed = false := by
  match hc₁ : c₁.failed with
  | false => rfl
  | true => rw [h.failed_mono hc₁] at hc₂; exact absurd hc₂ (by simp)

/-- **Front decomposition of a run.** A `PStepStar` is either reflexive (source = target) or takes a
    first step followed by a run. `PStepStar` is defined snoc-first (`refl`/`tail`), so exposing the
    head step needs this re-association — the dual of `tail`. Used to drive the run↔`bodyObligations`
    correspondence by the body's leading statement. -/
theorem PStepStar.uncons {opInterp fvarVal} {c₁ c₃ : PConfig}
    (h : PStepStar opInterp fvarVal c₁ c₃) :
    c₁ = c₃ ∨ ∃ c₂, PStep opInterp fvarVal c₁ c₂ ∧ PStepStar opInterp fvarVal c₂ c₃ := by
  induction h with
  | refl => exact Or.inl rfl
  | tail b c₃' hrun hstep ih =>
      rcases ih with heq | ⟨c₂, hfirst, hrest⟩
      · exact Or.inr ⟨c₃', heq ▸ hstep, PStepStar.refl c₃'⟩
      · exact Or.inr ⟨c₂, hfirst, PStepStar.tail c₂ b c₃' hrest hstep⟩

/-- **A single flag-flipping step is an `assertFail`.** The `failed` flag can only be raised by the
    `assertFail` rule (every other rule copies `f` through), so a step from `failed = false` to
    `failed = true` is exactly `assertFail` on some `assert b` with `b` denoting `false`, and the
    pre-config's work is `Statement.assert l b md :: rest`. The per-step core of first-failure
    extraction. -/
theorem PStep.assertFail_of_flip {opInterp fvarVal} {c c' : PConfig}
    (h : PStep opInterp fvarVal c c') (hc : c.failed = false) (hc' : c'.failed = true) :
    ∃ (l : String) (b : Expression.Expr) (md : MetaData Expression) (rest : Statements),
      c.work = Statement.assert l b md :: rest ∧ c = ⟨c.work, false⟩ ∧
      c' = ⟨rest, true⟩ ∧ Denotes opInterp fvarVal b false := by
  cases h with
  | assumeLive l b md rest f hb => simp_all
  | assertPass l b md rest f hb => simp_all
  | assertFail l b md rest f hb =>
      -- pre-config is `⟨assert :: rest, f⟩`; `f = false` (from `hc`), post is `⟨rest, true⟩`
      refine ⟨l, b, md, rest, rfl, ?_, rfl, hb⟩
      simp only at hc ⊢; rw [hc]
  | initDetLive x ty mτ e md rest f hmono he hpin => simp_all
  | initNondet x ty md rest f => simp_all
  | iteLeft thenb elseb md rest f => simp_all
  | iteRight thenb elseb md rest f => simp_all
  | iteRest thenb elseb md rest f => simp_all

/-- **First-failure extraction.** A run from a non-failed config to a failed one passes through a
    first `assertFail`: there is an intermediate `c` reached from `c₁` (still `failed = false`) and a
    single step `c → c'` that raises the flag. Peels the run from the end via `failed_mono` to locate
    the unique flag-flip. The entry point the soundness proof uses to name the violated obligation. -/
theorem PStepStar.first_failure {opInterp fvarVal} {c₁ c₂ : PConfig}
    (h : PStepStar opInterp fvarVal c₁ c₂) (hc₁ : c₁.failed = false) (hc₂ : c₂.failed = true) :
    ∃ (c c' : PConfig), PStepStar opInterp fvarVal c₁ c ∧
      PStep opInterp fvarVal c c' ∧ c.failed = false ∧ c'.failed = true := by
  -- Generalize the end-failed hypothesis into the motive so the IH applies to sub-runs.
  induction h with
  | refl => rw [hc₁] at hc₂; exact absurd hc₂ (by simp)
  | tail a b subrun hab ih =>
      -- `subrun : PStepStar c₁ a`, `hab : PStep a b` (last step), `ih : a.failed = true → …`,
      -- `hc₂ : b.failed = true`. Is `a` already failed?
      match haf : a.failed with
      | true =>
          -- failure happened earlier; recurse into `subrun`
          obtain ⟨c, c', hrun, hstep, hcf, hc'f⟩ := ih haf
          exact ⟨c, c', hrun, hstep, hcf, hc'f⟩
      | false =>
          -- the flip is exactly `a → b`
          exact ⟨a, b, subrun, hab, haf, hc₂⟩

/-- **A well-typed `assert` always steps** (never stuck or pruned). Case on its Boolean value:
    `true` fires `assertPass`, `false` fires `assertFail` — total on `Bool`. This corollary settles
    the vacuity concern: a false well-typed obligation must flip the `failed` flag. Stated for the
    original `PStep`; the witness comes from `hb`. -/
theorem PStep.assert_progress {opInterp fvarVal}
    (l : String) (b : Expression.Expr) (md : MetaData Expression) (rest : Statements) (f : Bool)
    (hb : LExpr.HasTypeA [] b (.tcons "bool" [])) :
    ∃ cfg', PStep opInterp fvarVal ⟨Statement.assert l b md :: rest, f⟩ cfg' := by
  match hv : (simpDenote opInterp fvarVal .nil b (.tcons "bool" []) hb : Bool) with
  | true  => exact ⟨⟨rest, f⟩,   .assertPass l b md rest f ⟨hb, hv⟩⟩
  | false => exact ⟨⟨rest, true⟩, .assertFail l b md rest f ⟨hb, hv⟩⟩

/-- **Typed progress.** A preprocessed (hence well-typed) non-empty work list is never stuck for
    typing reasons: the head either steps, or is one of the two intentional model-relative prunes
    (`assume`-false / det-mismatch). Cased on the leading `Preprocessed` constructor; each supplies
    the `HasTypeA`/`MonoTy` data the corresponding `PStep` rule needs, so the ill-typed "no rule"
    situation never arises. `assert`/`ite`/`havoc`/`nil-tail` always land in the "steps" disjunct;
    only `assume` and `initDet` can land in "prune". -/
theorem PStep.progress {opInterp fvarVal} {Ψ : FnCtx} {Φ : FVarCtx} {ss : Statements}
    (hpre : Statements.Preprocessed Ψ Φ ss) (f : Bool) :
    ss = [] ∨
    (∃ cfg', PStep opInterp fvarVal ⟨ss, f⟩ cfg') ∨
    -- intentional prune: leading `assume b` (well-typed) with `b` denoting false
    (∃ l b md rest, ss = Statement.assume l b md :: rest ∧
      ∃ h : LExpr.HasTypeA [] b (.tcons "bool" []),
        (simpDenote opInterp fvarVal .nil b (.tcons "bool" []) h : Bool) = false) ∨
    -- intentional prune: leading `init x := e` (det) not pinned by the model
    (∃ x ty mτ e md rest, ss = Statement.init x ty (.det e) md :: rest ∧
      ty.toMonoType? = some mτ ∧ ∃ h : LExpr.HasTypeA [] e mτ,
        ¬ VarDef.Consistent opInterp fvarVal ⟨x.name, mτ, e⟩ h) := by
  cases hpre with
  | nil => exact Or.inl rfl
  | assume Φ l b md rest hb hrest =>
      -- `assume`: true ⇒ steps (assumeLive); false ⇒ intentional prune
      have hbA := HasSimpType_implies_HasTypeA hb
      match hv : (simpDenote opInterp fvarVal .nil b (.tcons "bool" []) hbA : Bool) with
      | true  => exact Or.inr (Or.inl ⟨⟨rest, f⟩, .assumeLive l b md rest f ⟨hbA, hv⟩⟩)
      | false => exact Or.inr (Or.inr (Or.inl ⟨l, b, md, rest, rfl, hbA, hv⟩))
  | assert Φ l b md rest hb hrest =>
      exact Or.inr (Or.inl (PStep.assert_progress l b md rest f (HasSimpType_implies_HasTypeA hb)))
  | initDet Φ name ty mτ e md rest hmono he hfreshΦ hfreshΨ hnres hrest =>
      -- `initDet`: pinned ⇒ steps (initDetLive); mismatch ⇒ intentional prune
      have heA := HasSimpType_implies_HasTypeA he
      by_cases hpin : VarDef.Consistent opInterp fvarVal ⟨name.name, mτ, e⟩ heA
      · exact Or.inr (Or.inl ⟨⟨rest, f⟩, .initDetLive name ty mτ e md rest f hmono heA hpin⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨name, ty, mτ, e, md, rest, rfl, hmono, heA, hpin⟩))
  | initNondet Φ name ty mτ md rest hmono hsimp hfreshΦ hfreshΨ hnres hrest =>
      exact Or.inr (Or.inl ⟨⟨rest, f⟩, .initNondet name ty md rest f⟩)
  | ite Φ thenb elseb md rest hthen helse hrest =>
      exact Or.inr (Or.inl ⟨⟨thenb, f⟩, .iteLeft thenb elseb md rest f⟩)

/-! ## Whole-program validity

`Program.Valid p` is the Layer-1 headline notion the decomposition theorem relates to the emitted
`OblProgram`s' `OblProgram.Valid`. It mirrors `OblProgram.Valid`: for every Lambda model consistent
with each proc's prefix factory and satisfying the prefix axioms/distincts, no reachable body
configuration fails (defined via the `PStep` small-step semantics). -/

/-! ## `DistinctHolds` -/

/-- **A distinctness group holds under `M`**: at some shared type `τ`, the elements denote to
    pairwise-distinct values. The context-free (no `Φ`/`Ψ`) analog of `DistinctSat`; existential
    over `τ` and the per-element typing derivations (functional by `proof_irrel`, as in `Denotes`). -/
def DistinctHolds (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) (es : List Expression.Expr) : Prop :=
  ∃ (τ : LMonoTy) (h : ∀ e ∈ es, LExpr.HasTypeA [] e τ),
    (es.attach.map (fun x => simpDenote opInterp fvarVal .nil x.1 τ (h x.1 x.2))).Pairwise (· ≠ ·)

/-! ## Emit helpers

Emission is two-phase: all function declarations first, then all function axioms — so an axiom may
reference any declared function regardless of order (mutual cycles OK). A non-recursive function
emits `fnDef` (body, formals lifted fvar→bvar); a recursive one emits a bodyless `fnDecl` (phase 1)
plus its axioms (phase 2). -/

/-- The formals→bvar substitution map for `f`: input `i` (from the right, innermost-last, matching
    `toSMTTerm`'s `.bvar` scheme) maps to `.bvar () i`. Names are `f`'s input identifiers. -/
def funcBvarSubst (f : LFunc CoreLParams) : Map CoreLParams.Identifier Expression.Expr :=
  Map.ofList ((List.range f.inputs.length).map
    (fun i => (f.inputs.keys[i]!, (LExpr.bvar () i : Expression.Expr))))

/-- `funcBvarSubst` unfolded to its underlying association list (`Map.ofList` is the identity, so
    this is `rfl`). -/
theorem funcBvarSubst_eq_map (f : LFunc CoreLParams) :
    funcBvarSubst f = (List.range f.inputs.length).map
      (fun i => (f.inputs.keys[i]!, (LExpr.bvar () i : Expression.Expr))) := rfl

/-- The single declaration command for `f`: `fnDecl` (recursive/bodyless, body dropped) or `fnDef`
    (non-recursive + body, formals lifted fvar→bvar). Phase 1; axioms come in phase 2. -/
def emitFuncDecl (f : LFunc CoreLParams) : OblCommand :=
  match f.isRecursive, f.body with
  | false, some body =>
      .fnDef { name := f.name.name,
               argTys := f.inputs.values,
               retTy := f.output,
               body := LExpr.substFvarsLifting body (funcBvarSubst f) }
  | _, _ => .fnDecl f.name.name (funcSig f).2

/-- `f`'s axioms as `assume` commands. Phase 2. -/
def funcAxiomAssumes (f : LFunc CoreLParams) : List OblCommand :=
  f.axioms.map OblCommand.assume

/-- Phase 1: the declarations of the functions `names` (in the given body-topological order),
    looked up in `F`. Names not in `F` are skipped (never happens for `reachableFuncs` output). -/
def emitFuncDecls (F : Lambda.Factory CoreLParams) (names : List String) : List OblCommand :=
  names.filterMap (fun g => (F[g]?).map emitFuncDecl)

/-- Phase 2: the axioms of the functions `names`, as `assume`s. Emitted after all declarations, so
    each axiom's referenced functions are already declared regardless of order (mutual cycles OK). -/
def emitFuncAxioms (F : Lambda.Factory CoreLParams) (names : List String) : List OblCommand :=
  names.flatMap (fun g => (F[g]?).map funcAxiomAssumes |>.getD [])

/-- **`emitFuncDecl f` contributes exactly `funcSig f` to `Ψ`.** Both branches (`fnDef` for a
    non-recursive body, `fnDecl` otherwise) declare the signature `funcSig f`: the `fnDef`'s
    `d.sig` unfolds to `(f.name.name, foldr arrow f.output f.inputs.values)`, and
    `f.inputs.values = f.inputs.toList.map Prod.snd` (`ListMap.values_eq_map_snd`), matching
    `funcSig`. -/
theorem step_emitFuncDecl_Ψ (c : OblCtx) (f : LFunc CoreLParams) :
    (c.step (emitFuncDecl f)).Ψ = c.Ψ ++ [funcSig f] := by
  unfold emitFuncDecl
  split
  · -- non-recursive `fnDef`: `Ψ ++ [d.sig]`
    rename_i body _hnr _hbody
    simp only [OblCtx.step, FnDef.sig, funcSig]
    rw [ListMap.values_eq_map_snd]
    rfl
  · -- `fnDecl`: `Ψ ++ [(f.name.name, (funcSig f).2)]`
    simp only [OblCtx.step, funcSig]

/-- **Every declared function's signature lands in the folded `Ψ`.** For `g ∈ names` resolving to
    `f = F[g]`, `funcSig f` is in the `Ψ` accumulated by folding `emitFuncDecls F names` from any
    starting `c`. Induction on `names`; the head contributes `funcSig f` (via `step_emitFuncDecl_Ψ`)
    and later steps preserve it (`foldl_step_mem`). -/
theorem funcSig_mem_foldl_emitFuncDecls (F : Lambda.Factory CoreLParams) :
    ∀ (names : List String) (c : OblCtx) (g : String) (f : LFunc CoreLParams),
      g ∈ names → F[g]? = some f →
      funcSig f ∈ ((emitFuncDecls F names).foldl OblCtx.step c).Ψ := by
  intro names
  induction names with
  | nil => intro c g f hg _; simp at hg
  | cons hd tl ih =>
    intro c g f hg hres
    -- `emitFuncDecls F (hd :: tl) = (opt. head decl) ++ emitFuncDecls F tl`
    rw [emitFuncDecls, List.filterMap_cons]
    rcases List.mem_cons.mp hg with h | h
    · -- `g = hd`: the head resolves to `f` and contributes `funcSig f`
      subst h
      rw [hres]
      simp only [Option.map_some, List.foldl_cons]
      -- after stepping the head decl, `funcSig f ∈ Ψ`; preserved through the rest
      have hstep : funcSig f ∈ (c.step (emitFuncDecl f)).Ψ := by
        rw [step_emitFuncDecl_Ψ]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      exact (foldl_step_mem (cmds := emitFuncDecls F tl)).2 hstep
    · -- `g ∈ tl`: recurse; the optional head decl is just one more prefix step
      cases hhd : F[hd]? with
      | none => simp only [Option.map_none]; exact ih c g f h hres
      | some fhd =>
          simp only [Option.map_some, List.foldl_cons]
          exact ih (c.step (emitFuncDecl fhd)) g f h hres

/-! ## Body fan-out

`bodyObligations` walks a preprocessed body, emitting one `(prefix, obligation)` pair per `assert`
with the path-local decl/assume prefix accumulated in `PStep` order; at each `.ite` it fans out into
the two branches and the continuation (each self-contained). An explicit `stmtsSize` measure gives
the well-founded recursion. -/

/- Size of a statement / statement list, counting the `ite`-branch nesting — the well-founded
   measure for the fan-out walk (which recurses into the `ite` branches and continuation). -/
mutual
def stmtSize : Statement → Nat
  | Stmt.ite _ t e _ => 1 + stmtsSize t + stmtsSize e
  | _                => 1
def stmtsSize : Statements → Nat
  | []          => 0
  | s :: rest   => stmtSize s + stmtsSize rest
end

theorem stmtSize_pos (s : Statement) : 1 ≤ stmtSize s := by
  cases s <;> simp only [stmtSize] <;> omega

theorem stmtsSize_lt_cons (s : Statement) (rest : Statements) :
    stmtsSize rest < stmtsSize (s :: rest) := by
  have := stmtSize_pos s; simp only [stmtsSize]; omega

/-- **All non-predefined function references appearing in a statement list.** A proc-level
    over-approximation of the union of every emitted obligation's reachability seeds: it collects the
    `exprFnRefs` of exactly the statement forms `bodyObligations` scans — `assume`/`assert` bodies,
    `.det`-init bodies (the `varDef` an `init` becomes; `.nondet`-init contributes none), and both
    `ite` branches (matching `bodyObligations`' terminal-branch fan-out). `cover`/non-preprocessed
    statements contribute nothing, exactly as `bodyObligations` skips them. Used to scope the `.proc`
    typing clause to reachable functions (`reachableFuncs c.F (stmtsFnRefs ss ++ globalRefs)`);
    `bodyObligations_seeds_subset` proves each obligation's seeds land in this set. -/
def stmtsFnRefs : Statements → List String
  | []                                   => []
  | Statement.assume _ b _ :: rest       => exprFnRefs b ++ stmtsFnRefs rest
  | Statement.assert _ b _ :: rest       => exprFnRefs b ++ stmtsFnRefs rest
  | Statement.init _ _ (.det body) _ :: rest => exprFnRefs body ++ stmtsFnRefs rest
  | Stmt.ite .nondet t e _ :: rest       => stmtsFnRefs t ++ stmtsFnRefs e ++ stmtsFnRefs rest
  | _ :: rest                            => stmtsFnRefs rest
  termination_by ss => stmtsSize ss
  decreasing_by
    all_goals simp_wf
    all_goals
      first
        | (simp only [stmtsSize, stmtSize]; omega)
        | (apply stmtsSize_lt_cons)

/-- The declaration command for an `init` (if its declared type is monomorphic): `.det e` → a
    `varDef` pin, `.nondet` → an `fvarDecl`. `none` when the type is non-monomorphic (never under
    `Statements.Preprocessed`, whose `init` rules require `ty.toMonoType? = some _`). -/
def initDecl (x : Expression.Ident) (ty : Expression.Ty) (e : ExprOrNondet Expression) :
    Option OblCommand :=
  match ty.toMonoType? with
  | none    => none
  | some mτ => match e with
    | .det body => some (.varDef ⟨x.name, mτ, body⟩)
    | .nondet   => some (.fvarDecl x.name mτ)

/-- **The body fan-out.** See the section header. Returns `(prefix, obligation)` pairs, one per
    `assert`, with the path-local declaration/assumption prefix accumulated in `PStep` order. -/
def bodyObligations : (prefix_ : List OblCommand) → Statements →
    List (List OblCommand × Expression.Expr)
  | _,   []                                   => []
  | pfx, Statement.assume _ b _ :: rest       =>
      bodyObligations (pfx ++ [OblCommand.assume b]) rest
  | pfx, Statement.assert _ b _ :: rest       =>
      -- A discharged `assert` is not added to the path condition of subsequent obligations (a
      -- failing `assert` does not block execution in Strata — `PStep.assertFail` sets the `failed`
      -- flag but steps into `rest`). So the tail resumes from the same `pfx`, whereas `assume` does
      -- extend the path condition.
      (pfx, b) :: bodyObligations pfx rest
  | pfx, Statement.cover _ _ _ :: rest        => bodyObligations pfx rest
  | pfx, Statement.init x ty e _ :: rest      =>
      match initDecl x ty e with
      | some c => bodyObligations (pfx ++ [c]) rest
      | none   => bodyObligations pfx rest
  | pfx, Stmt.ite .nondet t e _ :: rest       =>
      -- `.ite` is terminal nondeterministic branching — each branch is explored self-contained from
      -- the pre-branch prefix `pfx`, and the continuation `rest` also resumes from `pfx` (branch
      -- declarations stay out of `rest`). So the three are siblings sharing `pfx`, not
      -- `t ++ rest`/`e ++ rest`.
      bodyObligations pfx t ++ bodyObligations pfx e ++ bodyObligations pfx rest
  | pfx, _ :: rest                            => bodyObligations pfx rest    -- non-preprocessed; skip
  termination_by _ ss => stmtsSize ss
  decreasing_by
    all_goals simp_wf
    all_goals
      first
        | (simp only [stmtsSize, stmtSize]; omega)
        | (apply stmtsSize_lt_cons)

/-! ## The prefix fold (declare-before-use over `Program.decls`; factory reconstruction)

`CoreCtx` accumulates, as the fold moves left over `Program.decls`, exactly "the collection up to
here": a reconstructed `Factory F` (seeded with the default `Core.Factory` — the ceval builtins —
grown by `pushIfNew` on each `.func`, so `concreteEval` is preserved, unlike `FnDef`), its function
context `Ψ = Lambda.Factory.fnCtx F`, the collected function axioms `fnAxioms` (typed later, at
procs — recursive-function axioms aren't well-typed until their mutual siblings are declared), the
global `.ax` axioms, and the `.distinct` groups.

`declWF` checks each `Decl` against the prefix context its predecessors built — the
declare-before-use condition. Topological order of the input `.func` decls is used here (a
non-recursive body types at the prefix `Ψ`, satisfiable only if callees precede it), not separately
assumed. Function-axiom well-formedness is deferred to the `.proc` case (`∀ ax ∈ fnAxioms`,
bool-typed at `Ψ`), where `Ψ` holds every function the proc needs — this is what lets
recursive/mutual function axioms (which reference not-yet-declared siblings at collection time) be
admitted.

In-proc variable declarations (`init`) are not here: they are proc-body-local (`Φ` grows within
`Statements.Preprocessed`/`bodyObligations`), never accumulating across procs (`Decl` has no
top-level variable declaration). -/

/-- The declaration-prefix context accumulated by the fold. `F` is the reconstructed factory
    (seeded with `Core.Factory`); `Ψ`/`fnAxioms`/`axioms`/`distincts` are read off the decls so far. -/
structure CoreCtx where
  F         : Lambda.Factory CoreLParams
  fnAxioms  : List Expression.Expr := []
  axioms    : List Expression.Expr := []
  distincts : List (List Expression.Expr) := []

/-- The default `Core.Factory`'s function axioms, collected. These are theory axioms the emitted
    obligation assumes (phase-2 `.assume` commands, decoupled from declarations) — so, like
    program-declared `.func` axioms, they belong in `fnAxioms` and the model is assumed to satisfy
    them. Seeding `init.fnAxioms` with them makes `fnAxioms` hold every factory function's axioms, so
    every emitted fn-axiom's satisfaction is discharged uniformly from `ProcValid`'s `fnAxioms`
    hypothesis — no separate "seed axioms hold" obligation. -/
def seedFnAxioms : List Expression.Expr :=
  Core.Factory.toArray.toList.flatMap (·.axioms)

/-- The initial context: the default `Core.Factory` (ceval builtins), its function axioms collected
    into `fnAxioms` (theory assumptions), everything else empty. -/
def CoreCtx.init : CoreCtx := { F := Core.Factory, fnAxioms := seedFnAxioms }

/-- The function context read off the accumulated factory. -/
def CoreCtx.Ψ (c : CoreCtx) : FnCtx := Lambda.Factory.fnCtx c.F

/-- Fold one declaration into the prefix context. `.func` pushes into the factory (keeping ceval)
    and collects its axioms; `.ax`/`.distinct` accumulate; `.proc`/`.type`/`.recFuncBlock` leave the
    declaration context unchanged (a proc consumes the context; type/recFuncBlock are unsupported). -/
def CoreCtx.step (c : CoreCtx) : Decl → CoreCtx
  | .func f _        => { c with F := c.F.pushIfNew f.toLFunc, fnAxioms := c.fnAxioms ++ f.axioms }
  | .ax a _          => { c with axioms := c.axioms ++ [a.e] }
  | .distinct _ es _ => { c with distincts := c.distincts ++ [es] }
  | .proc _ _ | .type _ _ | .recFuncBlock _ _ => c

/-- **The fold's `Ψ` only grows by append.** `pushIfNew` either no-ops (name already present) or
    appends `funcSig f`; every other step leaves the factory unchanged. So `(c.step d).Ψ = c.Ψ ++ Ψ'`
    for some `Ψ'` — the append shape `HasSimpType_mono_Ψ` consumes to lift accumulated typings. -/
theorem CoreCtx.step_Ψ_append (c : CoreCtx) (d : Decl) :
    ∃ Ψ', (c.step d).Ψ = c.Ψ ++ Ψ' := by
  cases d with
  | func f _ =>
      show ∃ Ψ', (Lambda.Factory.fnCtx (c.F.pushIfNew f.toLFunc)) = Lambda.Factory.fnCtx c.F ++ Ψ'
      unfold Lambda.Factory.pushIfNew
      split
      · exact ⟨[], by rw [List.append_nil]⟩
      · rename_i hnew
        refine ⟨[funcSig f.toLFunc], ?_⟩
        show (Lambda.Factory.push c.F f.toLFunc hnew).toArray.toList.map funcSig = _
        unfold Lambda.Factory.push
        show (c.F.toArray.push f.toLFunc).toList.map funcSig = _
        rw [Array.toList_push, List.map_append]
        rfl
  | ax a _ => exact ⟨[], by simp [CoreCtx.step, CoreCtx.Ψ]⟩
  | distinct _ es _ => exact ⟨[], by simp [CoreCtx.step, CoreCtx.Ψ]⟩
  | proc _ _ => exact ⟨[], by simp [CoreCtx.step, CoreCtx.Ψ]⟩
  | type _ _ => exact ⟨[], by simp [CoreCtx.step, CoreCtx.Ψ]⟩
  | recFuncBlock _ _ => exact ⟨[], by simp [CoreCtx.step, CoreCtx.Ψ]⟩

/-- **A procedure's reachability seeds (proc-level over-approximation).** The function references of
    the proc body (`stmtsFnRefs ss`) plus the prefix's global axiom/distinct references — a superset of
    the union of every emitted obligation's per-obligation seeds (`bodyObligations_seeds_subset` for the
    body part; the global part is shared verbatim with `procObligations`). Used to scope the `.proc`
    fn-axiom typing clause to functions reachable from this proc. -/
def CoreCtx.procSeeds (c : CoreCtx) (ss : Statements) : List String :=
  stmtsFnRefs ss ++ c.axioms.flatMap exprFnRefs
    ++ c.distincts.flatMap (fun es => es.flatMap exprFnRefs)

/-- Well-formedness of one declaration against the prefix context `c`. Uses `Lambda.Factory.fnCtx`
    functions must be topologically ordered so a non-recursive body types at the prefix `Ψ`. -/
def CoreCtx.declWF (c : CoreCtx) : Decl → Prop
  | .func f _ =>
      -- fresh name, SMT-encodable signature (each input type + output base — so `funcSig` is
      -- `MonoTyIsSimp` and `argTys` are base, what the emitted `fnDecl`/`fnDef` needs), and
      -- (non-recursive) body type-checks at the prefix Ψ in its formals context. Recursive functions:
      -- body dropped at emission, so no body-typing obligation here; axioms checked at the proc.
      f.name.name ∉ (Lambda.Factory.fnCtx c.F).map Prod.fst ∧
      (∀ n : Nat, f.name.name ≠ s!"$__bv{n}") ∧
      f.inputs.keys.Nodup ∧
      (∀ t ∈ f.inputs.values, LExpr.MonoTyIsBase t) ∧ LExpr.MonoTyIsBase f.output ∧
      -- A body-carrying function is non-recursive (recursive functions are declared bodyless, their
      -- semantics given by axioms; the emitter drops recursive bodies anyway).
      (∀ body, f.body = some body → f.isRecursive = false) ∧
      (f.isRecursive = false → ∀ body, f.body = some body →
        LExpr.HasSimpType (funcFVarCtx f.toLFunc) c.Ψ [] body f.output)
  | .ax a _ =>
      LExpr.HasSimpType [] c.Ψ [] a.e (.tcons "bool" [])
  | .distinct _ es _ =>
      2 ≤ es.length ∧ ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es, LExpr.HasSimpType [] c.Ψ [] e τ
  | .proc p _ =>
      -- the obligation body is preprocessed at the prefix Ψ (empty Φ — program vars via init);
      -- and the deferred function-axiom check: every axiom of a function reachable from this proc
      -- (`reachableFuncs c.F (c.procSeeds ss)`) is bool-typed at Ψ. Scoping to reachable functions
      -- (rather than all `c.fnAxioms`) is required: the default factory's polymorphic Map/Sequence
      -- axioms, unreachable in theory-free programs, quantify over type variables and cannot be
      -- `HasSimpType`-typed, so a blanket `∀ ax ∈ c.fnAxioms` clause would be unsatisfiable.
      ∃ ss, p.body = .structured ss ∧ Statements.Preprocessed c.Ψ [] ss ∧
        (∀ g ∈ reachableFuncs c.F (c.procSeeds ss), ∀ f, c.F[g]? = some f →
          ∀ ax ∈ f.axioms, LExpr.HasSimpType [] c.Ψ [] ax (.tcons "bool" []))
  | .type _ _ | .recFuncBlock _ _ => False   -- unsupported / eliminated before this stage

/-- **Prefix well-formedness from a starting context** — the Core-`Decl`-level dual of
    `OblProgramWFfrom`. Each declaration is `declWF` against the context its predecessors built. -/
def Program.WFfrom : List Decl → CoreCtx → Prop
  | [], _        => True
  | d :: rest, c => c.declWF d ∧ Program.WFfrom rest (c.step d)

/-- **The preprocessed Core program is well-formed** (prefix declare-before-use from the default
    factory). Functions are reconstructed into the fold's factory; validity (below) reuses
    `Factory.InterpConsistent` on the final such factory. -/
def Program.WF (p : Program) : Prop := Program.WFfrom p.decls CoreCtx.init

/-- **Accumulated axiom/distinct well-formedness at a fold context.** Every global axiom `∈ c.axioms`
    is bool-typed at `c.Ψ`, and every `.distinct` group `∈ c.distincts` shares one base type at
    `c.Ψ`. These lift the per-prefix `declWF` facts of earlier `.ax`/`.distinct` decls to the later
    (larger) `c.Ψ` — via `HasSimpType_mono_Ψ` (`Ψ` only grows by append, `CoreCtx.step_Ψ_append`). -/
def CoreCtx.Good (c : CoreCtx) : Prop :=
  (∀ e ∈ c.axioms, LExpr.HasSimpType [] c.Ψ [] e (.tcons "bool" [])) ∧
  (∀ es ∈ c.distincts, 2 ≤ es.length ∧
    ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es, LExpr.HasSimpType [] c.Ψ [] e τ)

/-- `CoreCtx.init` is `Good` (empty axioms/distincts). -/
theorem CoreCtx.init_Good : CoreCtx.init.Good := by
  refine ⟨?_, ?_⟩ <;> intro e he <;> simp [CoreCtx.init] at he

/-- **Accumulated factory-function well-formedness at a fold context.** Every reconstructed function
    `f ∈ c.F` has a non-reserved name with nodup formal keys and — if non-recursive — a body that
    type-checks at its fvar-formal context against the reconstruction-prefix `Ψ` — the `funcSig`s of
    the factory functions before it in `toArray` (`pre.map funcSig` for any split
    `toArray.toList = pre ++ f :: suf`), bvar context `[]`. Prefix-precise (tighter than the full
    `fnCtx c.F`): this is exactly what `declWF (.func)` gives (bodies type at the prefix Ψ, `.fnOp`
    forcing callees ∈ prefix ⟹ callees declared earlier — the topological order), and it is what
    lets connector 1c conclude a callee precedes its caller in the emitted list. The seed base
    (`CoreCtx.init.F = Core.Factory`) is discharged downstream. -/
def CoreCtx.FactoryFuncsWF (c : CoreCtx) : Prop :=
  ∀ (pre : List (LFunc CoreLParams)) (f : LFunc CoreLParams) (suf : List (LFunc CoreLParams)),
    c.F.toArray.toList = pre ++ f :: suf →
    (∀ n : Nat, f.name.name ≠ s!"$__bv{n}") ∧
    f.inputs.keys.Nodup ∧
    -- A function carrying a body is non-recursive (recursive functions emit bodyless `fnDecl`); this
    -- lets the reachability base-closure use the guarded body-typing below for body references.
    (∀ body, f.body = some body → f.isRecursive = false) ∧
    (f.isRecursive = false → ∀ body, f.body = some body →
      LExpr.HasSimpType (funcFVarCtx f) (pre.map funcSig) [] body f.output)

/-- **The seed factory's function well-formedness** (`init.FactoryFuncsWF`). Threaded as a premise of
    the two top-level theorems (`toOblPrograms_wf`, `program_valid_of_oblProgramsValid`).

    `FactoryFuncsWF` does not require signatures to be `MonoTyIsBase`: the default `Core.Factory`
    contains uninterpreted regex/`Sequence`/`Map` functions with non-base signatures (e.g.
    `reAllFunc.output = .tcons "regex" []`), which a well-typed obligation can never reference.
    Base-ness of the functions the emitter actually touches is instead re-derived from the
    obligation's typing (`base_of_SimpSig` ∘ `reachableOrdered_simp`). What remains are the conjuncts
    that hold for `Core.Factory`: name freshness/non-reserved, `inputs.keys` nodup,
    bodied⟹non-recursive, and (vacuously — all seed functions are bodyless) body typing.

    So this premise is dischargeable for the real `Core.Factory`; it is proved as
    `Core.SeedFactory.init_FactoryFuncsWF` in `SeedFactory.lean` (a separate file since the discharge
    is `native_decide`-heavy over the concrete factory). -/
abbrev CoreCtx.SeedFactoryFuncsWF : Prop := CoreCtx.init.FactoryFuncsWF

/-- **Seed builtin-consistency premise.** Any model consistent with the default `Core.Factory`
    interprets each predefined operator as its concrete Lean function (`OpInterpConsistent`). It is
    threaded through the Layer-1 validity chain as a premise, so this file avoids a dependency on the
    `native_decide`-heavy consistency proof; it is discharged for the concrete factory downstream in
    `SeedFactory.lean`.

    Quantified over `opInterp` because the model is introduced internally (under `ProcValid`'s `∀`),
    so the premise is applied at a locally-bound model. -/
abbrev CoreCtx.SeedBuiltinConsistent : Prop :=
  ∀ {opInterp : Lambda.OpInterp simpTcInterp},
    Lambda.Factory.InterpConsistent simpTcInterp opInterp Core.Factory →
      ∃ divByZero modByZero, OpInterpConsistent divByZero modByZero opInterp

/-- **`pushIfNew` membership**: an element of `(F.pushIfNew fn).toArray` is either already in `F` or
    equals `fn`. -/
theorem toArray_pushIfNew_mem {F : Lambda.Factory CoreLParams} {fn g : LFunc CoreLParams}
    (h : g ∈ (F.pushIfNew fn).toArray) : g ∈ F.toArray ∨ g = fn := by
  unfold Lambda.Factory.pushIfNew at h
  split at h
  · exact Or.inl h
  · -- `push`: toArray = F.toArray.push fn
    rename_i hnew
    have : (Lambda.Factory.push F fn hnew).toArray = F.toArray.push fn := rfl
    rw [this, Array.mem_push] at h
    exact h

/-- **Seed provenance invariant.** The reconstructed factory `c.F` always extends the default
    `Core.Factory` as an array prefix, and every reconstructed function's axioms were collected into
    `c.fnAxioms` — uniformly, since `init.fnAxioms = seedFnAxioms` already holds the seed functions'
    axioms and each `.func` step appends the new function's axioms. This routes each emitted function
    axiom's satisfaction to `ProcValid`'s `fnAxioms` hypothesis (the model satisfies `c.fnAxioms`).
    Pure structural bookkeeping — `init`-true and `step`-preserved without any `declWF`. -/
def CoreCtx.SeedWF (c : CoreCtx) : Prop :=
  (∃ extra, c.F.toArray.toList = Core.Factory.toArray.toList ++ extra) ∧
  (∀ f ∈ c.F.toArray, ∀ ax ∈ f.axioms, ax ∈ c.fnAxioms)

/-- `CoreCtx.init` is `SeedWF`: its factory IS `Core.Factory` (prefix with empty extra), and every
    seed function's axioms are in `init.fnAxioms = seedFnAxioms` (the flatMap of all seed axioms). -/
theorem CoreCtx.init_SeedWF : CoreCtx.init.SeedWF := by
  refine ⟨⟨[], by show (Core.Factory).toArray.toList = _; rw [List.append_nil]⟩, ?_⟩
  intro f hf ax hax
  -- `init.fnAxioms = seedFnAxioms = Core.Factory.toArray.toList.flatMap (·.axioms)`
  show ax ∈ seedFnAxioms
  unfold seedFnAxioms
  exact List.mem_flatMap.mpr ⟨f, Array.mem_def.mp hf, hax⟩

/-- **`CoreCtx.step` preserves `SeedWF`.** Only `.func` touches `F`/`fnAxioms`: `pushIfNew` either
    no-ops (name already present) or appends `f` (prefix preserved), and `fnAxioms` grows by
    `f.axioms` so old functions stay covered and the new `f`'s axioms land in the appended part. Every
    other decl leaves `F`/`fnAxioms` fixed. No `declWF` needed. -/
theorem CoreCtx.SeedWF.step {c : CoreCtx} (d : Decl) (h : c.SeedWF) : (c.step d).SeedWF := by
  obtain ⟨⟨extra, hext⟩, hprov⟩ := h
  cases d with
  | func f md =>
      -- `pushIfNew` toList: no-op or append `[f.toLFunc]`
      have hpush : (c.F.pushIfNew f.toLFunc).toArray.toList = c.F.toArray.toList ∨
          (c.F.pushIfNew f.toLFunc).toArray.toList = c.F.toArray.toList ++ [f.toLFunc] := by
        unfold Lambda.Factory.pushIfNew
        split
        · exact Or.inl rfl
        · rename_i hnew
          exact Or.inr (by show (c.F.toArray.push f.toLFunc).toList = _; rw [Array.toList_push])
      refine ⟨?_, ?_⟩
      · -- prefix preserved: `Core.Factory ++ extra` or `Core.Factory ++ (extra ++ [f.toLFunc])`
        show ∃ e, (c.F.pushIfNew f.toLFunc).toArray.toList = _ ++ e
        rcases hpush with h | h
        · exact ⟨extra, by rw [h, hext]⟩
        · exact ⟨extra ++ [f.toLFunc], by rw [h, hext, List.append_assoc]⟩
      · -- provenance: `step` grows `fnAxioms` by `f.axioms`; old fns covered (left), new `f` (right)
        show ∀ g ∈ (c.F.pushIfNew f.toLFunc).toArray, ∀ ax ∈ g.axioms, ax ∈ c.fnAxioms ++ f.axioms
        intro g hg ax hax
        rcases toArray_pushIfNew_mem hg with hold | hgf
        · exact List.mem_append_left _ (hprov g hold ax hax)
        · exact List.mem_append_right _ (by rw [hgf] at hax; exact hax)
  | ax a _ => exact ⟨⟨extra, hext⟩, hprov⟩
  | distinct _ es _ => exact ⟨⟨extra, hext⟩, hprov⟩
  | proc _ _ => exact ⟨⟨extra, hext⟩, hprov⟩
  | type _ _ => exact ⟨⟨extra, hext⟩, hprov⟩
  | recFuncBlock _ _ => exact ⟨⟨extra, hext⟩, hprov⟩

/-- Splitting `pre ++ g :: suf = old ++ [x]`: either `g :: (its tail)` lies within `old` (so `old`
    splits `pre ++ g :: rest`), or `g` is the appended `x` at the very end (`pre = old`, `suf = []`). -/
theorem split_append_singleton {α} {pre : List α} {g : α} {suf old : List α} {x : α}
    (h : pre ++ g :: suf = old ++ [x]) :
    (∃ rest, old = pre ++ g :: rest) ∨ (pre = old ∧ g = x ∧ suf = []) := by
  induction pre generalizing old with
  | nil =>
      cases old with
      | nil =>
          -- `g :: suf = [x]` ⇒ g = x, suf = []
          simp only [List.nil_append] at h
          rw [List.cons_eq_cons] at h
          exact Or.inr ⟨rfl, h.1, h.2⟩
      | cons o0 os =>
          -- `g :: suf = o0 :: os ++ [x]` ⇒ old = g :: os = [] ++ g :: os
          simp only [List.nil_append, List.cons_append, List.cons_eq_cons] at h
          exact Or.inl ⟨os, by rw [h.1]; rfl⟩
  | cons p0 ps ih =>
      cases old with
      | nil =>
          -- `p0 :: ps ++ g :: suf = [x]` impossible (length ≥ 2)
          exfalso; simp only [List.cons_append, List.nil_append, List.cons_eq_cons] at h
          have := congrArg List.length h.2; simp at this
      | cons o0 os =>
          simp only [List.cons_append, List.cons_eq_cons] at h
          rcases ih h.2 with ⟨rest, hrest⟩ | ⟨hpre, hgx, hsuf⟩
          · exact Or.inl ⟨rest, by rw [hrest, h.1]; rfl⟩
          · exact Or.inr ⟨by rw [hpre, h.1], hgx, hsuf⟩

theorem CoreCtx.FactoryFuncsWF.step {c : CoreCtx} {d : Decl}
    (hwf : c.FactoryFuncsWF) (hdWF : c.declWF d) : (c.step d).FactoryFuncsWF := by
  cases d with
  | func f md =>
      rw [CoreCtx.declWF] at hdWF
      obtain ⟨hfresh, hnres, hkeys, hinbase, houtbase, hbnr, hbodyty⟩ := hdWF
      -- `f.name ∉ fnCtx c.F` ⇒ `pushIfNew` genuinely pushes ⇒ new `toArray.toList = old ++ [f]`
      have hnotin : f.toLFunc.name.name ∉ c.F := by
        rw [Factory.mem_iff_mem_names]
        intro h
        refine hfresh ?_
        obtain ⟨e, hemem, hename⟩ := Array.mem_map.mp h
        exact List.mem_map.mpr ⟨funcSig e, List.mem_map.mpr ⟨e, Array.mem_def.mp hemem, rfl⟩,
          by rw [funcSig]; exact hename⟩
      have hpush : (c.step (.func f md)).F.toArray.toList = c.F.toArray.toList ++ [f.toLFunc] := by
        show (c.F.pushIfNew f.toLFunc).toArray.toList = _
        unfold Lambda.Factory.pushIfNew; rw [dif_neg hnotin]
        show (c.F.toArray.push f.toLFunc).toList = _
        rw [Array.toList_push]
      intro pre g suf hsplit
      rw [hpush] at hsplit
      -- `pre ++ g :: suf = old ++ [f]`. Compare against `old`: `g :: suf` starts within `old` (g old)
      -- or exactly at the appended `f`.
      rcases split_append_singleton hsplit.symm with ⟨rest, hpre⟩ | ⟨hpre, hgf, hsuf⟩
      · -- `g` is an old function: `old = pre ++ g :: rest`, and its prefix is the same `pre`
        -- (appending `f` at the very end doesn't change any old function's prefix).
        exact hwf pre g rest hpre
      · -- `g = f`, `pre = old`, `suf = []`: `f`'s body types at `pre.map funcSig = fnCtx c.F`
        subst hgf
        refine ⟨hnres, hkeys, hbnr, fun hnr body hb => ?_⟩
        have hpsig : pre.map funcSig = Lambda.Factory.fnCtx c.F := by rw [hpre, Lambda.Factory.fnCtx]
        rw [hpsig]; exact hbodyty hnr body hb
  | ax a _ => intro pre g suf h; exact hwf pre g suf h
  | distinct _ es _ => intro pre g suf h; exact hwf pre g suf h
  | proc _ _ => intro pre g suf h; exact hwf pre g suf h
  | type _ _ => rw [CoreCtx.declWF] at hdWF; exact hdWF.elim
  | recFuncBlock _ _ => rw [CoreCtx.declWF] at hdWF; exact hdWF.elim

/-- **`CoreCtx.step` preserves `Good`**, given the stepped decl is `declWF` at `c`. A `.ax`/`.distinct`
    step adds one entry (typed at `c.Ψ` by `declWF`, lifted to `c.Ψ` unchanged); a `.func` step grows
    `Ψ` by append, lifting existing axiom/distinct typings via `HasSimpType_mono_Ψ`; `.proc`/etc. leave
    axioms/distincts and `Ψ` unchanged. -/
theorem CoreCtx.Good.step {c : CoreCtx} {d : Decl} (hgood : c.Good) (hdWF : c.declWF d) :
    (c.step d).Good := by
  obtain ⟨hax, hdist⟩ := hgood
  -- `Ψ` grows by append, so existing typings lift by `HasSimpType_mono_Ψ`
  obtain ⟨Ψ', hΨ'⟩ := CoreCtx.step_Ψ_append c d
  have hliftAx : ∀ e ∈ c.axioms, LExpr.HasSimpType [] (c.step d).Ψ [] e (.tcons "bool" []) := by
    intro e he; rw [hΨ']; exact HasSimpType_mono_Ψ Ψ' (hax e he)
  have hliftDist : ∀ es ∈ c.distincts, 2 ≤ es.length ∧
      ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es, LExpr.HasSimpType [] (c.step d).Ψ [] e τ := by
    intro es hes; obtain ⟨hlen, τ, hbase, hty⟩ := hdist es hes
    exact ⟨hlen, τ, hbase, fun e he => by rw [hΨ']; exact HasSimpType_mono_Ψ Ψ' (hty e he)⟩
  cases d with
  | func f _ => exact ⟨fun e he => hliftAx e he, fun es hes => hliftDist es hes⟩
  | ax a md =>
      refine ⟨?_, ?_⟩
      · -- `axioms ++ [a.e]`: old ones lift; the new `a.e` is typed by `declWF`
        intro e he
        rw [CoreCtx.step] at he ⊢
        simp only at he ⊢
        rcases List.mem_append.mp he with h | h
        · exact hliftAx e h
        · rw [List.mem_singleton.mp h]
          rw [CoreCtx.declWF] at hdWF
          show LExpr.HasSimpType [] (c.step (.ax a md)).Ψ [] a.e _
          have : (c.step (.ax a md)).Ψ = c.Ψ := by simp [CoreCtx.step, CoreCtx.Ψ]
          rw [this]; exact hdWF
      · intro es hes; exact hliftDist es (by rw [CoreCtx.step] at hes; exact hes)
  | distinct n es' md =>
      refine ⟨?_, ?_⟩
      · intro e he; exact hliftAx e (by rw [CoreCtx.step] at he; exact he)
      · intro es hes
        rw [CoreCtx.step] at hes ⊢
        simp only at hes ⊢
        rcases List.mem_append.mp hes with h | h
        · exact hliftDist es h
        · rw [List.mem_singleton.mp h]
          rw [CoreCtx.declWF] at hdWF
          obtain ⟨hlen, τ, hbase, hty⟩ := hdWF
          exact ⟨hlen, τ, hbase, fun e he => hty e he⟩
  | proc _ _ => exact ⟨hliftAx, hliftDist⟩
  | type _ _ => rw [CoreCtx.declWF] at hdWF; exact hdWF.elim
  | recFuncBlock _ _ => rw [CoreCtx.declWF] at hdWF; exact hdWF.elim

/-! ## The emitter (`Program → List OblProgram`, per-proc at its prefix, per-assert minimal)

Walks `Program.decls` with the same `CoreCtx.step` fold. At each `.proc`, the accumulated context
`c` is "the declarations up to this procedure" — its factory `c.F`, axioms, distincts. For each
`assert` in that proc's body, one `OblProgram` is emitted whose command prefix is minimal: only the
functions transitively reachable from that obligation (plus its path assumptions and globals) are
declared, filtered from the factory in its (topological) array order so declare-before-use holds.

The shared per-obligation prefix, for reachable function names `fns` (a subset of the factory in
array order) and this proc's context `c`:
1. function declarations (`emitFuncDecls c.F fns`) — topological (array) order;
2. function axioms (`emitFuncAxioms c.F fns`) — after all declarations;
3. `c.distincts` as `distinct` commands;
4. `c.axioms` as `assume` commands;

then the body's per-assert `(bodyPrefix, obligation)` pair. -/

/-- The reachable function names for one obligation, filtered to the factory's array (topological)
    order so the emitted declarations satisfy declare-before-use. `seeds` are the non-predefined
    heads of the obligation-relevant expressions. -/
def reachableOrdered (F : Lambda.Factory CoreLParams) (seeds : List String) : List String :=
  let reach := reachableFuncs F seeds
  (factoryNames F).filter (· ∈ reach)

/-- **`reachableOrdered` is `funcDeps`-closed.** A reached-ordered node's `funcDeps` are all
    reached-ordered — the transitive-closure fact feeding the topological callees-precede argument:
    a callee referenced by an emitted function's body/axioms is itself emitted. -/
theorem reachableOrdered_closed (F : Lambda.Factory CoreLParams) (seeds : List String)
    {g : String} (hg : g ∈ reachableOrdered F seeds) {h : String} (hh : h ∈ funcDeps F g) :
    h ∈ reachableOrdered F seeds := by
  unfold reachableOrdered at hg ⊢
  rw [List.mem_filter] at hg ⊢
  exact ⟨funcDeps_subset F g h hh,
    decide_eq_true (reachableFuncs_closed F seeds (of_decide_eq_true hg.2) hh)⟩

/-- The shared command prefix for an obligation with reachable functions `fns`, under proc-context
    `c`: declarations, then function axioms, then distincts, then global axioms. -/
def obligationPrefix (c : CoreCtx) (fns : List String) : List OblCommand :=
  emitFuncDecls c.F fns ++ emitFuncAxioms c.F fns ++
  c.distincts.map OblCommand.distinct ++ c.axioms.map OblCommand.assume

/-- **A seed that is a factory node is reachable-ordered.** Combines seed-reachability
    (`mem_reachableFuncs_of_seed`) with the array-order filter defining `reachableOrdered`. The
    membership half of connector 1c: an obligation's referenced factory functions are emitted. -/
theorem mem_reachableOrdered_of_seed (F : Lambda.Factory CoreLParams) (seeds : List String)
    {g : String} (hg : g ∈ seeds) (hnode : g ∈ factoryNames F) :
    g ∈ reachableOrdered F seeds := by
  unfold reachableOrdered
  rw [List.mem_filter]
  exact ⟨hnode, decide_eq_true (mem_reachableFuncs_of_seed F seeds hg hnode)⟩

/-- **A resolved reachable function's signature is in the folded `Ψ` of `obligationPrefix ++ extra`.**
    `emitFuncDecls` (the head of `obligationPrefix`) contributes `funcSig f` for each declared `g`;
    the `emitFuncAxioms`/distinct/axiom tail and any `extra` suffix only append to `Ψ`, so membership
    is preserved (`foldl_step_mem`). This is the `Ψ`-characterization feeding `HasSimpType_restrict_Ψ`. -/
theorem funcSig_mem_obligationPrefix_Ψ (c : CoreCtx) (fns : List String) (extra : List OblCommand)
    {g : String} {f : LFunc CoreLParams} (hg : g ∈ fns) (hres : c.F[g]? = some f) :
    funcSig f ∈ ((obligationPrefix c fns ++ extra).foldl OblCtx.step {}).Ψ := by
  unfold obligationPrefix
  -- fold splits: `funcSig f` enters at `emitFuncDecls`, preserved through the rest.
  rw [List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_append]
  -- innermost: after `emitFuncDecls`, `funcSig f ∈ Ψ`
  have h0 : funcSig f ∈ ((emitFuncDecls c.F fns).foldl OblCtx.step {}).Ψ :=
    funcSig_mem_foldl_emitFuncDecls c.F fns {} g f hg hres
  -- preserve through `emitFuncAxioms`, distincts, axioms, extra (each a `foldl` append)
  exact (foldl_step_mem).2 ((foldl_step_mem).2 ((foldl_step_mem).2 ((foldl_step_mem).2 h0)))

/-- **The `restrict_Ψ` side-condition holds for any expression whose refs are seeds.** If every
    non-predefined head `exprFnRefs e` is among `seeds`, then narrowing the proc context `fnCtx c.F`
    to the emitted `Q.Ψ` preserves every referenced entry: a referenced `(n, σ) ∈ fnCtx c.F`
    resolves (`mem_fnCtx_resolves`) to a factory node `n`, which — being a seed — is reachable
    (`mem_reachableOrdered_of_seed`), so its `funcSig` sits in `Q.Ψ`
    (`funcSig_mem_obligationPrefix_Ψ`). This is the exact hypothesis
    `HasSimpType_restrict_Ψ` consumes for the obligation and for each `bpfx`-assumption. -/
theorem restrict_Ψ_side_condition (c : CoreCtx) (seeds : List String) (extra : List OblCommand)
    (e : Expression.Expr) (hrefs : ∀ n ∈ exprFnRefs e, n ∈ seeds) :
    ∀ n ∈ exprFnRefs e, ∀ σ, (n, σ) ∈ Lambda.Factory.fnCtx c.F →
      (n, σ) ∈ ((obligationPrefix c (reachableOrdered c.F seeds) ++ extra).foldl OblCtx.step {}).Ψ := by
  intro n hn σ hmem
  obtain ⟨f, hres, hfsig, hnode⟩ := mem_fnCtx_resolves c.F hmem
  have hfns : n ∈ reachableOrdered c.F seeds := mem_reachableOrdered_of_seed c.F seeds (hrefs n hn) hnode
  have := funcSig_mem_obligationPrefix_Ψ c (reachableOrdered c.F seeds) extra hfns hres
  rwa [hfsig] at this

/-- Emit the obligation programs for one procedure body `ss` under prefix-context `c`: one
    `OblProgram` per assert. Each obligation's reachable functions are computed from its own seeds —
    the obligation expression, its path assumptions (`bodyPrefix`), and the global axioms/distincts
    — for per-assertion minimality. -/
def procObligations (c : CoreCtx) (ss : Statements) : List OblProgram :=
  (bodyObligations [] ss).map (fun (bpfx, ob) =>
    -- seeds: this obligation + its path assumes/`.det`-var bodies + global axioms + distinct elements.
    -- (`.varDef` bodies are scanned too: a `.det init x := e` command's `e` may call a factory
    -- function, which must then be declared for the emitted `.varDef` to type-check. `.fvarDecl`
    -- carries no body, so it contributes nothing.)
    let seeds := exprFnRefs ob
      ++ bpfx.flatMap (fun | .assume e => exprFnRefs e | .varDef v => exprFnRefs v.body | _ => [])
      ++ c.axioms.flatMap exprFnRefs
      ++ c.distincts.flatMap (fun es => es.flatMap exprFnRefs)
    let fns := reachableOrdered c.F seeds
    ⟨obligationPrefix c fns ++ bpfx, ob⟩)

/-- Walk the declarations, folding the prefix context and emitting each procedure's obligations at
    its own prefix. The Core-`Decl`-level dual of the per-body fan-out, with position respected. -/
def toOblProgramsFrom : List Decl → CoreCtx → List OblProgram
  | [], _        => []
  | d :: rest, c =>
    let here := match d with
      | .proc p _ => match p.body with
                     | .structured ss => procObligations c ss
                     | .cfg _         => []
      | _ => []
    here ++ toOblProgramsFrom rest (c.step d)

/-- **The whole-program emitter.** One `OblProgram` per `assert` across all procedures, each with
    the minimal function prefix from its own procedure's declaration context. -/
def toOblPrograms (p : Program) : List OblProgram :=
  toOblProgramsFrom p.decls CoreCtx.init

/-! ## Validity (per-procedure, at its prefix context — the source-side `LogConseq`)

`Program.Valid` reuses Core's `Factory.InterpConsistent` on the reconstructed factory at each
procedure's prefix context (the point of factory reconstruction: connectors 1a/1b become
projections of this one consistency fact — UDF bodies via `InterpConsistentBody`, ceval builtins via
`InterpConsistentEval`). For every procedure, and every model consistent with that proc's factory
`c.F` and satisfying the prefix axioms/distincts, no reachable configuration of the proc's body has
`failed` set (i.e. every reachable `assert` holds). Position is respected: each proc uses the
context its predecessors built. -/

/-- Body validity of one procedure at prefix-context `c`: for every factory-consistent model
    satisfying the prefix axioms + fn-axioms + distincts, no reachable body config fails. -/
def ProcValid (c : CoreCtx) (ss : Statements) : Prop :=
  ∀ (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp),
    Lambda.Factory.InterpConsistent simpTcInterp opInterp c.F →
    (∀ e ∈ c.axioms, Denotes opInterp fvarVal e true) →
    (∀ e ∈ c.fnAxioms, Denotes opInterp fvarVal e true) →
    (∀ es ∈ c.distincts, DistinctHolds opInterp fvarVal es) →
    ∀ cfg, PStepStar opInterp fvarVal ⟨ss, false⟩ cfg → cfg.failed = false

/-- Fold the prefix context and require `ProcValid` at each procedure's own prefix. -/
def Program.ValidFrom : List Decl → CoreCtx → Prop
  | [], _        => True
  | d :: rest, c =>
    (match d with
     | .proc p _ => match p.body with
                    | .structured ss => ProcValid c ss
                    | .cfg _         => True
     | _ => True) ∧
    Program.ValidFrom rest (c.step d)

/-- **The preprocessed Core program is valid** — every procedure's obligations hold, each at the
    declaration context accumulated up to that procedure. -/
def Program.Valid (p : Program) : Prop := Program.ValidFrom p.decls CoreCtx.init

/-! ## Soundness

`program_valid_of_oblProgramsValid`: if every emitted `OblProgram` is `OblProgram.Valid`, the
preprocessed program is `Program.Valid`. Composed with `oblProgram_valid_of_smtUnsat` (Layer 2), the
tower gives `(∀ emitted SMT query, Unsat) → Program.Valid`. Proven modulo the `SeedFactoryFuncsWF`
premise (discharged for the default `Core.Factory` in `SeedFactory`); the model-transfer discharge
routes through connectors 1a/1b (the guarded div/mod ops via the model-chosen div-by-zero values). -/

/-! ## Supporting lemmas for `toOblPrograms_wf` (structural, bottom-up) -/

/- **Ψ-narrowing for `HasSimpType`.** A body typed at `Ψ` stays typed at a narrower `Ψ'` provided
   every non-predefined head name it applies (`exprFnRefs`) keeps its `Ψ`-entry in `Ψ'`. `Φ` and
   `Δ` are untouched (fvars/bvars are unaffected by the `Ψ` restriction) — the connector-1c
   foundation, since reachability guarantees exactly this side condition for the reachable-ordered
   `Ψ'`. -/
mutual
theorem HasSimpType_restrict_Ψ {Φ : FVarCtx} {Ψ Ψ' : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {τ : LMonoTy}
    (hsub : ∀ n ∈ exprFnRefs e, ∀ σ, (n, σ) ∈ Ψ → (n, σ) ∈ Ψ')
    (he : LExpr.HasSimpType Φ Ψ Δ e τ) :
    LExpr.HasSimpType Φ Ψ' Δ e τ := by
  match he with
  | .const c hbase => exact .const c hbase
  | .bvar i t hlook hbase => exact .bvar i t hlook hbase
  | .app fn arg rty hspine => exact .app fn arg rty (AppSpine_restrict_Ψ hsub hspine)
  | .fvarNullary f t rty hspine => exact .fvarNullary f t rty (AppSpine_restrict_Ψ hsub hspine)
  | .ite c t t' d hc ht he_ =>
    -- `exprFnRefs (.ite c t e) = (exprFnRefs c ++ exprFnRefs t) ++ exprFnRefs e`
    refine .ite c t t' d (HasSimpType_restrict_Ψ ?_ hc) (HasSimpType_restrict_Ψ ?_ ht)
      (HasSimpType_restrict_Ψ ?_ he_)
    · intro n hn; apply hsub n
      simp only [exprFnRefs]; exact List.mem_append_left _ (List.mem_append_left _ hn)
    · intro n hn; apply hsub n
      simp only [exprFnRefs]; exact List.mem_append_left _ (List.mem_append_right _ hn)
    · intro n hn; apply hsub n
      simp only [exprFnRefs]; exact List.mem_append_right _ hn
  | .eq e1 e2 t hbase he1 he2 =>
    refine .eq e1 e2 t hbase (HasSimpType_restrict_Ψ ?_ he1) (HasSimpType_restrict_Ψ ?_ he2)
    · intro n hn; apply hsub n
      simp only [exprFnRefs]; exact List.mem_append_left _ hn
    · intro n hn; apply hsub n
      simp only [exprFnRefs]; exact List.mem_append_right _ hn
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody =>
    -- `exprFnRefs (.quant … tr body) = exprFnRefs tr ++ exprFnRefs body`; restrict both (the trigger
    -- may carry refs).
    refine .quant qty qbody qk qname qtr qτtr hbase
      (HasSimpType_restrict_Ψ ?_ htr) (HasSimpType_restrict_Ψ ?_ hbody)
    · intro n hn; apply hsub n
      simp only [exprFnRefs]; exact List.mem_append_left _ hn
    · intro n hn; apply hsub n
      simp only [exprFnRefs]; exact List.mem_append_right _ hn

theorem AppSpine_restrict_Ψ {Φ : FVarCtx} {Ψ Ψ' : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {acc : List LMonoTy} {rty : LMonoTy}
    (hsub : ∀ n ∈ exprFnRefs e, ∀ σ, (n, σ) ∈ Ψ → (n, σ) ∈ Ψ')
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    LExpr.AppSpine Φ Ψ' Δ e acc rty := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    -- `exprFnRefs (.app fn arg) = exprFnRefs fn ++ exprFnRefs arg`; `harg`←arg, `hrest`←fn
    refine .app fn arg aty acc' rty (HasSimpType_restrict_Ψ ?_ harg) (AppSpine_restrict_Ψ ?_ hrest)
    · intro n hn; apply hsub n
      simp only [exprFnRefs]; exact List.mem_append_right _ hn
    · intro n hn; apply hsub n
      simp only [exprFnRefs]; exact List.mem_append_left _ hn
  | .fvar f t acc' rty hmem hcollect hbase =>
    exact .fvar f t acc' rty hmem hcollect hbase
  | .op o oty acc' rty hop hcollect =>
    exact .op o oty acc' rty hop hcollect
  | .fnOp o oty acc' rty hmem hnpre hcollect hbase =>
    -- the head name `o.name` is in `exprFnRefs (.op () o (some oty))` (since `¬IsPredefinedOp`)
    refine .fnOp o oty acc' rty (hsub o.name ?_ oty hmem) hnpre hcollect hbase
    simp only [exprFnRefs]
    rw [if_neg hnpre]
    exact List.mem_singleton.mpr rfl
termination_by structural hspine
end

/-- `OblProgramWFfrom` splits over `++`: a prefix-WF concatenation is prefix-WF on the head, and
    prefix-WF on the tail from the head-folded context. -/
theorem OblProgramWFfrom_append (a b : List OblCommand) (c : OblCtx) :
    OblProgramWFfrom (a ++ b) c ↔
      OblProgramWFfrom a c ∧ OblProgramWFfrom b (a.foldl OblCtx.step c) := by
  induction a generalizing c with
  | nil => simp [OblProgramWFfrom]
  | cons hd tl ih =>
    simp only [List.cons_append, OblProgramWFfrom, List.foldl_cons, ih, and_assoc]

/-- Membership in `procObligations` exposes the per-assert witness: `Q`'s commands are
    `obligationPrefix c fns ++ bpfx` and its obligation `ob`, for some `(bpfx, ob)` produced by
    the body fan-out and `fns` the reachable-ordered functions of that obligation's seeds. -/
theorem mem_procObligations {Q : OblProgram} {c : CoreCtx} {ss : Statements}
    (hQ : Q ∈ procObligations c ss) :
    ∃ (bpfx : List OblCommand) (ob : Expression.Expr),
      (bpfx, ob) ∈ bodyObligations [] ss ∧
      Q = ⟨obligationPrefix c (reachableOrdered c.F
            (exprFnRefs ob
              ++ bpfx.flatMap (fun | .assume e => exprFnRefs e | .varDef v => exprFnRefs v.body | _ => [])
              ++ c.axioms.flatMap exprFnRefs
              ++ c.distincts.flatMap (fun es => es.flatMap exprFnRefs))) ++ bpfx, ob⟩ := by
  simp only [procObligations, List.mem_map] at hQ
  obtain ⟨⟨bpfx, ob⟩, hmem, heq⟩ := hQ
  exact ⟨bpfx, ob, hmem, heq.symm⟩

/-- **The emitting procedure's prefix context is `declWF`.** Threads `Program.WFfrom` through the
    decl fold to the `.proc` that emitted `Q`: there is a prefix context `c'` at which the proc's
    body `ss` is preprocessed (`Statements.Preprocessed c'.Ψ [] ss`), every collected fn-axiom is
    bool-typed at `c'.Ψ`, and `Q ∈ procObligations c' ss`. This packages the fold bookkeeping so the
    per-obligation WF lemma can work at a single fixed context. -/
theorem toOblProgramsFrom_declWF {Q : OblProgram} :
    ∀ (decls : List Decl) (c : CoreCtx), Program.WFfrom decls c → c.Good → c.FactoryFuncsWF →
      c.SeedWF →
      Q ∈ toOblProgramsFrom decls c →
      ∃ (p : Procedure) (ss : Statements) (c' : CoreCtx),
        p.body = .structured ss ∧
        Statements.Preprocessed c'.Ψ [] ss ∧
        (∀ g ∈ reachableFuncs c'.F (c'.procSeeds ss), ∀ f, c'.F[g]? = some f →
          ∀ ax ∈ f.axioms, LExpr.HasSimpType [] c'.Ψ [] ax (.tcons "bool" [])) ∧
        c'.Good ∧ c'.FactoryFuncsWF ∧ c'.SeedWF ∧
        Q ∈ procObligations c' ss := by
  intro decls
  induction decls with
  | nil => intro c _ _ _ _ hQ; simp [toOblProgramsFrom] at hQ
  | cons d rest ih =>
    intro c hwf hgood hffwf hseed hQ
    obtain ⟨hdWF, hrestWF⟩ := hwf
    cases d with
    | proc p md =>
      cases hb : p.body with
      | structured ss =>
          simp only [toOblProgramsFrom, hb, List.mem_append] at hQ
          rcases hQ with hhere | htail
          · -- emitted at this proc; its `declWF` gives the body-preprocessed + fn-axiom facts
            rw [CoreCtx.declWF, hb] at hdWF
            obtain ⟨ss', hss'eq, hpre, hax⟩ := hdWF
            -- `.structured ss = .structured ss'` ⇒ `ss = ss'`
            cases hss'eq
            exact ⟨p, ss, c, hb, hpre, hax, hgood, hffwf, hseed, hhere⟩
          · exact ih (c.step (.proc p md)) hrestWF (hgood.step hdWF) (hffwf.step hdWF)
              (hseed.step _) htail
      | cfg _ =>
          simp only [toOblProgramsFrom, hb, List.nil_append] at hQ
          exact ih (c.step (.proc p md)) hrestWF (hgood.step hdWF) (hffwf.step hdWF)
            (hseed.step _) hQ
    | func f md =>
        simp only [toOblProgramsFrom, List.nil_append] at hQ
        exact ih (c.step (.func f md)) hrestWF (hgood.step hdWF) (hffwf.step hdWF)
          (hseed.step _) hQ
    | type t md =>
        simp only [toOblProgramsFrom, List.nil_append] at hQ
        exact ih (c.step (.type t md)) hrestWF (hgood.step hdWF) (hffwf.step hdWF)
          (hseed.step _) hQ
    | ax a md =>
        simp only [toOblProgramsFrom, List.nil_append] at hQ
        exact ih (c.step (.ax a md)) hrestWF (hgood.step hdWF) (hffwf.step hdWF) (hseed.step _) hQ
    | distinct n es md =>
        simp only [toOblProgramsFrom, List.nil_append] at hQ
        exact ih (c.step (.distinct n es md)) hrestWF (hgood.step hdWF) (hffwf.step hdWF)
          (hseed.step _) hQ
    | recFuncBlock b md =>
        simp only [toOblProgramsFrom, List.nil_append] at hQ
        exact ih (c.step (.recFuncBlock b md)) hrestWF (hgood.step hdWF) (hffwf.step hdWF)
          (hseed.step _) hQ

/-- **`bodyObligations` types its obligations (at the full proc `Ψ`).** Every emitted obligation
    `ob` from a preprocessed body is bool-typed at the full proc `Ψ` and some free-var context `Φ'`
    (the accumulated `Φ` at that `assert`). Straight induction on the `Preprocessed` derivation: the
    only obligation-producing case is `assert`, whose `hb` field is the typing; every other case
    recurses (`ite` fans into three sub-derivations, all at appropriate `Φ`). No reachability
    narrowing yet — applied per-`Q` afterward. -/
theorem bodyObligations_ob_typed {Ψ : FnCtx} :
    ∀ {Φ : FVarCtx} {ss : Statements}, Statements.Preprocessed Ψ Φ ss →
    ∀ (pfx : List OblCommand), (pfx.foldl OblCtx.step {}).Φ = Φ →
    ∀ bpfx ob, (bpfx, ob) ∈ bodyObligations pfx ss →
      LExpr.HasSimpType (bpfx.foldl OblCtx.step {}).Φ Ψ [] ob (.tcons "bool" []) := by
  intro Φ ss hpre
  induction hpre with
  | nil Φ => intro pfx _ bpfx ob hmem; simp [bodyObligations] at hmem
  | assume Φ l b md rest hb hrest ih =>
      intro pfx hpfxΦ bpfx ob hmem
      rw [bodyObligations] at hmem
      refine ih (pfx ++ [OblCommand.assume b]) ?_ bpfx ob hmem
      rw [List.foldl_append]; simpa [OblCtx.step] using hpfxΦ
  | assert Φ l b md rest hb hrest ih =>
      intro pfx hpfxΦ bpfx ob hmem
      rw [bodyObligations] at hmem
      rcases List.mem_cons.mp hmem with heq | htl
      · -- head pair `(pfx, b)`: `bpfx = pfx`, `ob = b`; `hb` types it at `Φ = pfx-folded Φ`
        rw [Prod.mk.injEq] at heq
        obtain ⟨hbpfx, hob⟩ := heq
        rw [hbpfx, hpfxΦ, hob]; exact hb
      · -- tail resumes from the same `pfx` (discharged asserts are not added to the path condition)
        exact ih pfx hpfxΦ bpfx ob htl
  | initDet Φ name ty mτ e md rest hmono he hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpfxΦ bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      refine ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]) ?_ bpfx ob hmem
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [OblCtx.step]; rw [hpfxΦ]
  | initNondet Φ name ty mτ md rest hmono hsimp hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpfxΦ bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      refine ih (pfx ++ [OblCommand.fvarDecl name.name mτ]) ?_ bpfx ob hmem
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [OblCtx.step]; rw [hpfxΦ]
  | ite Φ thenb elseb md rest hthen helse hrest ihthen ihelse ihrest =>
      intro pfx hpfxΦ bpfx ob hmem
      rw [bodyObligations] at hmem
      rcases List.mem_append.mp hmem with h | hr
      · rcases List.mem_append.mp h with ht | he'
        · exact ihthen pfx hpfxΦ bpfx ob ht
        · exact ihelse pfx hpfxΦ bpfx ob he'
      · exact ihrest pfx hpfxΦ bpfx ob hr

/-- The function refs carried by a single prefix command's body (`.assume`/`.varDef`; declarations
    and distincts contribute none here — they are handled by `emitFuncDecls`/globals). -/
def cmdBodyRefs : OblCommand → List String
  | .assume e => exprFnRefs e
  | .varDef v => exprFnRefs v.body
  | _         => []

/-- **`bodyObligations` only extends its prefix.** For a preprocessed body, every produced
    `(bpfx, ob)` has `bpfx = pfx ++ suffix` — the accumulator grows monotonically along the path to
    each assert. Proven over `Preprocessed` (so the `bodyObligations` fall-through never fires). Used
    to show each folded command is a command of the produced `bpfx` (hence its refs are seeds). -/
theorem bodyObligations_pfx_prefix {Ψ : FnCtx} {Φ : FVarCtx} {ss : Statements}
    (hpre : Statements.Preprocessed Ψ Φ ss) :
    ∀ (pfx : List OblCommand) bpfx ob, (bpfx, ob) ∈ bodyObligations pfx ss →
      ∃ suf, bpfx = pfx ++ suf := by
  induction hpre with
  | nil Φ => intro pfx bpfx ob hmem; simp [bodyObligations] at hmem
  | assume Φ l b md rest hb hrest ih =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      obtain ⟨suf, hsuf⟩ := ih (pfx ++ [OblCommand.assume b]) bpfx ob hmem
      exact ⟨[OblCommand.assume b] ++ suf, by rw [hsuf, List.append_assoc]⟩
  | assert Φ l b md rest hb hrest ih =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      rcases List.mem_cons.mp hmem with heq | htl
      · rw [Prod.mk.injEq] at heq; exact ⟨[], by rw [heq.1, List.append_nil]⟩
      · -- tail resumes from the same `pfx`
        exact ih pfx bpfx ob htl
  | initDet Φ name ty mτ e md rest hmono he hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      obtain ⟨suf, hsuf⟩ := ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]) bpfx ob hmem
      exact ⟨[OblCommand.varDef ⟨name.name, mτ, e⟩] ++ suf, by rw [hsuf, List.append_assoc]⟩
  | initNondet Φ name ty mτ md rest hmono hsimp hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      obtain ⟨suf, hsuf⟩ := ih (pfx ++ [OblCommand.fvarDecl name.name mτ]) bpfx ob hmem
      exact ⟨[OblCommand.fvarDecl name.name mτ] ++ suf, by rw [hsuf, List.append_assoc]⟩
  | ite Φ thenb elseb md rest hthen helse hrest ihthen ihelse ihrest =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      rcases List.mem_append.mp hmem with h | hr
      · rcases List.mem_append.mp h with ht | he'
        · exact ihthen pfx bpfx ob ht
        · exact ihelse pfx bpfx ob he'
      · exact ihrest pfx bpfx ob hr

/-- **A produced `bodyObligations` prefix has no `.distinct` command** (given the accumulator has
    none). The path accumulator only ever grows by `.assume`/`.varDef`/`.fvarDecl` (`initDecl`), so no
    `.distinct` is introduced. Used to show `Q`'s distinctness groups all originate in `obligationPrefix`'s
    global `c.distincts`, never in `bpfx`. -/
theorem bodyObligations_no_distinct {Ψ : FnCtx} {Φ : FVarCtx} {ss : Statements}
    (hpre : Statements.Preprocessed Ψ Φ ss) :
    ∀ (pfx : List OblCommand), (∀ es, OblCommand.distinct es ∉ pfx) →
      ∀ bpfx ob, (bpfx, ob) ∈ bodyObligations pfx ss →
      ∀ es, OblCommand.distinct es ∉ bpfx := by
  induction hpre with
  | nil Φ => intro pfx _ bpfx ob hmem; simp [bodyObligations] at hmem
  | assume Φ l b md rest hb hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      refine ih (pfx ++ [OblCommand.assume b]) (fun es hc => ?_) bpfx ob hmem
      rcases List.mem_append.mp hc with h | h
      · exact hpfx es h
      · rw [List.mem_singleton] at h; exact OblCommand.noConfusion h
  | assert Φ l b md rest hb hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      rcases List.mem_cons.mp hmem with heq | htl
      · rw [Prod.mk.injEq] at heq; rw [heq.1]; exact hpfx
      · -- tail resumes from the same `pfx`
        exact ih pfx hpfx bpfx ob htl
  | initDet Φ name ty mτ e md rest hmono he hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      refine ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]) (fun es hc => ?_) bpfx ob hmem
      rcases List.mem_append.mp hc with h | h
      · exact hpfx es h
      · rw [List.mem_singleton] at h; exact OblCommand.noConfusion h
  | initNondet Φ name ty mτ md rest hmono hsimp hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      refine ih (pfx ++ [OblCommand.fvarDecl name.name mτ]) (fun es hc => ?_) bpfx ob hmem
      rcases List.mem_append.mp hc with h | h
      · exact hpfx es h
      · rw [List.mem_singleton] at h; exact OblCommand.noConfusion h
  | ite Φ thenb elseb md rest hthen helse hrest ihthen ihelse ihrest =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      rcases List.mem_append.mp hmem with h | hr
      · rcases List.mem_append.mp h with ht | he'
        · exact ihthen pfx hpfx bpfx ob ht
        · exact ihelse pfx hpfx bpfx ob he'
      · exact ihrest pfx hpfx bpfx ob hr

/-- **`bodyObligations` prefixes contain no `.fnDef`.** The commands `bodyObligations` appends to the
    running prefix are only `.assume`/`.varDef`/`.fvarDecl` (path assumptions and `init` declarations) —
    never `.fnDef`. So any `.fnDef` in a produced `bpfx` must have been in the initial `pfx`; with
    `pfx = []` there are none. The `.fnDef`-analog of `bodyObligations_no_distinct`, routing every
    emitted `Q.defs` entry to the `obligationPrefix` (function-declaration) side of `Q.cmds`. -/
theorem bodyObligations_no_fnDef {Ψ : FnCtx} {Φ : FVarCtx} {ss : Statements}
    (hpre : Statements.Preprocessed Ψ Φ ss) :
    ∀ (pfx : List OblCommand), (∀ d, OblCommand.fnDef d ∉ pfx) →
      ∀ bpfx ob, (bpfx, ob) ∈ bodyObligations pfx ss →
      ∀ d, OblCommand.fnDef d ∉ bpfx := by
  induction hpre with
  | nil Φ => intro pfx _ bpfx ob hmem; simp [bodyObligations] at hmem
  | assume Φ l b md rest hb hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      refine ih (pfx ++ [OblCommand.assume b]) (fun d hc => ?_) bpfx ob hmem
      rcases List.mem_append.mp hc with h | h
      · exact hpfx d h
      · rw [List.mem_singleton] at h; exact OblCommand.noConfusion h
  | assert Φ l b md rest hb hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      rcases List.mem_cons.mp hmem with heq | htl
      · rw [Prod.mk.injEq] at heq; rw [heq.1]; exact hpfx
      · -- tail resumes from the same `pfx`
        exact ih pfx hpfx bpfx ob htl
  | initDet Φ name ty mτ e md rest hmono he hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      refine ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]) (fun d hc => ?_) bpfx ob hmem
      rcases List.mem_append.mp hc with h | h
      · exact hpfx d h
      · rw [List.mem_singleton] at h; exact OblCommand.noConfusion h
  | initNondet Φ name ty mτ md rest hmono hsimp hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      refine ih (pfx ++ [OblCommand.fvarDecl name.name mτ]) (fun d hc => ?_) bpfx ob hmem
      rcases List.mem_append.mp hc with h | h
      · exact hpfx d h
      · rw [List.mem_singleton] at h; exact OblCommand.noConfusion h
  | ite Φ thenb elseb md rest hthen helse hrest ihthen ihelse ihrest =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      rcases List.mem_append.mp hmem with h | hr
      · rcases List.mem_append.mp h with ht | he'
        · exact ihthen pfx hpfx bpfx ob ht
        · exact ihelse pfx hpfx bpfx ob he'
      · exact ihrest pfx hpfx bpfx ob hr

/-- **`bodyObligations` produces `cmdWF`-valid prefixes (at the narrowed `Ψ'`).** For a single
    produced `(bpfx, ob)`, folding `bpfx` from base `c₀` is `OblProgramWFfrom`-valid, given: the
    running Ψ stays `Ψ'` and Φ = the `Preprocessed` Φ (`hpfxΨ`/`hpfxΦ`); `Ψ'`-names ⊆ `Ψ`-names
    (`hΨsub`); the accumulated prefix is already WF (`hpfxWF`); and — the key per-path scoping —
    `hcov` narrows `Ψ → Ψ'` for exactly the refs of this `bpfx`'s own commands (`cmdBodyRefs`),
    discharged at the use site by `restrict_Ψ_side_condition` since `bpfx`'s bodies are seeds. Each
    folded command lies in `bpfx` (`bodyObligations_pfx_prefix`), so its refs are covered by `hcov`. -/
theorem bodyObligations_cmdsWF {Ψ Ψ' : FnCtx}
    (hΨsub : ∀ nm : String, nm ∈ Ψ'.map (·.1) → nm ∈ Ψ.map (·.1))
    (c₀ : OblCtx) :
    ∀ {Φ : FVarCtx} {ss : Statements}, Statements.Preprocessed Ψ Φ ss →
    ∀ (pfx : List OblCommand), OblProgramWFfrom pfx c₀ →
      (pfx.foldl OblCtx.step c₀).Φ = Φ → (pfx.foldl OblCtx.step c₀).Ψ = Ψ' →
    ∀ bpfx ob, (bpfx, ob) ∈ bodyObligations pfx ss →
      (∀ n ∈ bpfx.flatMap cmdBodyRefs, ∀ σ, (n, σ) ∈ Ψ → (n, σ) ∈ Ψ') →
      OblProgramWFfrom bpfx c₀ := by
  intro Φ ss hpre
  induction hpre with
  | nil Φ => intro pfx _ _ _ bpfx ob hmem _; simp [bodyObligations] at hmem
  | assume Φ l b md rest hb hrest ih =>
      intro pfx hpfxWF hpfxΦ hpfxΨ bpfx ob hmem hcov
      rw [bodyObligations] at hmem
      -- `.assume b` lies in `bpfx` (produced-prefix), so its refs are covered by `hcov`
      obtain ⟨suf, hsuf⟩ := bodyObligations_pfx_prefix hrest _ bpfx ob hmem
      have hbmem : OblCommand.assume b ∈ bpfx := by
        rw [hsuf, List.append_assoc]; exact List.mem_append_right _ (by simp)
      have hbstep : (pfx.foldl OblCtx.step c₀).cmdWF (OblCommand.assume b) := by
        show LExpr.HasSimpType (pfx.foldl OblCtx.step c₀).Φ (pfx.foldl OblCtx.step c₀).Ψ [] b _
        rw [hpfxΦ, hpfxΨ]
        refine HasSimpType_restrict_Ψ (fun n hn σ hσ => hcov n ?_ σ hσ) hb
        exact List.mem_flatMap.mpr ⟨_, hbmem, by rw [cmdBodyRefs]; exact hn⟩
      have hpfxWF' : OblProgramWFfrom (pfx ++ [OblCommand.assume b]) c₀ := by
        rw [OblProgramWFfrom_append]; exact ⟨hpfxWF, hbstep, trivial⟩
      refine ih (pfx ++ [OblCommand.assume b]) hpfxWF' ?_ ?_ bpfx ob hmem hcov
      · rw [List.foldl_append]; simpa [OblCtx.step] using hpfxΦ
      · rw [List.foldl_append]; simpa [OblCtx.step] using hpfxΨ
  | assert Φ l b md rest hb hrest ih =>
      intro pfx hpfxWF hpfxΦ hpfxΨ bpfx ob hmem hcov
      rw [bodyObligations] at hmem
      rcases List.mem_cons.mp hmem with heq | htl
      · -- head pair `(pfx, b)`: `bpfx = pfx`; WF is exactly `hpfxWF`
        rw [Prod.mk.injEq] at heq; rw [heq.1]; exact hpfxWF
      · -- tail resumes from the same `pfx` (the asserted `b` is not added to the prefix)
        exact ih pfx hpfxWF hpfxΦ hpfxΨ bpfx ob htl hcov
  | initDet Φ name ty mτ e md rest hmono he hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpfxWF hpfxΦ hpfxΨ bpfx ob hmem hcov
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      obtain ⟨suf, hsuf⟩ := bodyObligations_pfx_prefix hrest _ bpfx ob hmem
      have hvmem : OblCommand.varDef ⟨name.name, mτ, e⟩ ∈ bpfx := by
        rw [hsuf, List.append_assoc]; exact List.mem_append_right _ (by simp)
      -- extend pfx by `.varDef ⟨name,mτ,e⟩` (cmdWF: fresh name + `e : mτ` narrowed)
      have hvstep : (pfx.foldl OblCtx.step c₀).cmdWF (OblCommand.varDef ⟨name.name, mτ, e⟩) := by
        refine ⟨?_, hnres, ?_⟩
        · -- freshness: `name ∉ running names = Φ.map fst ++ Ψ'.map fst`
          show name.name ∉ (pfx.foldl OblCtx.step c₀).names
          rw [OblCtx.names, hpfxΦ, hpfxΨ, List.mem_append]
          rintro (h | h)
          · exact hfreshΦ h
          · exact hfreshΨ (hΨsub name.name h)
        · -- `VarDef.WFIn`: `e : mτ` at running ctx, narrowed
          show LExpr.HasSimpType (pfx.foldl OblCtx.step c₀).Φ (pfx.foldl OblCtx.step c₀).Ψ [] e mτ
          rw [hpfxΦ, hpfxΨ]
          refine HasSimpType_restrict_Ψ (fun n hn σ hσ => hcov n ?_ σ hσ) he
          exact List.mem_flatMap.mpr ⟨_, hvmem, by rw [cmdBodyRefs]; exact hn⟩
      have hpfxWF' : OblProgramWFfrom (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]) c₀ := by
        rw [OblProgramWFfrom_append]; exact ⟨hpfxWF, hvstep, trivial⟩
      refine ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]) hpfxWF' ?_ ?_ bpfx ob hmem hcov
      · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]; simp only [OblCtx.step]; rw [hpfxΦ]
      · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]; simp only [OblCtx.step]; rw [hpfxΨ]
  | initNondet Φ name ty mτ md rest hmono hsimp hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpfxWF hpfxΦ hpfxΨ bpfx ob hmem hcov
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      have hvstep : (pfx.foldl OblCtx.step c₀).cmdWF (OblCommand.fvarDecl name.name mτ) := by
        refine ⟨?_, hnres, hsimp⟩
        show name.name ∉ (pfx.foldl OblCtx.step c₀).names
        rw [OblCtx.names, hpfxΦ, hpfxΨ, List.mem_append]
        rintro (h | h)
        · exact hfreshΦ h
        · exact hfreshΨ (hΨsub name.name h)
      have hpfxWF' : OblProgramWFfrom (pfx ++ [OblCommand.fvarDecl name.name mτ]) c₀ := by
        rw [OblProgramWFfrom_append]; exact ⟨hpfxWF, hvstep, trivial⟩
      refine ih (pfx ++ [OblCommand.fvarDecl name.name mτ]) hpfxWF' ?_ ?_ bpfx ob hmem hcov
      · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]; simp only [OblCtx.step]; rw [hpfxΦ]
      · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]; simp only [OblCtx.step]; rw [hpfxΨ]
  | ite Φ thenb elseb md rest hthen helse hrest ihthen ihelse ihrest =>
      intro pfx hpfxWF hpfxΦ hpfxΨ bpfx ob hmem hcov
      rw [bodyObligations] at hmem
      rcases List.mem_append.mp hmem with h | hr
      · rcases List.mem_append.mp h with ht | he'
        · exact ihthen pfx hpfxWF hpfxΦ hpfxΨ bpfx ob ht hcov
        · exact ihelse pfx hpfxWF hpfxΦ hpfxΨ bpfx ob he' hcov
      · exact ihrest pfx hpfxWF hpfxΦ hpfxΨ bpfx ob hr hcov

/-- **`emitFuncDecls` leaves `Φ` unchanged.** Its commands are only `.fnDecl`/`.fnDef` (grow
    `Ψ`/`defs`), none touch `Φ`. -/
theorem foldl_emitFuncDecls_Φ (F : Lambda.Factory CoreLParams) (names : List String) (c : OblCtx) :
    ((emitFuncDecls F names).foldl OblCtx.step c).Φ = c.Φ := by
  unfold emitFuncDecls
  induction names generalizing c with
  | nil => simp [List.filterMap]
  | cons hd tl ih =>
      rw [List.filterMap_cons]
      cases F[hd]? with
      | none => simp only [Option.map_none]; exact ih c
      | some f =>
          simp only [Option.map_some, List.foldl_cons]
          rw [ih (c.step (emitFuncDecl f))]
          -- `emitFuncDecl f` is `.fnDef`/`.fnDecl`, both leave Φ unchanged
          unfold emitFuncDecl; split <;> simp [OblCtx.step]

theorem foldl_emitFuncAxioms_Φ (F : Lambda.Factory CoreLParams) (names : List String) (c : OblCtx) :
    ((emitFuncAxioms F names).foldl OblCtx.step c).Φ = c.Φ := by
  unfold emitFuncAxioms
  induction names generalizing c with
  | nil => simp
  | cons hd tl ih =>
      rw [List.flatMap_cons, List.foldl_append, ih]
      cases F[hd]? with
      | none => simp
      | some f =>
          simp only [Option.map_some, Option.getD_some, funcAxiomAssumes]
          -- each axiom is a `.assume`, leaving Φ unchanged
          induction f.axioms generalizing c with
          | nil => simp
          | cons a as iha => rw [List.map_cons, List.foldl_cons]; rw [iha]; simp [OblCtx.step]

/-- **A `.assume`/`.distinct`-only command list leaves `Φ` unchanged.** Used for the
    `c.distincts.map .distinct ++ c.axioms.map .assume` tail of `obligationPrefix`. -/
theorem foldl_assume_distinct_Φ : ∀ (cmds : List OblCommand) (c : OblCtx),
    (∀ cmd ∈ cmds, (∃ e, cmd = .assume e) ∨ (∃ es, cmd = .distinct es)) →
    (cmds.foldl OblCtx.step c).Φ = c.Φ := by
  intro cmds
  induction cmds with
  | nil => intro c _; rfl
  | cons hd tl ih =>
      intro c hcmds
      rw [List.foldl_cons, ih _ (fun cmd hc => hcmds cmd (List.mem_cons_of_mem hd hc))]
      rcases hcmds hd (List.mem_cons_self) with ⟨e, he⟩ | ⟨es, hes⟩
      · rw [he]; simp [OblCtx.step]
      · rw [hes]; simp [OblCtx.step]

/-- **`obligationPrefix` leaves `Φ` unchanged** — it declares functions and asserts axioms/distincts,
    none of which touch `Φ`. So `Q.Φ` is determined entirely by the body prefix `bpfx`. -/
theorem foldl_obligationPrefix_Φ (c : CoreCtx) (fns : List String) (base : OblCtx) :
    ((obligationPrefix c fns).foldl OblCtx.step base).Φ = base.Φ := by
  unfold obligationPrefix
  rw [List.foldl_append, List.foldl_append, List.foldl_append]
  rw [foldl_assume_distinct_Φ (c.axioms.map OblCommand.assume) _
        (fun cmd hc => by obtain ⟨e, _, he⟩ := List.mem_map.mp hc; exact Or.inl ⟨e, he.symm⟩)]
  rw [foldl_assume_distinct_Φ (c.distincts.map OblCommand.distinct) _
        (fun cmd hc => by obtain ⟨es, _, hes⟩ := List.mem_map.mp hc; exact Or.inr ⟨es, hes.symm⟩)]
  rw [foldl_emitFuncAxioms_Φ, foldl_emitFuncDecls_Φ]

/-- **`emitFuncDecls` only adds factory-function names to `Ψ`.** Each `emitFuncDecl f` (for a
    resolved `g`) contributes name `f.name.name = g ∈ factoryNames F`. So every `Ψ`-name after the
    fold is either a base name or a factory node name. -/
theorem foldl_emitFuncDecls_Ψ_names (F : Lambda.Factory CoreLParams) :
    ∀ (names : List String) (c : OblCtx) (nm : String),
      nm ∈ ((emitFuncDecls F names).foldl OblCtx.step c).Ψ.map (·.1) →
      nm ∈ c.Ψ.map (·.1) ∨ nm ∈ factoryNames F := by
  intro names
  induction names with
  | nil => intro c nm h; left; simpa [emitFuncDecls, List.filterMap] using h
  | cons hd tl ih =>
      intro c nm h
      rw [emitFuncDecls, List.filterMap_cons] at h
      cases hhd : F[hd]? with
      | none => rw [hhd] at h; simp only [Option.map_none] at h; exact ih c nm h
      | some f =>
          rw [hhd] at h; simp only [Option.map_some, List.foldl_cons] at h
          -- fold over `tl` from `c.step (emitFuncDecl f)`
          rcases ih (c.step (emitFuncDecl f)) nm h with h' | h'
          · -- `nm` in stepped Ψ = c.Ψ ++ [funcSig f]; either base or `f.name.name` (a node)
            rw [step_emitFuncDecl_Ψ] at h'
            simp only [List.map_append, List.mem_append] at h'
            rcases h' with hbase | hf
            · left; exact hbase
            · right
              simp only [List.map_cons, List.map_nil, List.mem_singleton] at hf
              -- `nm = (funcSig f).1 = f.name.name`; `f = F[hd]` so its name is a factory node
              rw [hf]
              have : f.name.name = hd := Factory.getElem?_name hhd
              simp only [factoryNames, List.mem_map]
              exact ⟨f, Array.mem_def.mp (Factory.getElem?_is_some_implies_mem hhd), by rw [funcSig]⟩
          · right; exact h'

/-- **`emitFuncAxioms`/`.assume`/`.distinct` commands leave `Ψ` unchanged** (they grow only
    assertions), so folding them preserves `Ψ`-names. -/
theorem foldl_emitFuncAxioms_Ψ (F : Lambda.Factory CoreLParams) (names : List String) (c : OblCtx) :
    ((emitFuncAxioms F names).foldl OblCtx.step c).Ψ = c.Ψ := by
  unfold emitFuncAxioms
  induction names generalizing c with
  | nil => simp
  | cons hd tl ih =>
      rw [List.flatMap_cons, List.foldl_append, ih]
      cases F[hd]? with
      | none => simp
      | some f =>
          simp only [Option.map_some, Option.getD_some, funcAxiomAssumes]
          induction f.axioms generalizing c with
          | nil => simp
          | cons a as iha => rw [List.map_cons, List.foldl_cons]; rw [iha]; simp [OblCtx.step]

theorem foldl_assume_distinct_Ψ : ∀ (cmds : List OblCommand) (c : OblCtx),
    (∀ cmd ∈ cmds, (∃ e, cmd = .assume e) ∨ (∃ es, cmd = .distinct es)) →
    (cmds.foldl OblCtx.step c).Ψ = c.Ψ := by
  intro cmds
  induction cmds with
  | nil => intro c _; rfl
  | cons hd tl ih =>
      intro c hcmds
      rw [List.foldl_cons, ih _ (fun cmd hc => hcmds cmd (List.mem_cons_of_mem hd hc))]
      rcases hcmds hd (List.mem_cons_self) with ⟨e, he⟩ | ⟨es, hes⟩
      · rw [he]; simp [OblCtx.step]
      · rw [hes]; simp [OblCtx.step]

/-- **`obligationPrefix`'s `Ψ`-names are all factory-function names** (from the empty base): the
    emitted declarations name only reachable factory functions; axioms/distincts don't touch `Ψ`. -/
theorem foldl_obligationPrefix_Ψ_names (c : CoreCtx) (fns : List String) (nm : String)
    (hnm : nm ∈ ((obligationPrefix c fns).foldl OblCtx.step {}).Ψ.map (·.1)) :
    nm ∈ factoryNames c.F := by
  unfold obligationPrefix at hnm
  rw [List.foldl_append, List.foldl_append, List.foldl_append] at hnm
  rw [foldl_assume_distinct_Ψ (c.axioms.map OblCommand.assume) _
        (fun cmd hc => by obtain ⟨e, _, he⟩ := List.mem_map.mp hc; exact Or.inl ⟨e, he.symm⟩)] at hnm
  rw [foldl_assume_distinct_Ψ (c.distincts.map OblCommand.distinct) _
        (fun cmd hc => by obtain ⟨es, _, hes⟩ := List.mem_map.mp hc; exact Or.inr ⟨es, hes.symm⟩)] at hnm
  rw [foldl_emitFuncAxioms_Ψ] at hnm
  rcases foldl_emitFuncDecls_Ψ_names c.F fns {} nm hnm with h | h
  · simp at h
  · exact h

/-- **`Φ`-fold depends only on the starting `Φ`.** `OblCtx.step`'s effect on `Φ` is a function of
    the current `Φ` and the command alone (not the other fields), so folding the same commands from
    two contexts that agree on `Φ` yields the same final `Φ`. -/
theorem foldl_step_Φ_congr : ∀ (cmds : List OblCommand) (c₁ c₂ : OblCtx), c₁.Φ = c₂.Φ →
    (cmds.foldl OblCtx.step c₁).Φ = (cmds.foldl OblCtx.step c₂).Φ := by
  intro cmds
  induction cmds with
  | nil => intro c₁ c₂ h; exact h
  | cons hd tl ih =>
      intro c₁ c₂ h
      rw [List.foldl_cons, List.foldl_cons]
      refine ih (c₁.step hd) (c₂.step hd) ?_
      cases hd <;> simp only [OblCtx.step] <;> rw [h]

/-- **`.assume`-mapped list is WF** given each expr bool-types at the base `Φ`/`Ψ` (which stays
    constant since `.assume` grows only assertions). -/
theorem OblProgramWFfrom_assume_map (es : List Expression.Expr) (base : OblCtx)
    (hty : ∀ e ∈ es, LExpr.HasSimpType base.Φ base.Ψ [] e (.tcons "bool" [])) :
    OblProgramWFfrom (es.map OblCommand.assume) base := by
  induction es generalizing base with
  | nil => trivial
  | cons hd tl ih =>
      rw [List.map_cons, OblProgramWFfrom]
      refine ⟨hty hd (by simp), ?_⟩
      -- `.assume hd` leaves Φ/Ψ unchanged, so the tail's typing hypothesis transports
      have hstep : (base.step (OblCommand.assume hd)).Φ = base.Φ ∧
                   (base.step (OblCommand.assume hd)).Ψ = base.Ψ := by
        constructor <;> simp [OblCtx.step]
      exact ih (base.step (OblCommand.assume hd))
        (fun e he => by rw [hstep.1, hstep.2]; exact hty e (by simp [he]))

/-- **`.distinct`-mapped list is WF** given each group is `≥2` and shares one base type at the base
    `Φ`/`Ψ` (constant since `.distinct` grows only assertions). -/
theorem OblProgramWFfrom_distinct_map (gs : List (List Expression.Expr)) (base : OblCtx)
    (hty : ∀ es ∈ gs, 2 ≤ es.length ∧
      ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es, LExpr.HasSimpType base.Φ base.Ψ [] e τ) :
    OblProgramWFfrom (gs.map OblCommand.distinct) base := by
  induction gs generalizing base with
  | nil => trivial
  | cons hd tl ih =>
      rw [List.map_cons, OblProgramWFfrom]
      refine ⟨hty hd (by simp), ?_⟩
      have hstep : (base.step (OblCommand.distinct hd)).Φ = base.Φ ∧
                   (base.step (OblCommand.distinct hd)).Ψ = base.Ψ := by
        constructor <;> simp [OblCtx.step]
      exact ih (base.step (OblCommand.distinct hd))
        (fun es hes => by rw [hstep.1, hstep.2]; exact hty es (by simp [hes]))

/-- **Narrow a body typed at the proc `Ψ` to the emitted `Ψ`.** A term `e` bool/base-typed at the
    full `fnCtx c.F` whose non-predefined heads (`exprFnRefs e`) are all `seeds` retypes at the
    obligation prefix's emitted `Ψ` — the reachability keystone specialized to `[]` extra and lifted
    across `HasSimpType_restrict_Ψ`. -/
theorem HasSimpType_narrow_to_emitted (c : CoreCtx) (seeds : List String)
    {e : Expression.Expr} {τ : LMonoTy}
    (hrefs : ∀ n ∈ exprFnRefs e, n ∈ seeds)
    (hty : LExpr.HasSimpType [] (Lambda.Factory.fnCtx c.F) [] e τ) :
    LExpr.HasSimpType []
      ((obligationPrefix c (reachableOrdered c.F seeds)).foldl OblCtx.step {}).Ψ [] e τ := by
  refine HasSimpType_restrict_Ψ (fun n hn σ hσ => ?_) hty
  have := restrict_Ψ_side_condition c seeds [] e hrefs n hn σ hσ
  rwa [List.append_nil] at this

/-- **Narrow to the emitted `Ψ` given refs already reachable.** Variant of
    `HasSimpType_narrow_to_emitted` whose side condition is `exprFnRefs e ⊆ reachableOrdered c.F seeds`
    (already-reachable, not just seeds) — the shape needed when `e` is a reachable function's axiom,
    whose refs are `funcDeps`-reachable by closure rather than original obligation seeds. -/
theorem HasSimpType_narrow_to_emitted_reachable (c : CoreCtx) (seeds : List String)
    {e : Expression.Expr} {τ : LMonoTy}
    (hrefs : ∀ n ∈ exprFnRefs e, n ∈ reachableOrdered c.F seeds)
    (hty : LExpr.HasSimpType [] (Lambda.Factory.fnCtx c.F) [] e τ) :
    LExpr.HasSimpType []
      ((obligationPrefix c (reachableOrdered c.F seeds)).foldl OblCtx.step {}).Ψ [] e τ := by
  refine HasSimpType_restrict_Ψ (fun n hn σ hσ => ?_) hty
  -- `(n,σ) ∈ fnCtx c.F` resolves; `n ∈ reachableOrdered` ⇒ `funcSig` in emitted `Ψ`
  obtain ⟨f, hres, hfsig, _⟩ := mem_fnCtx_resolves c.F hσ
  have := funcSig_mem_obligationPrefix_Ψ c (reachableOrdered c.F seeds) [] (hrefs n hn) hres
  rw [hfsig, List.append_nil] at this
  exact this

/-- **Any obligation-prefix suffix built from the same `fns` folds to the same `Ψ`.** Concretely the
    partial folds `emitFuncDecls ++ emitFuncAxioms` and `… ++ distincts.map` have the same `Ψ` as the
    full `obligationPrefix` — the `emitFuncAxioms`/distinct/axiom tail only grows assertions. Stated
    as: for a suffix `tl` of only-assume/distinct commands, `(pre ++ tl).foldl {}` and `pre.foldl {}`
    agree on `Ψ`. -/
theorem foldl_prefix_Ψ_eq (pre tl : List OblCommand)
    (htl : ∀ cmd ∈ tl, (∃ e, cmd = .assume e) ∨ (∃ es, cmd = .distinct es)) :
    ((pre ++ tl).foldl OblCtx.step {}).Ψ = (pre.foldl OblCtx.step ({} : OblCtx)).Ψ := by
  rw [List.foldl_append, foldl_assume_distinct_Ψ tl _ htl]

/-- The `emitFuncAxioms`/distinct/axiom tail commands are all `.assume`/`.distinct`. Convenience
    membership discharger for `foldl_prefix_Ψ_eq`/`foldl_assume_distinct_*`. -/
theorem obligationPrefix_tail_assume_distinct (c : CoreCtx) (fns : List String) :
    ∀ cmd ∈ emitFuncAxioms c.F fns ++ c.distincts.map OblCommand.distinct
              ++ c.axioms.map OblCommand.assume,
      (∃ e, cmd = .assume e) ∨ (∃ es, cmd = .distinct es) := by
  intro cmd hc
  rcases List.mem_append.mp hc with h | h
  · rcases List.mem_append.mp h with h' | h'
    · -- emitFuncAxioms = flatMap of `funcAxiomAssumes` = `.assume`s
      obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp h'
      rcases hgc : c.F[g]? with _ | f
      · rw [hgc] at hg; simp at hg
      · rw [hgc] at hg; simp only [Option.map_some, Option.getD_some, funcAxiomAssumes] at hg
        obtain ⟨x, _, hx⟩ := List.mem_map.mp hg; exact Or.inl ⟨x, hx.symm⟩
    · obtain ⟨es, _, hes⟩ := List.mem_map.mp h'; exact Or.inr ⟨es, hes.symm⟩
  · obtain ⟨e, _, he⟩ := List.mem_map.mp h; exact Or.inl ⟨e, he.symm⟩

/-- **The global-axiom/distinct tail of `obligationPrefix` is WF.** With `fns = reachableOrdered c.F
    seeds`, and given the accumulated `c.Good` (axioms/distincts typed at `c.Ψ = fnCtx c.F`) plus
    seed-coverage of their refs, the `distincts.map ++ axioms.map` tail is `OblProgramWFfrom` from any
    base whose `Ψ` is the emitted `obligationPrefix`-`Ψ` and `Φ = []`. Each element narrows from
    `c.Ψ` to the emitted `Ψ` via `HasSimpType_narrow_to_emitted`. -/
theorem obligationPrefix_globals_WF (c : CoreCtx) (seeds : List String) (base : OblCtx)
    (hbΦ : base.Φ = [])
    (hbΨ : base.Ψ = ((obligationPrefix c (reachableOrdered c.F seeds)).foldl OblCtx.step {}).Ψ)
    (hgood : c.Good)
    (hAxSeed : ∀ e ∈ c.axioms, ∀ n ∈ exprFnRefs e, n ∈ seeds)
    (hDistSeed : ∀ es ∈ c.distincts, ∀ e ∈ es, ∀ n ∈ exprFnRefs e, n ∈ seeds) :
    OblProgramWFfrom (c.distincts.map OblCommand.distinct ++ c.axioms.map OblCommand.assume) base := by
  rw [OblProgramWFfrom_append]
  refine ⟨?_, ?_⟩
  · -- distincts: `hgood.2` gives typing at `c.Ψ = fnCtx c.F`; narrow to emitted `Ψ = base.Ψ`
    apply OblProgramWFfrom_distinct_map
    intro es hes
    obtain ⟨hlen, τ, hbase, hty⟩ := hgood.2 es hes
    refine ⟨hlen, τ, hbase, fun e he => ?_⟩
    rw [hbΦ, hbΨ]
    exact HasSimpType_narrow_to_emitted c seeds
      (fun n hn => hDistSeed es hes e he n hn) (hty e he)
  · -- axioms: dual, `hgood.1` at `c.Ψ` narrowed. Base after distincts still has `Φ=[]`, `Ψ=base.Ψ`.
    have hbase2Φ : ((c.distincts.map OblCommand.distinct).foldl OblCtx.step base).Φ = [] := by
      rw [foldl_assume_distinct_Φ _ _ (fun cmd hc => by
        obtain ⟨x,_,hx⟩ := List.mem_map.mp hc; exact Or.inr ⟨x, hx.symm⟩), hbΦ]
    have hbase2Ψ : ((c.distincts.map OblCommand.distinct).foldl OblCtx.step base).Ψ = base.Ψ :=
      foldl_assume_distinct_Ψ _ _ (fun cmd hc => by
        obtain ⟨x,_,hx⟩ := List.mem_map.mp hc; exact Or.inr ⟨x, hx.symm⟩)
    apply OblProgramWFfrom_assume_map
    intro e he
    rw [hbase2Φ, hbase2Ψ, hbΨ]
    exact HasSimpType_narrow_to_emitted c seeds
      (fun n hn => hAxSeed e he n hn) (hgood.1 e he)

/-- `reachableOrdered` is duplicate-free — it filters the nodup `factoryNames F`. -/
theorem reachableOrdered_nodup (F : Lambda.Factory CoreLParams) (seeds : List String) :
    (reachableOrdered F seeds).Nodup :=
  (Factory.name_nodup F).filter _

/-- Every `reachableOrdered` name is a factory node (it is filtered from `factoryNames F`). -/
theorem reachableOrdered_mem_factoryNames (F : Lambda.Factory CoreLParams) (seeds : List String)
    {g : String} (hg : g ∈ reachableOrdered F seeds) : g ∈ factoryNames F :=
  (List.mem_filter.mp hg).1

/-- **The signature/body-typing content of `emitFuncDecl f`'s `cmdWF`, minus name freshness.**
    The deferred per-function obligation — everything `OblCtx.cmdWF (emitFuncDecl f)` requires except
    the `name ∉ c.names` freshness (which the fold proves for real from `reachableOrdered`-nodup):
      • non-reserved name (`≠ "$__bv{n}"`);
      • `fnDecl`: signature `MonoTyIsSimp`;
      • `fnDef`: base `argTys` (`d.WF`) + body types at `c.Φ`/`c.Ψ` (`d.WFIn`) — the latter is where
        the topological callees-precede order (connector 1c) is needed, since `c.Ψ` is the emitted
        prefix so far. Stated at an arbitrary `c` (the emitting fold instantiates it at the running
        prefix). -/
def emitFuncDeclTyped (c : OblCtx) (f : LFunc CoreLParams) : Prop :=
  match emitFuncDecl f with
  | .fnDecl name sig => (∀ n : Nat, name ≠ s!"$__bv{n}") ∧ LExpr.MonoTyIsSimp sig
  | .fnDef d => (∀ n : Nat, d.name ≠ s!"$__bv{n}") ∧ d.WF ∧ d.WFIn c.Φ c.Ψ
  | _ => True

/-- **`funcBvarSubst`'s replacement values are all ref-free** (each is a `.bvar () i`, whose
    `exprFnRefs` is `[]`). Feeds `exprFnRefs_substFvarsLifting`'s ref-free-values hypothesis. -/
theorem funcBvarSubst_refs_nil (f : LFunc CoreLParams) :
    ∀ k v, (funcBvarSubst f).find? k = some v → exprFnRefs v = [] := by
  intro k v hfind
  -- `(k, v) ∈ funcBvarSubst f = (range …).map (fun i => (key i, .bvar () i))`, so `v = .bvar () i`
  have hmem : (k, v) ∈ ((List.range f.inputs.length).map
      (fun i => (f.inputs.keys[i]!, (LExpr.bvar () i : Expression.Expr)))) := by
    have := Map.find?_mem _ k v hfind
    rw [funcBvarSubst_eq_map] at this
    exact this
  obtain ⟨i, _, heq⟩ := List.mem_map.mp hmem
  rw [Prod.mk.injEq] at heq
  rw [← heq.2]  -- `v = .bvar () i`
  rfl

/-- `liftBVars` preserves `exprFnRefs` (it only shifts `.bvar` indices; `.op`/`.const`/`.fvar` are
    untouched, structural elsewhere). -/
theorem exprFnRefs_liftBVars (n : Nat) : ∀ (e : Expression.Expr) (cutoff : Nat),
    exprFnRefs (LExpr.liftBVars n e cutoff) = exprFnRefs e := by
  intro e
  induction e with
  | const _ _ => intro _; rfl
  | op _ _ _ => intro _; rfl
  | bvar _ _ => intro cutoff; unfold LExpr.liftBVars; split <;> rfl
  | fvar _ _ _ => intro _; rfl
  | abs _ _ _ _ ih => intro cutoff; simp only [LExpr.liftBVars, exprFnRefs]; exact ih _
  | quant _ _ _ _ _ _ ihtr ih => intro cutoff; simp only [LExpr.liftBVars, exprFnRefs]; rw [ihtr, ih]
  | app _ _ _ ih1 ih2 => intro cutoff; simp only [LExpr.liftBVars, exprFnRefs]; rw [ih1, ih2]
  | ite _ _ _ _ ih1 ih2 ih3 => intro cutoff; simp only [LExpr.liftBVars, exprFnRefs]; rw [ih1, ih2, ih3]
  | eq _ _ _ ih1 ih2 => intro cutoff; simp only [LExpr.liftBVars, exprFnRefs]; rw [ih1, ih2]

/-- **`substFvarsLifting` with bvar-only replacements preserves `exprFnRefs`.** The formal→bvar
    substitution only rewrites matched `.fvar` formals to (lifted) `.bvar`s — which carry no function
    refs — and leaves `.op` heads and structure intact. So the emitted `fnDef` body references exactly
    the same functions as the source body. Lets the `Ψ`-restriction side condition transfer across the
    fvar→bvar lift (`exprFnRefs (emitted body) = exprFnRefs body`). -/
theorem exprFnRefs_substFvarsLifting (body : Expression.Expr)
    (sm : Map CoreLParams.Identifier Expression.Expr)
    (hrefs : ∀ k v, sm.find? k = some v → exprFnRefs v = []) :
    exprFnRefs (LExpr.substFvarsLifting body sm) = exprFnRefs body := by
  unfold LExpr.substFvarsLifting
  split
  · rfl
  · -- non-empty: induct on `go body 0`; the `.fvar` case substitutes a ref-free (lifted) value
    suffices h : ∀ (e : Expression.Expr) (depth : Nat),
        exprFnRefs (LExpr.substFvarsLifting.go sm e depth) = exprFnRefs e from h body 0
    intro e
    induction e with
    | const _ _ => intro _; rfl
    | op _ _ _ => intro _; rfl
    | bvar _ _ => intro _; rfl
    | fvar _ name _ =>
        intro depth
        unfold LExpr.substFvarsLifting.go
        split
        · rename_i to hfind
          rw [exprFnRefs_liftBVars, hrefs _ _ hfind]; rfl
        · rfl
    | abs _ _ _ _ ih => intro depth; simp only [LExpr.substFvarsLifting.go, exprFnRefs]; exact ih _
    | quant _ _ _ _ _ _ ihtr ih =>
        intro depth; simp only [LExpr.substFvarsLifting.go, exprFnRefs]; rw [ihtr, ih]
    | app _ _ _ ih1 ih2 =>
        intro depth; simp only [LExpr.substFvarsLifting.go, exprFnRefs]; rw [ih1, ih2]
    | ite _ _ _ _ ih1 ih2 ih3 =>
        intro depth; simp only [LExpr.substFvarsLifting.go, exprFnRefs]; rw [ih1, ih2, ih3]
    | eq _ _ _ ih1 ih2 =>
        intro depth; simp only [LExpr.substFvarsLifting.go, exprFnRefs]; rw [ih1, ih2]

/-- **`Map.find?` returns the value at a nodup-key index.** If `l`'s first components are nodup and
    `l[j]? = some (a, b)`, then `Map.find? l a = some b` — the (unique) key `a` first occurs at `j`. -/
theorem Map_find?_getElem_of_nodup {α β} [DecidableEq α] :
    ∀ (l : List (α × β)), (l.map Prod.fst).Nodup → ∀ {j : Nat} {a : α} {b : β},
      l[j]? = some (a, b) → Map.find? l a = some b := by
  intro l
  induction l with
  | nil => intro _ j a b hj; simp only [List.getElem?_nil, reduceCtorEq] at hj
  | cons hd tl ih =>
    intro hnd j a b hj
    obtain ⟨a0, b0⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hnd
    cases j with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        simp only [Map.find?, if_pos]
    | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        have ha_mem : a ∈ tl.map Prod.fst :=
          List.mem_map.mpr ⟨(a, b), List.mem_of_getElem? hj, rfl⟩
        have hne : a0 ≠ a := fun h => hnd.1 (h ▸ ha_mem)
        simp only [Map.find?, if_neg hne]
        exact ih hnd.2 hj

/-- **A formal-variable reference aligns with its bvar substitution and value type.** Given a formal
    `(g.name, τ) ∈ funcFVarCtx f` with distinct formal keys, there is an index `i` such that the
    fvar→bvar map sends `g` to `.bvar () i` and `f.inputs.values[i]? = some τ`. Bridges the fvar
    context `funcFVarCtx f` (name↦type) to the bvar substitution `funcBvarSubst f` (identifier↦index)
    and the resulting bvar context `f.inputs.values`. -/
theorem formal_align (f : LFunc CoreLParams) (g : CoreLParams.Identifier) (τ : LMonoTy)
    (hkeys : f.inputs.keys.Nodup) (hmem : (g.name, τ) ∈ funcFVarCtx f) :
    ∃ i, Map.find? (funcBvarSubst f) g = some (LExpr.bvar () i) ∧
      f.inputs.values[i]? = some τ := by
  -- `funcFVarCtx f = inputs.map (id,ty)↦(id.name,ty)`; `(g.name,τ)` comes from entry `i`.
  simp only [funcFVarCtx, ListMap.toList, List.mem_map, Prod.mk.injEq] at hmem
  obtain ⟨⟨id, ty⟩, hin, hidname, hty⟩ := hmem
  subst hty
  -- locate `(id, ty)` at some index `i` in `f.inputs`
  obtain ⟨i, hi_lt, hget⟩ := List.mem_iff_getElem.mp hin
  -- work on the underlying `List` (`ListMap` is `List` by definition)
  have hget? : (f.inputs.toList)[i]? = some (id, ty) := by
    rw [List.getElem?_eq_getElem (l := f.inputs.toList) hi_lt]; exact congrArg some hget
  -- `keys = toList.map Prod.fst`, `values = toList.map Prod.snd`
  have hkeysd : f.inputs.keys = f.inputs.toList.map Prod.fst := ListMap.keys_eq_map_fst _
  have hvalsd : f.inputs.values = f.inputs.toList.map Prod.snd := ListMap.values_eq_map_snd _
  refine ⟨i, ?_, ?_⟩
  · -- `funcBvarSubst f` at key `g`: `g = id` (same name, Unit metadata) `= keys[i]`; nodup ⇒ `.bvar i`
    have hki : f.inputs.keys[i]? = some id := by rw [hkeysd, List.getElem?_map, hget?]; rfl
    have hkeysi : f.inputs.keys[i]! = g := by
      have : f.inputs.keys[i]! = id := by rw [List.getElem!_eq_getElem?_getD, hki]; rfl
      rw [this]; cases g; cases id; simp_all
    have hn : i < f.inputs.length := hi_lt
    rw [funcBvarSubst_eq_map]
    apply Map_find?_getElem_of_nodup
    · -- first components = `(range n).map (keys[·]!)` = `keys` (nodup)
      rw [List.map_map]
      have heq : (List.range f.inputs.length).map
          (Prod.fst ∘ fun i => (f.inputs.keys[i]!, (LExpr.bvar () i : Expression.Expr)))
          = f.inputs.keys := by
        apply List.ext_getElem
        · rw [List.length_map, List.length_range, ListMap.keys.length]
        · intro k hk1 hk2
          rw [List.length_map, List.length_range] at hk1
          simp only [List.getElem_map, List.getElem_range, Function.comp]
          rw [List.getElem!_eq_getElem?_getD]
          rw [show f.inputs.keys[k]? = some f.inputs.keys[k] from
            List.getElem?_eq_getElem (by rw [ListMap.keys.length]; exact hk1)]
          rfl
      rw [heq]; exact hkeys
    · -- the `i`-th entry of the range-map list
      rw [List.getElem?_map, List.getElem?_range hn]
      simp only [Option.map_some, Option.some.injEq]
      rw [hkeysi]
  · -- `values[i]? = some ty`
    rw [hvalsd, List.getElem?_map, hget?]; rfl

/-- A formal `(n, τ) ∈ funcFVarCtx f` has its type among the input value types. -/
theorem mem_funcFVarCtx_mem_values {f : LFunc CoreLParams} {n : String} {τ : LMonoTy}
    (hmem : (n, τ) ∈ funcFVarCtx f) : τ ∈ f.inputs.values := by
  simp only [funcFVarCtx, ListMap.toList, List.mem_map, Prod.mk.injEq] at hmem
  obtain ⟨⟨id, ty⟩, hin, _, hty⟩ := hmem
  subst hty
  rw [ListMap.values_eq_map_snd]
  exact List.mem_map.mpr ⟨(id, ty), hin, rfl⟩

/-- **A formal fvar's declared type is base**, hence its arrow decomposition is nullary. Feeds both
    the `.fvarNullary` transport (fvar → bvar) and the vacuous `AppSpine.fvar`-with-args case. -/
theorem funcFVarCtx_collectArrowTy_nil {f : LFunc CoreLParams} {n : String} {τ : LMonoTy}
    (hinbase : ∀ t ∈ f.inputs.values, LExpr.MonoTyIsBase t) (hmem : (n, τ) ∈ funcFVarCtx f) :
    collectArrowTy τ = ([], τ) := by
  have hb := hinbase τ (mem_funcFVarCtx_mem_values hmem)
  cases hb <;> rfl

mutual
/-- **`.go`-level transport of `HasSimpType` across the formal fvar→bvar substitution** (mutual with
    `fnDef_body_spine_go`). Threads an arbitrary outer bvar context `Δ` at `depth = Δ.length`: a body
    typed at `(funcFVarCtx f, Ψ', Δ)` has its substituted form `substFvarsLifting.go (funcBvarSubst f)
    body Δ.length` typed at `([], Ψ', Δ ++ f.inputs.values)`, same type. A formal fvar (base ⟹
    nullary) becomes `.bvar (i + Δ.length)`, typed against the appended `f.inputs.values`. -/
theorem fnDef_body_go {Ψ' : FnCtx} (f : LFunc CoreLParams)
    (hkeys : f.inputs.keys.Nodup)
    (hinbase : ∀ t ∈ f.inputs.values, LExpr.MonoTyIsBase t)
    {Δ : BVarCtx} {e : Expression.Expr} {τ : LMonoTy}
    (hty : LExpr.HasSimpType (funcFVarCtx f) Ψ' Δ e τ) :
    LExpr.HasSimpType [] Ψ' (Δ ++ f.inputs.values)
      (LExpr.substFvarsLifting.go (funcBvarSubst f) e Δ.length) τ := by
  match hty with
  | .const c hbase =>
      simp only [LExpr.substFvarsLifting.go]; exact .const c hbase
  | .bvar i t hlook hbase =>
      -- original bvar points into `Δ`; unchanged by `go`, still resolves in `Δ ++ vals`
      have hlt : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
      simp only [LExpr.substFvarsLifting.go]
      exact .bvar i t (by rw [List.getElem?_append_left hlt]; exact hlook) hbase
  | .app fn arg rty hspine =>
      -- peel the outer `.app`: `hspine : AppSpine (.app fn arg) [] rty` from an inner
      -- `AppSpine fn [aty] rty` and `HasSimpType arg aty`; recurse (spine on the nonempty `[aty]`).
      match hspine with
      | .app _ _ aty [] rty' harg hrest =>
          simp only [LExpr.substFvarsLifting.go]
          have harg' := fnDef_body_go f hkeys hinbase harg
          have hrest' := fnDef_body_spine_go f hkeys hinbase (show aty :: [] ≠ [] by simp) hrest
          exact .app _ _ rty'
            (LExpr.AppSpine.app _ _ aty [] rty' harg' hrest')
  | .fvarNullary fv τ rty hspine =>
      -- a formal fvar (nullary, base): substitute to a bvar `.bvar (i + Δ.length)`
      match hspine with
      | .fvar fv τ acc rty hmem hcollect hbase =>
          have hnil := funcFVarCtx_collectArrowTy_nil hinbase hmem
          rw [hcollect] at hnil
          -- `collectArrowTy τ = ([], τ)` and `= (acc, rty)` ⇒ `acc = []`, `rty = τ`
          obtain ⟨hacc, hrty⟩ := Prod.mk.injEq .. ▸ hnil
          subst hacc; subst hrty
          obtain ⟨i, hfind, hval⟩ := formal_align f fv rty hkeys hmem
          simp only [LExpr.substFvarsLifting.go, hfind, LExpr.liftBVars]
          rw [if_pos (Nat.zero_le i)]
          refine .bvar (i + Δ.length) rty ?_ hbase
          rw [List.getElem?_append_right (Nat.le_add_left _ _)]
          simpa using hval
  | .ite c t t' d hc ht he_ =>
      simp only [LExpr.substFvarsLifting.go]
      exact .ite _ _ t' _ (fnDef_body_go f hkeys hinbase hc)
        (fnDef_body_go f hkeys hinbase ht) (fnDef_body_go f hkeys hinbase he_)
  | .eq e1 e2 t hbase he1 he2 =>
      simp only [LExpr.substFvarsLifting.go]
      exact .eq _ _ t hbase (fnDef_body_go f hkeys hinbase he1) (fnDef_body_go f hkeys hinbase he2)
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody =>
      -- descend under the binder: `Δ` grows to `qty :: Δ`, depth to `Δ.length + 1`. Transport both
      -- the trigger and the body through the lifting (the trigger is lifted at the same depth).
      simp only [LExpr.substFvarsLifting.go]
      have ihtr := fnDef_body_go f hkeys hinbase htr
      have ihbody := fnDef_body_go f hkeys hinbase hbody
      simp only [List.length_cons] at ihtr ihbody
      refine .quant qty _ qk qname _ qτtr hbase ?_ ?_
      · rw [show Δ.length + 1 = (qty :: Δ).length from rfl]
        simpa only [List.cons_append] using ihtr
      · rw [show Δ.length + 1 = (qty :: Δ).length from rfl]
        simpa only [List.cons_append] using ihbody
termination_by structural hty

/-- **`.go`-level transport of `AppSpine`** (mutual with `fnDef_body_go`). Given `acc ≠ []` — always
    the case when reached through `.app` recursion — the substituted head types with the same `acc`.
    The `.fvar` head case is vacuous: a formal fvar is base-typed, so `collectArrowTy = ([], _)` forces
    `acc = []`, contradicting `hne`. `.op`/`.fnOp` heads are unchanged by the substitution. -/
theorem fnDef_body_spine_go {Ψ' : FnCtx} (f : LFunc CoreLParams)
    (hkeys : f.inputs.keys.Nodup)
    (hinbase : ∀ t ∈ f.inputs.values, LExpr.MonoTyIsBase t)
    {Δ : BVarCtx} {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hne : acc ≠ []) (hspine : LExpr.AppSpine (funcFVarCtx f) Ψ' Δ e acc rty) :
    LExpr.AppSpine [] Ψ' (Δ ++ f.inputs.values)
      (LExpr.substFvarsLifting.go (funcBvarSubst f) e Δ.length) acc rty := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
      simp only [LExpr.substFvarsLifting.go]
      exact .app _ _ aty acc' rty (fnDef_body_go f hkeys hinbase harg)
        (fnDef_body_spine_go f hkeys hinbase (by simp) hrest)
  | .fvar fv τ acc rty hmem hcollect hbase =>
      -- formal fvar ⇒ base ⇒ `collectArrowTy τ = ([], τ)` ⇒ `acc = []`, contradicting `hne`
      have hnil := funcFVarCtx_collectArrowTy_nil hinbase hmem
      rw [hcollect] at hnil
      exact absurd (Prod.mk.injEq .. ▸ hnil).1 hne
  | .op o oty acc rty hop hcollect =>
      simp only [LExpr.substFvarsLifting.go]; exact .op o oty acc rty hop hcollect
  | .fnOp o oty acc rty hmem hnpre hcollect hbase =>
      simp only [LExpr.substFvarsLifting.go]; exact .fnOp o oty acc rty hmem hnpre hcollect hbase
termination_by structural hspine
end

/-- **Connector 1a — the fvar→bvar body lift.** A function `f` whose body types at its fvar-formal
    context `funcFVarCtx f` (bvar context `[]`), at some `Ψ'`, has its emitted `fnDef` body —
    `substFvarsLifting body (funcBvarSubst f)`, with formals now bvars — typing at the empty fvar
    context `[]`, bvar context `f.inputs.values` (`= d.argTys`), same `Ψ'`. Requires distinct formal
    names (`hkeys`, so the fvar→bvar index is unambiguous) and base-typed formals (`hinbase`, so each
    formal fvar is nullary — a bvar cannot head an application, and `HasSimpType.bvar` demands a base
    type).

    Proven via a `.go`-level mutual transport (`fnDef_body_go` / `fnDef_body_spine_go`) threading an
    arbitrary outer bvar context `Δ` at `depth = Δ.length`: a formal fvar (nullary, base) at fvar
    index `i` becomes `.bvar (i + depth)` typed against `Δ ++ f.inputs.values`; a spine head that is a
    formal fvar is vacuous (base ⟹ empty arg-spine contradicts the enclosing application). -/
theorem fnDef_body_HasSimpType_of_fvar {Ψ' : FnCtx} (f : LFunc CoreLParams) (body : Expression.Expr)
    (hkeys : f.inputs.keys.Nodup)
    (hinbase : ∀ t ∈ f.inputs.values, LExpr.MonoTyIsBase t)
    (hty : LExpr.HasSimpType (funcFVarCtx f) Ψ' [] body f.output) :
    LExpr.HasSimpType [] Ψ' f.inputs.values
      (LExpr.substFvarsLifting body (funcBvarSubst f)) f.output := by
  -- the `.go`-level transport at `Δ = []` (depth `0`); reconcile `substFvarsLifting` with `.go`.
  have hgo := fnDef_body_go f hkeys hinbase (Δ := []) hty
  simp only [List.length_nil, List.nil_append] at hgo
  unfold LExpr.substFvarsLifting
  split
  · -- empty subst ⇒ no formals ⇒ `funcFVarCtx f = []` and `f.inputs.values = []`; `hty` is the goal
    rename_i hempty
    -- `funcBvarSubst f` empty ⇒ `range f.inputs.length` empty ⇒ `f.inputs.length = 0` ⇒ `f.inputs = []`
    rw [funcBvarSubst_eq_map] at hempty
    unfold Map.isEmpty at hempty
    have hmapnil : (List.range f.inputs.length).map
        (fun i => (f.inputs.keys[i]!, (LExpr.bvar () i : Expression.Expr))) = [] := by
      split at hempty
      · assumption
      · exact absurd hempty (by simp)
    rw [List.map_eq_nil_iff, List.range_eq_nil] at hmapnil
    have hnil : f.inputs = [] := List.eq_nil_of_length_eq_zero hmapnil
    have hvals : f.inputs.values = [] := by rw [hnil]; rfl
    have hfvc : funcFVarCtx f = [] := by rw [funcFVarCtx, hnil]; rfl
    rw [hvals]; rw [hfvc] at hty; exact hty
  · exact hgo

/-! ## Reachable-⟹-base foundation

A well-typed obligation can only reference base-signatured functions, so reachable factory functions
are automatically SMT-encodable (`SimpSig`). This lets `FactoryFuncsWF` drop the unconditional
base-signature conjuncts (which the default `Core.Factory`'s regex/Sequence/Map functions violate) —
the emitter re-derives them from the obligation's typing. -/

theorem coreOpHasType_base {op acc rty} (h : LExpr.CoreOpHasType op acc rty) :
    LExpr.MonoTyIsBase rty := by cases h <;> first | exact .int | exact .bool

mutual
theorem hst_base {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {τ : LMonoTy} (he : LExpr.HasSimpType Φ Ψ Δ e τ) : LExpr.MonoTyIsBase τ := by
  match he with
  | .const c hb => exact hb
  | .bvar i t _ hb => exact hb
  | .app fn arg rty hspine => exact aspine_base hspine
  | .fvarNullary f t rty hspine => exact aspine_base hspine
  | .ite c t t' d hc ht he_ => exact hst_base ht
  | .eq e1 e2 t hb he1 he2 => exact .bool
  | .quant qty qbody qk qname qtr qτtr hb htr hbody => exact .bool
theorem aspine_base {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {acc : List LMonoTy} {rty : LMonoTy} (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    LExpr.MonoTyIsBase rty := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest => exact aspine_base hrest
  | .fvar f τ acc' rty hmem hcollect hbase => exact hbase
  | .op o oty acc' rty hop hcollect => exact coreOpHasType_base hop
  | .fnOp o oty acc' rty hmem hnpre hcollect hbase => exact hbase
termination_by structural hspine
end

-- "n has an SMT-encodable (base-decomposing) signature in Ψ": its Ψ-type collectArrowTy-decomposes
-- into all-base argument types and a base return type. This is exactly what `AppSpine.fnOp` provides
-- for a referenced fn, and what the emitter's `MonoTyIsSimp`/base needs.
abbrev SimpSig (Ψ : FnCtx) (n : String) : Prop :=
  ∃ σ acc rty, (n, σ) ∈ Ψ ∧ collectArrowTy σ = (acc, rty) ∧
    (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ LExpr.MonoTyIsBase rty

mutual
theorem HasSimpType_fnRefs_simp {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {τ : LMonoTy} (he : LExpr.HasSimpType Φ Ψ Δ e τ) :
    ∀ n ∈ exprFnRefs e, SimpSig Ψ n := by
  match he with
  | .const c _ => intro n hn; simp only [exprFnRefs, List.not_mem_nil] at hn
  | .bvar i t _ _ => intro n hn; simp only [exprFnRefs, List.not_mem_nil] at hn
  | .app fn arg rty hspine => exact AppSpine_fnRefs_simp (by intro t ht; simp at ht) hspine
  | .fvarNullary f t rty hspine => exact AppSpine_fnRefs_simp (by intro t ht; simp at ht) hspine
  | .ite c t t' d hc ht he_ =>
    intro n hn
    simp only [exprFnRefs, List.mem_append] at hn
    rcases hn with (h | h) | h
    · exact HasSimpType_fnRefs_simp hc n h
    · exact HasSimpType_fnRefs_simp ht n h
    · exact HasSimpType_fnRefs_simp he_ n h
  | .eq e1 e2 t _ he1 he2 =>
    intro n hn
    simp only [exprFnRefs, List.mem_append] at hn
    rcases hn with h | h
    · exact HasSimpType_fnRefs_simp he1 n h
    · exact HasSimpType_fnRefs_simp he2 n h
  | .quant qty qbody qk qname qtr qτtr _ htr hbody =>
    intro n hn
    simp only [exprFnRefs, List.mem_append] at hn
    rcases hn with h | h
    · exact HasSimpType_fnRefs_simp htr n h
    · exact HasSimpType_fnRefs_simp hbody n h

theorem AppSpine_fnRefs_simp {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {acc : List LMonoTy} {rty : LMonoTy}
    (hacc : ∀ t ∈ acc, LExpr.MonoTyIsBase t)
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    ∀ n ∈ exprFnRefs e, SimpSig Ψ n := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    intro n hn
    simp only [exprFnRefs, List.mem_append] at hn
    rcases hn with h | h
    · refine AppSpine_fnRefs_simp (fun t ht => ?_) hrest n h
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact hst_base harg
      · exact hacc t ht'
    · exact HasSimpType_fnRefs_simp harg n h
  | .fvar f τ acc' rty _ _ _ => intro n hn; simp only [exprFnRefs, List.not_mem_nil] at hn
  | .op o oty acc' rty hop hcollect =>
    intro n hn
    have hpre : IsPredefinedOp o.name := ⟨acc', rty, hop⟩
    simp only [exprFnRefs, hpre, if_true, List.not_mem_nil] at hn
  | .fnOp o oty acc' rty hmem hnpre hcollect hbase =>
    intro n hn
    simp only [exprFnRefs, hnpre, if_false, List.mem_singleton] at hn
    subst hn
    exact ⟨oty, acc', rty, hmem, hcollect, hacc, hbase⟩
termination_by structural hspine
end
theorem funcFnRefs_simp (Frec : Lambda.Factory CoreLParams) (f : LFunc CoreLParams)
    -- Functions carrying a body are non-recursive (they are the ones typed / emitted as `fnDef`);
    -- recursive functions are bodyless (`Core.Factory`'s are all bodyless, and `declWF` only types
    -- non-recursive bodies). This lets the body-ref branch use the guarded `FactoryFuncsWF` typing.
    (hbnr : ∀ body, f.body = some body → f.isRecursive = false)
    (hbody : f.isRecursive = false → ∀ body, f.body = some body →
      LExpr.HasSimpType (funcFVarCtx f) (Lambda.Factory.fnCtx Frec) [] body f.output)
    (hax : ∀ ax ∈ f.axioms,
      LExpr.HasSimpType [] (Lambda.Factory.fnCtx Frec) [] ax (.tcons "bool" [])) :
    ∀ n ∈ funcFnRefs f, SimpSig (Lambda.Factory.fnCtx Frec) n := by
  intro n hn
  unfold funcFnRefs at hn
  rcases List.mem_append.mp hn with hb | ha
  · cases hbeq : f.body with
    | none => rw [hbeq] at hb; simp at hb
    | some body =>
        rw [hbeq] at hb; simp only [Option.map_some, Option.getD_some] at hb
        exact HasSimpType_fnRefs_simp (hbody (hbnr body hbeq) body hbeq) n hb
  · obtain ⟨ax, haxmem, hnax⟩ := List.mem_flatMap.mp ha
    exact HasSimpType_fnRefs_simp (hax ax haxmem) n hnax

theorem reachableFuncsGo_simp (Frec : Lambda.Factory CoreLParams)
    (hFrec : ∀ (g : String) (f : LFunc CoreLParams), Frec[g]? = some f →
      ∀ n ∈ funcFnRefs f, SimpSig (Lambda.Factory.fnCtx Frec) n) :
    ∀ (seen wl : List String),
      (∀ x ∈ seen, SimpSig (Lambda.Factory.fnCtx Frec) x) →
      (∀ x ∈ wl, SimpSig (Lambda.Factory.fnCtx Frec) x) →
      ∀ g ∈ reachableFuncsGo Frec seen wl, SimpSig (Lambda.Factory.fnCtx Frec) g := by
  intro seen wl
  induction seen, wl using reachableFuncsGo.induct Frec with
  | case1 seen => intro hseen _ g hg; rw [reachableFuncsGo] at hg; exact hseen g hg
  | case2 seen g' rest hg' ih =>
      intro hseen hwl g hg
      rw [reachableFuncsGo] at hg; simp only [hg', dif_pos] at hg
      exact ih hseen (fun x hx => hwl x (List.mem_cons_of_mem g' hx)) g hg
  | case3 seen g' rest hg' hf ih =>
      intro hseen hwl g hg
      rw [reachableFuncsGo] at hg; simp only [hg', dif_neg, not_false_iff] at hg; rw [hf] at hg
      exact ih hseen (fun x hx => hwl x (List.mem_cons_of_mem g' hx)) g hg
  | case4 seen g' rest hg' f hf ih =>
      intro hseen hwl g hg
      rw [reachableFuncsGo] at hg; simp only [hg', dif_neg, not_false_iff] at hg; rw [hf] at hg
      refine ih ?_ ?_ g hg
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hwl x (List.mem_cons_self)
        · exact hseen x hx'
      · intro x hx
        rcases List.mem_append.mp hx with hxref | hxrest
        · exact hFrec g' f hf x (List.mem_filter.mp hxref).1
        · exact hwl x (List.mem_cons_of_mem g' hxrest)

/-- **Scoped variant of `reachableFuncsGo_simp`.** The `hFrec` (ref-simplicity of every function's
    body/axiom refs) is required only for functions in a `funcDeps`-closed target set `R` that
    contains every worklist/seen node — not for every factory function. This is the key weakening:
    `hFrecR` is only ever consulted at a worklist head `g'` (which resolves, so is a node ⇒ `∈ R`),
    and `R` being `funcDeps`-closed keeps each processed node's node-refs in `R`. Instantiated at
    `R = reachableFuncs Frec seeds` (`reachableFuncs_closed`), this needs `hFrec` only at reachable
    functions — the polymorphic `Map`/`Sequence` seed axioms (unreachable in theory-free programs) are
    never typed. The `∈ R` invariant is scoped to nodes because non-node refs are dropped by the loop
    (`case3`) and never fed to `hFrecR`/closure. -/
theorem reachableFuncsGo_simp_scoped (Frec : Lambda.Factory CoreLParams) (R : List String)
    (hRclosed : ∀ x ∈ R, ∀ y ∈ funcDeps Frec x, y ∈ R)
    (hFrecR : ∀ (g : String) (f : LFunc CoreLParams), g ∈ R → Frec[g]? = some f →
      ∀ n ∈ funcFnRefs f, SimpSig (Lambda.Factory.fnCtx Frec) n) :
    ∀ (seen wl : List String),
      (∀ x ∈ seen, x ∈ factoryNames Frec → x ∈ R) →
      (∀ x ∈ wl, x ∈ factoryNames Frec → x ∈ R) →
      (∀ x ∈ seen, SimpSig (Lambda.Factory.fnCtx Frec) x) →
      (∀ x ∈ wl, SimpSig (Lambda.Factory.fnCtx Frec) x) →
      ∀ g ∈ reachableFuncsGo Frec seen wl, SimpSig (Lambda.Factory.fnCtx Frec) g := by
  intro seen wl
  induction seen, wl using reachableFuncsGo.induct Frec with
  | case1 seen => intro _ _ hseen _ g hg; rw [reachableFuncsGo] at hg; exact hseen g hg
  | case2 seen g' rest hg' ih =>
      intro hseenR hwlR hseen hwl g hg
      rw [reachableFuncsGo] at hg; simp only [hg', dif_pos] at hg
      exact ih hseenR (fun x hx => hwlR x (List.mem_cons_of_mem g' hx)) hseen
        (fun x hx => hwl x (List.mem_cons_of_mem g' hx)) g hg
  | case3 seen g' rest hg' hf ih =>
      intro hseenR hwlR hseen hwl g hg
      rw [reachableFuncsGo] at hg; simp only [hg', dif_neg, not_false_iff] at hg; rw [hf] at hg
      exact ih hseenR (fun x hx => hwlR x (List.mem_cons_of_mem g' hx)) hseen
        (fun x hx => hwl x (List.mem_cons_of_mem g' hx)) g hg
  | case4 seen g' rest hg' f hf ih =>
      intro hseenR hwlR hseen hwl g hg
      rw [reachableFuncsGo] at hg; simp only [hg', dif_neg, not_false_iff] at hg; rw [hf] at hg
      -- `g'` resolves ⇒ it is a node; being a worklist head, it is thus in `R`.
      have hg'node : g' ∈ factoryNames Frec := by
        simp only [factoryNames, List.mem_map]
        exact ⟨f, Array.mem_def.mp (Factory.getElem?_is_some_implies_mem hf),
          Factory.getElem?_name hf⟩
      have hg'R : g' ∈ R := hwlR g' List.mem_cons_self hg'node
      -- Each filtered node-ref of `g'` is a `funcDep`, hence in `R` by closure.
      have hrefsR : ∀ n ∈ (funcFnRefs f).filter (· ∉ g' :: seen),
          n ∈ factoryNames Frec → n ∈ R := by
        intro n hn hnnode
        have hndep : n ∈ funcDeps Frec g' := by
          unfold funcDeps; rw [hf]
          exact List.mem_filter.mpr ⟨(List.mem_filter.mp hn).1, decide_eq_true hnnode⟩
        exact hRclosed g' hg'R n hndep
      refine ih ?_ ?_ ?_ ?_ g hg
      · intro x hx hxnode
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hg'R
        · exact hseenR x hx' hxnode
      · intro x hx hxnode
        rcases List.mem_append.mp hx with hxref | hxrest
        · exact hrefsR x hxref hxnode
        · exact hwlR x (List.mem_cons_of_mem g' hxrest) hxnode
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hwl x List.mem_cons_self
        · exact hseen x hx'
      · intro x hx
        rcases List.mem_append.mp hx with hxref | hxrest
        · exact hFrecR g' f hg'R hf x (List.mem_filter.mp hxref).1
        · exact hwl x (List.mem_cons_of_mem g' hxrest)

theorem reachableOrdered_simp (Frec : Lambda.Factory CoreLParams) (seeds : List String)
    (hFrec : ∀ (g : String) (f : LFunc CoreLParams), Frec[g]? = some f →
      ∀ n ∈ funcFnRefs f, SimpSig (Lambda.Factory.fnCtx Frec) n)
    (hseeds : ∀ n ∈ seeds, SimpSig (Lambda.Factory.fnCtx Frec) n)
    {g : String} (hg : g ∈ reachableOrdered Frec seeds) :
    SimpSig (Lambda.Factory.fnCtx Frec) g := by
  unfold reachableOrdered at hg
  rw [List.mem_filter] at hg
  have hgr : g ∈ reachableFuncs Frec seeds := of_decide_eq_true hg.2
  exact reachableFuncsGo_simp Frec hFrec [] seeds (by simp) hseeds g hgr

/-- **Scoped `reachableOrdered_simp`**: the ref-simplicity hypothesis `hFrecR` is needed only for
    reachable functions (`g ∈ reachableFuncs Frec seeds`), not every factory function. Instantiates
    `reachableFuncsGo_simp_scoped` at the `funcDeps`-closed set `R = reachableFuncs Frec seeds`
    (`reachableFuncs_closed`); seeds that are nodes land in `R` (`mem_reachableFuncs_of_seed`). -/
theorem reachableOrdered_simp_scoped (Frec : Lambda.Factory CoreLParams) (seeds : List String)
    (hFrecR : ∀ (g : String) (f : LFunc CoreLParams), g ∈ reachableFuncs Frec seeds → Frec[g]? = some f →
      ∀ n ∈ funcFnRefs f, SimpSig (Lambda.Factory.fnCtx Frec) n)
    (hseeds : ∀ n ∈ seeds, SimpSig (Lambda.Factory.fnCtx Frec) n)
    {g : String} (hg : g ∈ reachableOrdered Frec seeds) :
    SimpSig (Lambda.Factory.fnCtx Frec) g := by
  unfold reachableOrdered at hg
  rw [List.mem_filter] at hg
  have hgr : g ∈ reachableFuncs Frec seeds := of_decide_eq_true hg.2
  refine reachableFuncsGo_simp_scoped Frec (reachableFuncs Frec seeds)
    (fun x hx y hy => reachableFuncs_closed Frec seeds hx hy) hFrecR
    [] seeds (by simp) (fun x hx hxnode => mem_reachableFuncs_of_seed Frec seeds hx hxnode)
    (by simp) hseeds g hgr

theorem collectArrowTy_foldr_general : ∀ (args : List LMonoTy) (rty : LMonoTy),
    collectArrowTy (List.foldr LMonoTy.arrow rty args)
    = (args ++ (collectArrowTy rty).1, (collectArrowTy rty).2)
  | [], rty => by show collectArrowTy rty = _; rfl
  | a :: as, rty => by
      show (let (atys, r) := collectArrowTy (List.foldr LMonoTy.arrow rty as); (a :: atys, r)) = _
      rw [collectArrowTy_foldr_general as rty]; rfl

-- foldr arrow tail-simp: all args base + tail simp ⟹ whole foldr simp.
theorem foldr_arrow_simp_tail : ∀ (args : List LMonoTy) {rty : LMonoTy},
    (∀ t ∈ args, LExpr.MonoTyIsBase t) → LExpr.MonoTyIsSimp rty →
    LExpr.MonoTyIsSimp (List.foldr LMonoTy.arrow rty args)
  | [], rty, _, hr => hr
  | a :: as, rty, hargs, hr =>
      .arrow (hargs a (by simp)) (foldr_arrow_simp_tail as (fun t ht => hargs t (by simp [ht])) hr)

-- Extraction: SimpSig at fnCtx Frec + resolution ⟹ what the emitter needs — `f.inputs.values` base
-- (for `d.WF`/connector-1a `hinbase`) and `MonoTyIsSimp (funcSig f).2` (for the `.fnDecl` sig).
-- (`f.output` base is not needed by the emitter — `FnDef.WF`/`fnDef_body_...` only touch argTys.)
theorem base_of_SimpSig (Frec : Lambda.Factory CoreLParams) {g : String} {f : LFunc CoreLParams}
    (hres : Frec[g]? = some f) (hs : SimpSig (Lambda.Factory.fnCtx Frec) g) :
    (∀ t ∈ f.inputs.values, LExpr.MonoTyIsBase t) ∧ LExpr.MonoTyIsSimp (funcSig f).2 := by
  obtain ⟨σ, acc, rty, hmem, hcol, haccb, hrtyb⟩ := hs
  obtain ⟨f', hres', hfsig, _⟩ := mem_fnCtx_resolves Frec hmem
  rw [hres] at hres'; injection hres' with hff; subst hff
  -- σ = (funcSig f).2 = foldr arrow f.output (f.inputs.toList.map Prod.snd)
  have hσ : σ = List.foldr LMonoTy.arrow f.output (f.inputs.toList.map Prod.snd) := by
    rw [funcSig] at hfsig; exact (Prod.mk.injEq .. ▸ hfsig).2.symm
  subst hσ
  -- decompose collectArrowTy (foldr arrow out args) = (args ++ tailArgs, tailRet)
  rw [collectArrowTy_foldr_general] at hcol
  injection hcol with hacceq hrtyeq
  have hvals : ∀ t ∈ f.inputs.toList.map Prod.snd, LExpr.MonoTyIsBase t :=
    fun t ht => haccb t (hacceq ▸ List.mem_append_left _ ht)
  have htail : ∀ t ∈ (collectArrowTy f.output).1, LExpr.MonoTyIsBase t :=
    fun t ht => haccb t (hacceq ▸ List.mem_append_right _ ht)
  have houtsimp : LExpr.MonoTyIsSimp f.output := by
    have hout : f.output = List.foldr LMonoTy.arrow (collectArrowTy f.output).2 (collectArrowTy f.output).1 := by
      have := collectArrowTy_foldr f.output; simpa using this
    rw [hout]; exact foldr_arrow_simp_tail (collectArrowTy f.output).1 htail (.base (hrtyeq ▸ hrtyb))
  refine ⟨fun t ht => hvals t (by rw [← ListMap.values_eq_map_snd]; exact ht), ?_⟩
  rw [funcSig]; simp only []
  exact foldr_arrow_simp_tail (f.inputs.toList.map Prod.snd) hvals houtsimp


-- For a produced (bpfx, ob): ob's refs + every bpfx-cmd body's refs are SimpSig Ψ.
-- Invariant: the accumulated `pfx` commands' body-refs are all SimpSig (from prior assume/init typing).
theorem bodyObligations_refs_simp {Ψ : FnCtx} {Φ : FVarCtx} {ss : Statements}
    (hpre : Statements.Preprocessed Ψ Φ ss) :
    ∀ (pfx : List OblCommand),
      (∀ n ∈ pfx.flatMap cmdBodyRefs, SimpSig Ψ n) →
      ∀ bpfx ob, (bpfx, ob) ∈ bodyObligations pfx ss →
        (∀ n ∈ exprFnRefs ob, SimpSig Ψ n) ∧ (∀ n ∈ bpfx.flatMap cmdBodyRefs, SimpSig Ψ n) := by
  induction hpre with
  | nil Φ => intro pfx _ bpfx ob hmem; simp [bodyObligations] at hmem
  | assume Φ l b md rest hb hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      refine ih (pfx ++ [OblCommand.assume b]) ?_ bpfx ob hmem
      intro n hn
      rw [List.flatMap_append] at hn
      rcases List.mem_append.mp hn with h | h
      · exact hpfx n h
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, cmdBodyRefs] at h
        exact HasSimpType_fnRefs_simp hb n h
  | assert Φ l b md rest hb hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      rcases List.mem_cons.mp hmem with heq | htl
      · rw [Prod.mk.injEq] at heq
        obtain ⟨hbpfx, hob⟩ := heq
        subst hbpfx; subst hob
        exact ⟨fun n hn => HasSimpType_fnRefs_simp hb n hn, hpfx⟩
      · -- tail resumes from the same `pfx`
        exact ih pfx hpfx bpfx ob htl
  | initDet Φ name ty mτ e md rest hmono he hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      refine ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]) ?_ bpfx ob hmem
      intro n hn
      rw [List.flatMap_append] at hn
      rcases List.mem_append.mp hn with h | h
      · exact hpfx n h
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, cmdBodyRefs] at h
        exact HasSimpType_fnRefs_simp he n h
  | initNondet Φ name ty mτ md rest hmono hsimp hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      refine ih (pfx ++ [OblCommand.fvarDecl name.name mτ]) ?_ bpfx ob hmem
      intro n hn
      rw [List.flatMap_append] at hn
      rcases List.mem_append.mp hn with h | h
      · exact hpfx n h
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, cmdBodyRefs, List.not_mem_nil] at h
  | ite Φ thenb elseb md rest hthen helse hrest ihthen ihelse ihrest =>
      intro pfx hpfx bpfx ob hmem
      rw [bodyObligations] at hmem
      rcases List.mem_append.mp hmem with h | hr
      · rcases List.mem_append.mp h with ht | he'
        · exact ihthen pfx hpfx bpfx ob ht
        · exact ihelse pfx hpfx bpfx ob he'
      · exact ihrest pfx hpfx bpfx ob hr

/-- **Every emitted obligation's reachability seeds lie in `pfx`-refs ∪ `stmtsFnRefs ss`.** For a
    preprocessed body, each `(bpfx, ob) ∈ bodyObligations pfx ss` has its obligation refs
    (`exprFnRefs ob`) and its accumulated-prefix refs (`bpfx.flatMap cmdBodyRefs`) contained in the
    starting prefix's refs together with `stmtsFnRefs ss` (the whole body's refs). Since `stmtsFnRefs`
    scans exactly the statement forms `bodyObligations` traverses, the induction mirrors
    `bodyObligations_refs_simp` structurally. This is the seed-subset half of the `.proc` reachability
    weakening: with `pfx = []`, each obligation's seeds ⊆ `stmtsFnRefs ss`. -/
theorem bodyObligations_seeds_subset {Ψ : FnCtx} {Φ : FVarCtx} {ss : Statements}
    (hpre : Statements.Preprocessed Ψ Φ ss) :
    ∀ (pfx : List OblCommand) bpfx ob, (bpfx, ob) ∈ bodyObligations pfx ss →
      (∀ n ∈ exprFnRefs ob, n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs ss) ∧
      (∀ n ∈ bpfx.flatMap cmdBodyRefs, n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs ss) := by
  induction hpre with
  | nil Φ => intro pfx bpfx ob hmem; simp [bodyObligations] at hmem
  | assume Φ l b md rest hb hrest ih =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      obtain ⟨ihob, ihpfx⟩ := ih (pfx ++ [OblCommand.assume b]) bpfx ob hmem
      have hss : stmtsFnRefs (Statement.assume l b md :: rest) = exprFnRefs b ++ stmtsFnRefs rest := by
        simp only [stmtsFnRefs]
      -- Relocate `(pfx ++ [assume b]).flatMap ++ stmtsFnRefs rest` into `pfx.flatMap ++ stmtsFnRefs (…::rest)`.
      have reloc : ∀ n, n ∈ (pfx ++ [OblCommand.assume b]).flatMap cmdBodyRefs ++ stmtsFnRefs rest →
          n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs (Statement.assume l b md :: rest) := by
        intro n hn; rw [hss, List.flatMap_append] at *
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, cmdBodyRefs] at hn
        rcases List.mem_append.mp hn with h | h
        · rcases List.mem_append.mp h with hp | hb'
          · exact List.mem_append_left _ hp
          · exact List.mem_append_right _ (List.mem_append_left _ hb')
        · exact List.mem_append_right _ (List.mem_append_right _ h)
      exact ⟨fun n hn => reloc n (ihob n hn), fun n hn => reloc n (ihpfx n hn)⟩
  | assert Φ l b md rest hb hrest ih =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      have hss : stmtsFnRefs (Statement.assert l b md :: rest) = exprFnRefs b ++ stmtsFnRefs rest := by
        simp only [stmtsFnRefs]
      rcases List.mem_cons.mp hmem with heq | htl
      · rw [Prod.mk.injEq] at heq
        obtain ⟨hbpfx, hob⟩ := heq
        subst hbpfx; subst hob
        rw [hss]
        exact ⟨fun n hn => List.mem_append_right _ (List.mem_append_left _ hn),
               fun n hn => List.mem_append_left _ hn⟩
      · obtain ⟨ihob, ihpfx⟩ := ih pfx bpfx ob htl
        have reloc : ∀ n, n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs rest →
            n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs (Statement.assert l b md :: rest) := by
          intro n hn; rw [hss]
          rcases List.mem_append.mp hn with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_append_right _ h)
        exact ⟨fun n hn => reloc n (ihob n hn), fun n hn => reloc n (ihpfx n hn)⟩
  | initDet Φ name ty mτ e md rest hmono he hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      obtain ⟨ihob, ihpfx⟩ := ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]) bpfx ob hmem
      have hss : stmtsFnRefs (Statement.init name ty (.det e) md :: rest)
          = exprFnRefs e ++ stmtsFnRefs rest := by simp only [stmtsFnRefs]
      have reloc : ∀ n, n ∈ (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]).flatMap cmdBodyRefs
            ++ stmtsFnRefs rest →
          n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs (Statement.init name ty (.det e) md :: rest) := by
        intro n hn; rw [hss, List.flatMap_append] at *
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, cmdBodyRefs] at hn
        rcases List.mem_append.mp hn with h | h
        · rcases List.mem_append.mp h with hp | he'
          · exact List.mem_append_left _ hp
          · exact List.mem_append_right _ (List.mem_append_left _ he')
        · exact List.mem_append_right _ (List.mem_append_right _ h)
      exact ⟨fun n hn => reloc n (ihob n hn), fun n hn => reloc n (ihpfx n hn)⟩
  | initNondet Φ name ty mτ md rest hmono hsimp hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      simp only [initDecl, hmono] at hmem
      obtain ⟨ihob, ihpfx⟩ := ih (pfx ++ [OblCommand.fvarDecl name.name mτ]) bpfx ob hmem
      have hss : stmtsFnRefs (Statement.init name ty .nondet md :: rest) = stmtsFnRefs rest := by
        simp only [stmtsFnRefs]
      have reloc : ∀ n, n ∈ (pfx ++ [OblCommand.fvarDecl name.name mτ]).flatMap cmdBodyRefs
            ++ stmtsFnRefs rest →
          n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs (Statement.init name ty .nondet md :: rest) := by
        intro n hn; rw [hss, List.flatMap_append] at *
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, cmdBodyRefs,
          List.append_nil] at hn
        exact hn
      exact ⟨fun n hn => reloc n (ihob n hn), fun n hn => reloc n (ihpfx n hn)⟩
  | ite Φ thenb elseb md rest hthen helse hrest ihthen ihelse ihrest =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      have hss : stmtsFnRefs (Stmt.ite .nondet thenb elseb md :: rest)
          = stmtsFnRefs thenb ++ stmtsFnRefs elseb ++ stmtsFnRefs rest := by simp only [stmtsFnRefs]
      rcases List.mem_append.mp hmem with h | hr
      · rcases List.mem_append.mp h with ht | he'
        · obtain ⟨ihob, ihpfx⟩ := ihthen pfx bpfx ob ht
          have reloc : ∀ n, n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs thenb →
              n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs (Stmt.ite .nondet thenb elseb md :: rest) := by
            intro n hn; rw [hss]
            rcases List.mem_append.mp hn with hp | hb'
            · exact List.mem_append_left _ hp
            · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hb'))
          exact ⟨fun n hn => reloc n (ihob n hn), fun n hn => reloc n (ihpfx n hn)⟩
        · obtain ⟨ihob, ihpfx⟩ := ihelse pfx bpfx ob he'
          have reloc : ∀ n, n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs elseb →
              n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs (Stmt.ite .nondet thenb elseb md :: rest) := by
            intro n hn; rw [hss]
            rcases List.mem_append.mp hn with hp | hb'
            · exact List.mem_append_left _ hp
            · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hb'))
          exact ⟨fun n hn => reloc n (ihob n hn), fun n hn => reloc n (ihpfx n hn)⟩
      · obtain ⟨ihob, ihpfx⟩ := ihrest pfx bpfx ob hr
        have reloc : ∀ n, n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs rest →
            n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs (Stmt.ite .nondet thenb elseb md :: rest) := by
          intro n hn; rw [hss]
          rcases List.mem_append.mp hn with hp | hb'
          · exact List.mem_append_left _ hp
          · exact List.mem_append_right _ (List.mem_append_right _ hb')
        exact ⟨fun n hn => reloc n (ihob n hn), fun n hn => reloc n (ihpfx n hn)⟩

/-- **Deferred (connector-1c topological callees-precede):** the emitted `fnDef` body of a reachable
    factory function `f` types at the emit prefix `c.Ψ` (the earlier-emitted reachable functions).
    `FactoryFuncsWF` gives the body typed at the full `fnCtx F` (fvar formals); `fnDef_body_...` (1a)
    lifts it to bvar formals; and `HasSimpType_restrict_Ψ` would narrow `fnCtx F → c.Ψ` — but its
    side condition (`f`'s callees are in `c.Ψ`, i.e. emitted earlier) is exactly the topological
    order, which requires the factory-array index bookkeeping. That narrowing side-condition is what
    remains deferred here; everything else (sig simplicity, fnDecl case, `d.WF`) is discharged. -/
theorem emitFuncDeclTyped_of_reachable (Frec : Lambda.Factory CoreLParams) (seeds : List String)
    (hFwf : ({ F := Frec } : CoreCtx).FactoryFuncsWF)
    -- Reachable-⟹-base inputs: every reachable factory fn's body/axiom refs are SMT-encodable, and
    -- every seed is. Together (`reachableOrdered_simp_scoped`) they give `SimpSig (fnCtx Frec) g`,
    -- from which the emitted decl's `d.WF`/sig-simplicity (`base_of_SimpSig`) follow — no base
    -- conjuncts in `FactoryFuncsWF`. `hFrec` is scoped to reachable functions (see the scoped
    -- lemmas): polymorphic unreachable seed axioms (Map/Sequence) need not be typed.
    (hFrec : ∀ (g' : String) (f' : LFunc CoreLParams), g' ∈ reachableFuncs Frec seeds → Frec[g']? = some f' →
      ∀ n ∈ funcFnRefs f', SimpSig (Lambda.Factory.fnCtx Frec) n)
    (hseedsimp : ∀ n ∈ seeds, SimpSig (Lambda.Factory.fnCtx Frec) n)
    (c : OblCtx) (hΦ : c.Φ = []) {g : String} (hg : g ∈ reachableOrdered Frec seeds) (f : LFunc CoreLParams)
    (hres : Frec[g]? = some f)
    -- Topological callees-precede (connector 1c): every function `f`'s body references, resolved in
    -- the full `fnCtx Frec`, is already in the emit prefix `c.Ψ`. Discharged at the emitting fold
    -- (`emitFuncDecls_WF`) where `c.Ψ` is the concrete earlier-emitted set. (For non-`.det`-fn cases
    -- vacuous.)
    (htopo : f.isRecursive = false → ∀ body, f.body = some body → ∀ n ∈ exprFnRefs body, ∀ σ,
      (n, σ) ∈ Lambda.Factory.fnCtx Frec → (n, σ) ∈ c.Ψ) :
    emitFuncDeclTyped c f := by
  -- `f ∈ Frec.toArray` (it resolves) ⇒ some split `toArray.toList = pre ++ f :: suf`; prefix-precise
  -- `FactoryFuncsWF` gives name-freshness/nodup + body typing at `pre.map funcSig` (its reconstruction prefix).
  have hfmem : f ∈ Frec.toArray.toList := Array.mem_def.mp (Factory.getElem?_is_some_implies_mem hres)
  obtain ⟨pre, suf, hsplit⟩ := List.append_of_mem hfmem
  obtain ⟨hnres, hkeys, _hbnr, hbodyPre⟩ := hFwf pre f suf hsplit
  -- base signature (inputs base + sig simp) re-derived from reachability, not from `FactoryFuncsWF`.
  obtain ⟨hinbase, hsig⟩ := base_of_SimpSig Frec hres
    (reachableOrdered_simp_scoped Frec seeds hFrec hseedsimp hg)
  -- lift body typing `pre.map funcSig → fnCtx Frec` (`pre` a prefix of `toArray.toList`, so
  -- `pre.map funcSig` a prefix of `fnCtx Frec = toArray.toList.map funcSig`, via `HasSimpType_mono_Ψ`)
  have hbodyty : f.isRecursive = false → ∀ body, f.body = some body →
      LExpr.HasSimpType (funcFVarCtx f) (Lambda.Factory.fnCtx Frec) [] body f.output := by
    intro hnr body hb
    have hfnceq : Lambda.Factory.fnCtx Frec = pre.map funcSig ++ (f :: suf).map funcSig := by
      rw [Lambda.Factory.fnCtx, hsplit, List.map_append]
    rw [hfnceq]; exact HasSimpType_mono_Ψ _ (hbodyPre hnr body hb)
  unfold emitFuncDeclTyped emitFuncDecl
  cases hrec : f.isRecursive
  · cases hbody : f.body with
    | none => simp only []; exact ⟨hnres, hsig⟩  -- `.fnDecl`
    | some body =>
        simp only []  -- `.fnDef` (`d.name = f.name.name`, so `hnres` applies)
        refine ⟨hnres, hinbase, ?_⟩
        -- `d.WFIn c.Φ c.Ψ` = `HasSimpType c.Φ c.Ψ f.inputs.values (emitted body) f.output`.
        show LExpr.HasSimpType c.Φ c.Ψ f.inputs.values
          (LExpr.substFvarsLifting body (funcBvarSubst f)) f.output
        rw [hΦ]
        -- (1)+(2): body typed at fvar-formals/`fnCtx Frec` → 1a lift → bvar-formals/`fnCtx Frec`
        have hbvar := fnDef_body_HasSimpType_of_fvar f body hkeys hinbase (hbodyty hrec body hbody)
        -- (3) narrow `fnCtx Frec → c.Ψ` via `htopo`. Side condition on the emitted body reduces to
        -- the source body (`exprFnRefs_substFvarsLifting`: fvar→bvar lift preserves refs).
        refine HasSimpType_restrict_Ψ (fun n hn σ hσ => ?_) hbvar
        rw [exprFnRefs_substFvarsLifting body (funcBvarSubst f) (funcBvarSubst_refs_nil f)] at hn
        exact htopo hrec body hbody n hn σ hσ
  · simp only []  -- recursive ⇒ `.fnDecl`
    exact ⟨hnres, hsig⟩

/-- **`emitFuncDecl f` is `cmdWF`** from its typing content (`emitFuncDeclTyped`) plus name
    freshness. Matches on `emitFuncDecl f` once so the `cmdWF` goal and the `emitFuncDeclTyped`
    hypothesis reduce to the same branch together. -/
theorem emitFuncDecl_cmdWF (c : OblCtx) (f : LFunc CoreLParams)
    (hfresh : f.name.name ∉ c.names) (htyped : emitFuncDeclTyped c f) :
    c.cmdWF (emitFuncDecl f) := by
  -- `emitFuncDecl f` = `match f.isRecursive, f.body …`; case on those two so both `htyped` and the
  -- goal's `match emitFuncDecl f …` reduce to the same command (head name = `f.name.name`).
  unfold emitFuncDeclTyped at htyped
  unfold OblCtx.cmdWF
  unfold emitFuncDecl at htyped ⊢
  -- non-recursive body ⇒ `.fnDef` (4-tuple cmdWF); every other combination ⇒ `.fnDecl` (3-tuple)
  cases hrec : f.isRecursive
  · cases hbody : f.body
    · simp only [hrec, hbody] at htyped ⊢; exact ⟨hfresh, htyped.1, htyped.2⟩
    · simp only [hrec, hbody] at htyped ⊢; exact ⟨hfresh, htyped.1, htyped.2.1, htyped.2.2⟩
  · simp only [hrec] at htyped ⊢; exact ⟨hfresh, htyped.1, htyped.2⟩

/-- **The emitted function declarations are well-formed** (fold + freshness). Folds
    `emitFuncDecls F fns` for a nodup `fns` of factory-node names, proving each emitted `fnDecl`/
    `fnDef` is `cmdWF`: name freshness from `fns`-nodup (running names = the prior emitted funcSigs'
    names = prior `fns`-prefix), the rest from `emitFuncDeclTyped` (deferred). Requires the base
    ctx `Φ = []` and its names disjoint from `fns`. -/
theorem emitFuncDecls_WF (F : Lambda.Factory CoreLParams) (seeds : List String)
    (hFwf : ({ F := F } : CoreCtx).FactoryFuncsWF)
    (hFrec : ∀ (g' : String) (f' : LFunc CoreLParams), g' ∈ reachableFuncs F seeds → F[g']? = some f' →
      ∀ n ∈ funcFnRefs f', SimpSig (Lambda.Factory.fnCtx F) n)
    (hseedsimp : ∀ n ∈ seeds, SimpSig (Lambda.Factory.fnCtx F) n) :
    ∀ (names : List String), names.Nodup → (∀ g ∈ names, g ∈ reachableOrdered F seeds) →
      ∀ (c : OblCtx), c.Φ = [] → (∀ g ∈ names, g ∉ c.Ψ.map (·.1)) →
      (∀ g ∈ names, ∀ f, F[g]? = some f → f.name.name = g) →
      -- Topological (prefix-indexed): for each split `names = pre ++ g :: suf`, function `g`'s body
      -- refs are in the `Ψ` of emitting `pre` from `c` — i.e. `g`'s callees were emitted earlier.
      -- Satisfiable at the initial `c={}` (`pre=[]` head has no callees, later `g`'s callees sit in
      -- the earlier `pre`), and threads: dropping `hd` folds `emitFuncDecl f_hd` into the base `c`.
      (∀ (pre : List String) (g : String) (suf : List String), names = pre ++ g :: suf →
        ∀ f, F[g]? = some f → f.isRecursive = false → ∀ body, f.body = some body →
          ∀ n ∈ exprFnRefs body, ∀ σ,
          (n, σ) ∈ Lambda.Factory.fnCtx F →
          (n, σ) ∈ ((emitFuncDecls F pre).foldl OblCtx.step c).Ψ) →
      OblProgramWFfrom (emitFuncDecls F names) c := by
  intro names
  induction names with
  | nil => intro _ _ c _ _ _ _; simp [emitFuncDecls, List.filterMap]; trivial
  | cons hd tl ih =>
      intro hnd hreach c hΦ hdisj hname htopo
      rw [List.nodup_cons] at hnd
      rw [emitFuncDecls, List.filterMap_cons]
      cases hhd : F[hd]? with
      | none =>
          -- `hd ∈ reachableOrdered` is a factory node ⇒ `F[hd]?` is some — contradiction
          exact absurd (factoryNames_getElem?_isSome F
            (reachableOrdered_mem_factoryNames F seeds (hreach hd (by simp)))) (by rw [hhd]; simp)
      | some f =>
          simp only [Option.map_some]
          rw [OblProgramWFfrom]
          refine ⟨?_, ?_⟩
          · -- head `emitFuncDecl f` is `cmdWF` at `c`: freshness (proved) + typing (via htopo, pre=[])
            have htyped := emitFuncDeclTyped_of_reachable F seeds hFwf hFrec hseedsimp c hΦ (hreach hd (by simp)) f hhd
              (fun hrec body hb n hn σ hσ => by
                have := htopo [] hd tl rfl f hhd hrec body hb n hn σ hσ
                simpa [emitFuncDecls, List.filterMap] using this)
            have hfname : f.name.name = hd := hname hd (by simp) f hhd
            -- freshness: `f.name.name = hd ∉ c.names` (c.Φ = [] ⇒ names = c.Ψ.map fst)
            have hfresh : f.name.name ∉ c.names := by
              rw [OblCtx.names, hΦ]; simp only [List.map_nil, List.nil_append]
              rw [hfname]; exact hdisj hd (by simp)
            exact emitFuncDecl_cmdWF c f hfresh htyped
          · -- tail: fold from `c.step (emitFuncDecl f)`; re-establish the hypotheses
            have hfname : f.name.name = hd := hname hd (by simp) f hhd
            refine ih hnd.2 (fun g hg => hreach g (by simp [hg]))
              (c.step (emitFuncDecl f)) ?_ ?_ (fun g hg fg hfg => hname g (by simp [hg]) fg hfg) ?_
            · -- `.step` of a decl leaves Φ = c.Φ = []
              rw [← hΦ]; unfold emitFuncDecl; split <;> simp [OblCtx.step]
            · -- disjointness for the tail: `g ∈ tl` fresh vs `c.Ψ ++ [funcSig f]` (i.e. vs f.name = hd)
              intro g hg
              rw [step_emitFuncDecl_Ψ]
              simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                List.mem_singleton, not_or]
              refine ⟨hdisj g (by simp [hg]), ?_⟩
              -- `(funcSig f).1 = f.name.name = hd`; `g ∈ tl` and `hd ∉ tl` ⇒ `g ≠ hd`
              rw [funcSig]; simp only []
              rw [hfname]; exact fun h => hnd.1 (h ▸ hg)
            · -- topological, tail: split `tl = pre' ++ g :: suf'` ⇒ outer split `hd :: pre' ++ …`,
              -- and `(emitFuncDecls F (hd::pre')).foldl c = (emitFuncDecls F pre').foldl (c.step ..)`.
              intro pre' g suf' hsplit fg hfg hrecg body hb n hn σ hσ
              have := htopo (hd :: pre') g suf' (by rw [hsplit, List.cons_append]) fg hfg hrecg body hb n hn σ hσ
              -- rewrite `emitFuncDecls F (hd :: pre')` = `emitFuncDecl f :: emitFuncDecls F pre'`
              rwa [emitFuncDecls, List.filterMap_cons, hhd, Option.map_some,
                List.foldl_cons] at this

/-- `takeWhile (· ≠ x)` over `pre ++ x :: suf` recovers `pre` exactly, when `x ∉ pre` (so every
    element of `pre` passes the guard and the scan stops at the first `x`). -/
theorem takeWhile_ne_append_cons {α} [DecidableEq α] {pre suf : List α} {x : α}
    (hx : x ∉ pre) :
    List.takeWhile (fun y => y != x) (pre ++ x :: suf) = pre := by
  induction pre with
  | nil =>
      simp only [List.nil_append, List.takeWhile_cons, bne_self_eq_false, Bool.false_eq_true,
        if_false]
  | cons a as ih =>
      have hane : a ≠ x := fun h => hx (h ▸ List.mem_cons_self ..)
      have hxas : x ∉ as := fun h => hx (List.mem_cons_of_mem a h)
      rw [List.cons_append, List.takeWhile_cons, if_pos (by simp [bne_iff_ne, hane]), ih hxas]

/-- **A nodup list splits uniquely around a given element.** If `l` is nodup and `l = pre ++ x :: suf
    = pre' ++ x :: suf'`, the prefixes agree. Both equal `takeWhile (· ≠ x) l` (the element `x`
    appears only once, so the scan stops at the same place). -/
theorem nodup_append_cons_inj {α} [DecidableEq α] {l pre suf pre' suf' : List α} {x : α}
    (hnd : l.Nodup) (h1 : l = pre ++ x :: suf) (h2 : l = pre' ++ x :: suf') :
    pre = pre' := by
  have hx1 : x ∉ pre := by
    have hnd1 := hnd; rw [h1, List.nodup_append] at hnd1
    exact fun h => hnd1.2.2 x h x (List.mem_cons_self ..) rfl
  have hx2 : x ∉ pre' := by
    have hnd2 := hnd; rw [h2, List.nodup_append] at hnd2
    exact fun h => hnd2.2.2 x h x (List.mem_cons_self ..) rfl
  have e1 := takeWhile_ne_append_cons (pre := pre) (suf := suf) (x := x) hx1
  have e2 := takeWhile_ne_append_cons (pre := pre') (suf := suf') (x := x) hx2
  rw [← h1] at e1; rw [← h2] at e2
  rw [← e1, e2]

/-- **Connector-1c topological declare-before-use.** `reachableOrdered F seeds` lists its functions
    in a declare-before-use order: for any split `pre ++ g :: suf` and non-recursive `f = F[g]?`,
    every body reference `n ∈ exprFnRefs body` (which types in `fnCtx F` as `(n, σ)`) is already in
    the `Ψ` of emitting `pre`. Proof chain: (1) `n ∈ pre` suffices, since then
    `funcSig_mem_foldl_emitFuncDecls` puts `funcSig fn = (n, σ)` in the prefix `Ψ`. (2) The
    prefix-precise `FactoryFuncsWF` types `f`'s body against `fpre.map funcSig` — the factory-array
    functions before `f` — so `HasSimpType_fnRefs_mem` witnesses `n ∈ fpre.map (·.name.name)`, i.e.
    `n` precedes `g` in `factoryNames F`. (3) `reachableOrdered = (factoryNames F).filter (·∈reach)`
    preserves that order and `n` is reachable (`reachableFuncs_closed`: `n ∈ funcDeps F g`), so `n`
    lands in the reachable-filtered prefix; nodup-split uniqueness (`nodup_append_cons_inj`) pins that
    filtered prefix to `pre`. This is the topological fact — callee-before-caller — that
    `Program.WF`'s `declWF` prefix-`Ψ` typing bakes in via `.fnOp` callee membership. -/
theorem reachableOrdered_declBeforeUse (F : Lambda.Factory CoreLParams) (seeds : List String)
    (hFwf : ({ F := F } : CoreCtx).FactoryFuncsWF) :
    ∀ (pre : List String) (g : String) (suf : List String),
      reachableOrdered F seeds = pre ++ g :: suf →
      ∀ f, F[g]? = some f → f.isRecursive = false → ∀ body, f.body = some body →
        ∀ n ∈ exprFnRefs body, ∀ σ,
        (n, σ) ∈ Lambda.Factory.fnCtx F →
        (n, σ) ∈ ((emitFuncDecls F pre).foldl OblCtx.step ({} : OblCtx)).Ψ := by
  intro pre g suf hsplit f hf hrec body hbody n hn σ hmem
  -- resolve the given `(n, σ) ∈ fnCtx F` to its factory function `fn`
  obtain ⟨fn, hfn, hfnsig, hnnode⟩ := mem_fnCtx_resolves F hmem
  -- it suffices to show `n ∈ pre`: then `funcSig fn = (n, σ)` is in the prefix `Ψ`
  suffices hnpre : n ∈ pre by
    have h := funcSig_mem_foldl_emitFuncDecls F pre {} n fn hnpre hfn
    rwa [hfnsig] at h
  -- (2) `f`'s body types against the factory-array prefix before `f`; `n` is a ref, so it names an
  -- earlier factory function ⇒ `n ∈ fpre.map (·.name.name)`.
  have hfmem : f ∈ F.toArray.toList := Array.mem_def.mp (Factory.getElem?_is_some_implies_mem hf)
  obtain ⟨fpre, fsuf, hfsplit⟩ := List.append_of_mem hfmem
  have hbodyty := (hFwf fpre f fsuf hfsplit).2.2.2 hrec body hbody
  obtain ⟨σ', hnσ'⟩ := HasSimpType_fnRefs_mem hbodyty n hn
  have hnFP : n ∈ fpre.map (·.name.name) := by
    rw [List.mem_map] at hnσ'
    obtain ⟨a, ha, hasig⟩ := hnσ'
    rw [List.mem_map]
    exact ⟨a, ha, by rw [funcSig] at hasig; exact (Prod.mk.injEq .. ▸ hasig).1⟩
  -- `factoryNames F = FP ++ g :: FS` with `FP = fpre.map (·.name.name)`, `g = f.name.name`
  have hfg : f.name.name = g := Factory.getElem?_name hf
  have hfnames : factoryNames F
      = fpre.map (·.name.name) ++ g :: fsuf.map (·.name.name) := by
    rw [factoryNames, hfsplit, List.map_append, List.map_cons, hfg]
  -- (3) `n` is reachable: `g` is reachable, `n ∈ funcDeps F g`, closure ⇒ `n ∈ reach`.
  have hg_ro : g ∈ reachableOrdered F seeds := by
    rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hg_reach : g ∈ reachableFuncs F seeds := by
    unfold reachableOrdered at hg_ro; rw [List.mem_filter] at hg_ro
    exact of_decide_eq_true hg_ro.2
  have hn_dep : n ∈ funcDeps F g := by
    unfold funcDeps; rw [hf, List.mem_filter]
    refine ⟨?_, decide_eq_true hnnode⟩
    unfold funcFnRefs; apply List.mem_append_left
    rw [hbody, Option.map_some, Option.getD_some]; exact hn
  have hn_reach : n ∈ reachableFuncs F seeds := reachableFuncs_closed F seeds hg_reach hn_dep
  -- reachableOrdered splits as `FP.filter reach ++ g :: FS.filter reach`; nodup-uniqueness pins
  -- `pre = FP.filter reach`; `n ∈ FP` and `n` reachable ⇒ `n ∈ pre`.
  have hfilt : reachableOrdered F seeds
      = (fpre.map (·.name.name)).filter (fun x => decide (x ∈ reachableFuncs F seeds))
        ++ g :: (fsuf.map (·.name.name)).filter (fun x => decide (x ∈ reachableFuncs F seeds)) := by
    unfold reachableOrdered
    rw [hfnames, List.filter_append, List.filter_cons, if_pos (decide_eq_true hg_reach)]
  have hpre_eq := nodup_append_cons_inj (reachableOrdered_nodup F seeds) hsplit hfilt
  rw [hpre_eq, List.mem_filter]
  exact ⟨hnFP, decide_eq_true hn_reach⟩

/-- **`emitFuncAxioms` is a `.assume`-map of the collected axioms.** Reshapes the phase-2 emission
    into `OblCommand.assume`-mapped form so `OblProgramWFfrom_assume_map` applies. -/
theorem emitFuncAxioms_eq_assume_map (F : Lambda.Factory CoreLParams) (fns : List String) :
    emitFuncAxioms F fns
      = (fns.flatMap (fun g => (F[g]?).map (·.axioms) |>.getD [])).map OblCommand.assume := by
  unfold emitFuncAxioms
  rw [List.map_flatMap]
  congr 1; funext g
  rcases hg : F[g]? with _ | f
  · simp
  · simp only [Option.map_some, Option.getD_some, funcAxiomAssumes]

/-- **Every emitted function axiom is bool-typed at the full reconstructed `Ψ = fnCtx F`.** For a
    reachable resolved `f = F[g]?` (`g ∈ reachableOrdered`) and `ax ∈ f.axioms`: `SeedWF`'s uniform
    provenance puts `ax ∈ c.fnAxioms` (seed axioms seeded into `init.fnAxioms`, program axioms
    collected per `.func` step), and `hax` types every `c.fnAxioms` entry at `fnCtx c.F`. -/
theorem emitFuncAxiom_typed_at_fnCtx (c : CoreCtx) (seeds : List String)
    (hax : ∀ (g : String) (f : LFunc CoreLParams), g ∈ reachableFuncs c.F seeds → c.F[g]? = some f →
      ∀ a ∈ f.axioms, LExpr.HasSimpType [] (Lambda.Factory.fnCtx c.F) [] a (.tcons "bool" []))
    {g : String} {f : LFunc CoreLParams} (hg : g ∈ reachableOrdered c.F seeds) (hres : c.F[g]? = some f)
    {ax : Expression.Expr} (hax_mem : ax ∈ f.axioms) :
    LExpr.HasSimpType [] (Lambda.Factory.fnCtx c.F) [] ax (.tcons "bool" []) := by
  -- `g ∈ reachableOrdered = (factoryNames F).filter (· ∈ reachableFuncs)`, so `g ∈ reachableFuncs`.
  have hgreach : g ∈ reachableFuncs c.F seeds := by
    unfold reachableOrdered at hg; exact of_decide_eq_true (List.mem_filter.mp hg).2
  exact hax g f hgreach hres ax hax_mem

/-- **Phase-2 function axioms are well-formed.** Each `.assume`-emitted axiom of a reachable resolved
    function is bool-typed at the emitted `Ψ`. Typing comes uniformly from `hax` (every `c.fnAxioms`
    entry — seed axioms seeded into `init.fnAxioms`, program axioms collected per `.func` step — is
    bool-typed at `fnCtx c.F`, as `declWF (.proc)` requires), routed via `SeedWF`'s provenance. The
    `fnCtx F → emitted Ψ` narrowing reuses connector-1c reachability: an axiom's refs are `funcDeps`
    of the (reachable) function, hence reachable, hence emitted. -/
theorem emitFuncAxioms_WF (c : CoreCtx) (seeds : List String) (base : OblCtx)
    (hbΦ : base.Φ = [])
    (hbΨ : base.Ψ = ((obligationPrefix c (reachableOrdered c.F seeds)).foldl OblCtx.step {}).Ψ)
    (hax : ∀ (g : String) (f : LFunc CoreLParams), g ∈ reachableFuncs c.F seeds → c.F[g]? = some f →
      ∀ a ∈ f.axioms, LExpr.HasSimpType [] (Lambda.Factory.fnCtx c.F) [] a (.tcons "bool" [])) :
    OblProgramWFfrom (emitFuncAxioms c.F (reachableOrdered c.F seeds)) base := by
  rw [emitFuncAxioms_eq_assume_map]
  apply OblProgramWFfrom_assume_map
  intro ax hax_flat
  -- locate `ax` as an axiom of some reachable resolved `f`
  rw [List.mem_flatMap] at hax_flat
  obtain ⟨g, hg, hax_in⟩ := hax_flat
  rcases hgres : c.F[g]? with _ | f
  · rw [hgres] at hax_in; simp at hax_in
  · rw [hgres, Option.map_some, Option.getD_some] at hax_in
    rw [hbΦ, hbΨ]
    -- type at `fnCtx c.F`, then narrow to emitted `Ψ` using reachability of the axiom's refs
    have hty := emitFuncAxiom_typed_at_fnCtx c seeds hax hg hgres hax_in
    refine HasSimpType_narrow_to_emitted_reachable c seeds (fun n hn => ?_) hty
    -- `n ∈ exprFnRefs ax`: it types in `fnCtx c.F` (`HasSimpType_fnRefs_mem`) ⇒ `n` a factory node;
    -- `n ∈ funcFnRefs f` (axiom refs), so `n ∈ funcDeps c.F g`; `g` reachable ⇒ `n` reachable.
    obtain ⟨σ, hnσ⟩ := HasSimpType_fnRefs_mem hty n hn
    obtain ⟨_, _, _, hnnode⟩ := mem_fnCtx_resolves c.F hnσ
    have hn_dep : n ∈ funcDeps c.F g := by
      unfold funcDeps; rw [hgres, List.mem_filter]
      refine ⟨?_, decide_eq_true hnnode⟩
      -- `n ∈ funcFnRefs f` via the axiom summand
      unfold funcFnRefs; apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨ax, hax_in, hn⟩
    exact reachableOrdered_closed c.F seeds hg hn_dep

/-- **The emitted function declarations + axioms are well-formed.** Phase-1 declarations
    `emitFuncDecls c.F fns` then phase-2 axioms `emitFuncAxioms c.F fns` (`fns = reachableOrdered c.F
    seeds`) are `OblProgramWFfrom` from `{}`. Splits via `OblProgramWFfrom_append`: decls-WF is
    `emitFuncDecls_WF` (fold + freshness + connector-1c declare-before-use, all proven); axioms-WF is
    `emitFuncAxioms_WF` (all fn-axioms bool-typed via `hax`, seed+program uniformly in `c.fnAxioms`).
    Takes the full `CoreCtx c` since axiom typing consumes `c.SeedWF` and the `.proc` `fnAxioms` fact. -/
theorem emitFuncDecls_axioms_WF (c : CoreCtx) (seeds : List String)
    (hFwf : c.FactoryFuncsWF) (_hseed : c.SeedWF)
    (hseedsimp : ∀ n ∈ seeds, SimpSig (Lambda.Factory.fnCtx c.F) n)
    -- Weakened: axiom typing is required only for the axioms of reachable functions (whose refs the
    -- emitted obligation actually assumes). The polymorphic Map/Sequence seed axioms, unreachable in
    -- theory-free programs, need not type — closing the gap that made `declWF`'s proc clause
    -- unsatisfiable for the default factory. See `reachableFuncsGo_simp_scoped`.
    (hax : ∀ (g : String) (f : LFunc CoreLParams), g ∈ reachableFuncs c.F seeds → c.F[g]? = some f →
      ∀ a ∈ f.axioms, LExpr.HasSimpType [] (Lambda.Factory.fnCtx c.F) [] a (.tcons "bool" [])) :
    OblProgramWFfrom (emitFuncDecls c.F (reachableOrdered c.F seeds)
      ++ emitFuncAxioms c.F (reachableOrdered c.F seeds)) {} := by
  -- Reachable-⟹-base input `hFrec` (scoped): every reachable factory fn's body/axiom refs are
  -- `SimpSig` — from its body typing (`FactoryFuncsWF`) + axiom typing (`hax` at that reachable fn).
  have hFrec : ∀ (g' : String) (f' : LFunc CoreLParams), g' ∈ reachableFuncs c.F seeds → c.F[g']? = some f' →
      ∀ n ∈ funcFnRefs f', SimpSig (Lambda.Factory.fnCtx c.F) n := by
    intro g' f' hg'reach hres'
    have hf'mem : f' ∈ c.F.toArray := Factory.getElem?_is_some_implies_mem hres'
    obtain ⟨pre', suf', hsplit'⟩ := List.append_of_mem (Array.mem_def.mp hf'mem)
    obtain ⟨_, _, hbnr', hbodyPre'⟩ := hFwf pre' f' suf' hsplit'
    refine funcFnRefs_simp c.F f' hbnr' (fun hnr body hb => ?_) (fun ax hax' => ?_)
    · -- body typing at `pre'.map funcSig`, lifted to `fnCtx c.F`
      have hfnceq : Lambda.Factory.fnCtx c.F = pre'.map funcSig ++ (f' :: suf').map funcSig := by
        rw [Lambda.Factory.fnCtx, hsplit', List.map_append]
      exact hfnceq ▸ HasSimpType_mono_Ψ _ (hbodyPre' hnr body hb)
    · -- axiom typing: `ax ∈ f'.axioms`, typed by `hax` at the reachable `g'`
      exact hax g' f' hg'reach hres' ax hax'
  rw [OblProgramWFfrom_append]
  refine ⟨?_, ?_⟩
  · -- phase-1 declarations: fold + freshness + connector-1c declare-before-use (all proven)
    exact emitFuncDecls_WF c.F seeds hFwf hFrec hseedsimp (reachableOrdered c.F seeds)
      (reachableOrdered_nodup c.F seeds)
      (fun g hg => hg) {} rfl (fun g _ => by simp) (fun g _ f hf => Factory.getElem?_name hf)
      (reachableOrdered_declBeforeUse c.F seeds hFwf)
  · -- phase-2 axioms: all bool-typed via `hax` (seed+program uniformly in `c.fnAxioms`). Base Ψ =
    -- the decls-fold Ψ = the obligationPrefix Ψ (the emitFuncAxioms/distinct/axiom tail preserves Ψ).
    refine emitFuncAxioms_WF c seeds
      ((emitFuncDecls c.F (reachableOrdered c.F seeds)).foldl OblCtx.step {}) ?_ ?_ hax
    · rw [foldl_emitFuncDecls_Φ]
    · -- decls-fold Ψ = obligationPrefix Ψ: the emitFuncAxioms/distinct/axiom tail only grows assertions
      unfold obligationPrefix
      rw [show emitFuncDecls c.F (reachableOrdered c.F seeds)
            ++ emitFuncAxioms c.F (reachableOrdered c.F seeds)
            ++ c.distincts.map OblCommand.distinct ++ c.axioms.map OblCommand.assume
          = emitFuncDecls c.F (reachableOrdered c.F seeds)
            ++ (emitFuncAxioms c.F (reachableOrdered c.F seeds)
                ++ c.distincts.map OblCommand.distinct ++ c.axioms.map OblCommand.assume) by
        simp only [List.append_assoc]]
      exact (foldl_prefix_Ψ_eq _ _ (obligationPrefix_tail_assume_distinct c _)).symm

/-- **Emitted obligations are well-formed, at any fold context.** The generalized form of
    `toOblPrograms_wf` over a prefix `decls`/`c` with the accumulated invariants — the shape the
    Layer-1 soundness fold also consumes to supply `OblProgramWF Q` for `OblProgram.Valid`. -/
theorem toOblProgramsFrom_WF (c : CoreCtx) (decls : List Decl)
    (hwf : Program.WFfrom decls c) (hgood : c.Good) (hffwf : c.FactoryFuncsWF) (hseed : c.SeedWF) :
    ∀ Q ∈ toOblProgramsFrom decls c, OblProgramWF Q := by
  intro Q hQ
  obtain ⟨p', ss, c', hbody, hpre, hax, hcgood, hcffwf, hcseed, hmem⟩ :=
    toOblProgramsFrom_declWF decls c hwf hgood hffwf hseed hQ
  -- Expose the per-assert witness: `Q = ⟨obligationPrefix c' fns ++ bpfx, ob⟩`.
  obtain ⟨bpfx, ob, hbomem, hQeq⟩ := mem_procObligations hmem
  subst hQeq
  constructor
  · -- `cmdsWF`: `OblProgramWFfrom (obligationPrefix c' fns ++ bpfx) {}`
    -- Splits (via `OblProgramWFfrom_append`) into obligationPrefix-WF from `{}` and bpfx-WF from the
    -- obligationPrefix-folded context.
    show OblProgramWFfrom (obligationPrefix c' _ ++ bpfx) {}
    rw [OblProgramWFfrom_append]
    refine ⟨?_, ?_⟩
    · -- obligationPrefix-WF from `{}`: 2-way split into the function decls+axioms and the
      -- global distinct/axiom tail. `obligationPrefix = (emitFuncDecls ++ emitFuncAxioms)
      --   ++ (distincts.map ++ axioms.map)`.
      show OblProgramWFfrom (obligationPrefix c' _) {}
      have hsplit : ∀ fns, obligationPrefix c' fns
          = (emitFuncDecls c'.F fns ++ emitFuncAxioms c'.F fns)
            ++ (c'.distincts.map OblCommand.distinct ++ c'.axioms.map OblCommand.assume) := by
        intro fns; unfold obligationPrefix; simp only [List.append_assoc]
      rw [hsplit, OblProgramWFfrom_append]
      refine ⟨?_, ?_⟩
      · -- function decls+axioms from `{}`: connector-1c decls (proven) + program/seed axioms.
        -- `hax : ∀ ax ∈ c'.fnAxioms, HasSimpType [] c'.Ψ [] ax bool`, and `c'.Ψ = fnCtx c'.F`.
        -- `hseedsimp`: every seed (obligation refs + bpfx bodies + global axiom/distinct refs) has a
        -- base-decomposing signature, because each is a ref of an expression well-typed at `c'.Ψ`
        -- (`= fnCtx c'.F`): `ob`/`bpfx` via `bodyObligations_refs_simp`, globals via `hcgood`.
        -- Bridge the per-`declWF` proc-level scoped `hax` (typing at `reachableFuncs c'.F
        -- (procSeeds c' ss)`) into the per-obligation scoped shape `emitFuncDecls_axioms_WF` wants
        -- (typing at `reachableFuncs c'.F obligationSeeds`): the obligation's seeds ⊆ `procSeeds c' ss`
        -- (`bodyObligations_seeds_subset` for `ob`/`bpfx`, verbatim for the global parts), so
        -- `reachableFuncs_mono` maps a reachable `g` for this obligation to a reachable `g` for the proc.
        refine emitFuncDecls_axioms_WF c' _ hcffwf hcseed (fun n hn => ?_)
          (fun g f hg_reach hres ax hax_mem => ?_)
        · -- Goal 1 (seed simplicity `hseedsimp`): every obligation seed has a base-decomposing sig
          obtain ⟨hobsimp, hbpfxsimp⟩ := bodyObligations_refs_simp hpre [] (by simp) bpfx ob hbomem
          rcases List.mem_append.mp hn with h | hdist
          · rcases List.mem_append.mp h with h | hax'
            · rcases List.mem_append.mp h with hob | hbp
              · exact hobsimp n hob
              · exact hbpfxsimp n hbp
            · -- global axiom ref: `c'.axioms.flatMap exprFnRefs`, each axiom typed by `hcgood.1`
              obtain ⟨e, hemem, hne⟩ := List.mem_flatMap.mp hax'
              exact HasSimpType_fnRefs_simp (hcgood.1 e hemem) n hne
          · -- global distinct ref: `c'.distincts.flatMap (·.flatMap exprFnRefs)`, typed by `hcgood.2`
            obtain ⟨es, hesmem, hnes⟩ := List.mem_flatMap.mp hdist
            obtain ⟨e, hemem, hne⟩ := List.mem_flatMap.mp hnes
            obtain ⟨_, τ, _, hty⟩ := hcgood.2 es hesmem
            exact HasSimpType_fnRefs_simp (hty e hemem) n hne
        · -- Goal 2 (reachable-axiom typing): bridge proc-scoped `hax` to this obligation's seeds via
          -- seed-subset + `reachableFuncs_mono`.
          obtain ⟨hsubob, hsubbpfx⟩ := bodyObligations_seeds_subset hpre [] bpfx ob hbomem
          have hseedsub : ∀ x ∈ (exprFnRefs ob
              ++ bpfx.flatMap (fun | .assume e => exprFnRefs e | .varDef v => exprFnRefs v.body | _ => [])
              ++ c'.axioms.flatMap exprFnRefs
              ++ c'.distincts.flatMap (fun es => es.flatMap exprFnRefs)),
              x ∈ c'.procSeeds ss := by
            intro x hx
            unfold CoreCtx.procSeeds
            rcases List.mem_append.mp hx with h | hdist
            · rcases List.mem_append.mp h with h2 | hax'
              · rcases List.mem_append.mp h2 with hob | hbp
                · -- `ob` refs ⊆ `[].flatMap cmdBodyRefs ++ stmtsFnRefs ss = stmtsFnRefs ss`
                  have := hsubob x hob; simp only [List.flatMap_nil, List.nil_append] at this
                  exact List.mem_append_left _ (List.mem_append_left _ this)
                · -- `bpfx` refs (via `cmdBodyRefs`) ⊆ `stmtsFnRefs ss`
                  have := hsubbpfx x hbp; simp only [List.flatMap_nil, List.nil_append] at this
                  exact List.mem_append_left _ (List.mem_append_left _ this)
              · exact List.mem_append_left _ (List.mem_append_right _ hax')
            · exact List.mem_append_right _ hdist
          exact hax g (reachableFuncs_mono c'.F hseedsub g hg_reach) f hres ax hax_mem
      · -- global distinct/axiom tail, via `obligationPrefix_globals_WF`. Base = the decls+axioms fold.
        refine obligationPrefix_globals_WF c'
          (exprFnRefs ob
            ++ bpfx.flatMap (fun | .assume e => exprFnRefs e | .varDef v => exprFnRefs v.body | _ => [])
            ++ c'.axioms.flatMap exprFnRefs
            ++ c'.distincts.flatMap (fun es => es.flatMap exprFnRefs))
          ((emitFuncDecls c'.F (reachableOrdered c'.F _)
            ++ emitFuncAxioms c'.F (reachableOrdered c'.F _)).foldl OblCtx.step {}) ?_ ?_ hcgood ?_ ?_
        · -- base Φ = []
          rw [List.foldl_append, foldl_emitFuncAxioms_Φ, foldl_emitFuncDecls_Φ]
        · -- base Ψ = full obligationPrefix Ψ (tail preserves Ψ)
          rw [hsplit]
          exact (foldl_prefix_Ψ_eq _ _ (fun cmd hc => by
            rcases List.mem_append.mp hc with h | h
            · obtain ⟨x,_,hx⟩ := List.mem_map.mp h; exact Or.inr ⟨x, hx.symm⟩
            · obtain ⟨x,_,hx⟩ := List.mem_map.mp h; exact Or.inl ⟨x, hx.symm⟩)).symm
        · -- axiom refs are seeds (3rd `++` summand `c'.axioms.flatMap exprFnRefs`)
          intro e he n hn
          exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hn⟩))
        · -- distinct refs are seeds (4th `++` summand)
          intro es hes e he n hn
          exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨es, hes, List.mem_flatMap.mpr ⟨e, he, hn⟩⟩)
    · -- bpfx-WF from the obligationPrefix-folded context `c₀`, via `bodyObligations_cmdsWF`
      -- (target `Ψ' = c₀.Ψ`, the emitted/narrowed function context). `pfx = []`, base `c₀`.
      refine bodyObligations_cmdsWF (Ψ := c'.Ψ)
        (Ψ' := ((obligationPrefix c' _).foldl OblCtx.step {}).Ψ) ?_
        ((obligationPrefix c' _).foldl OblCtx.step {}) hpre [] trivial ?_ rfl bpfx ob hbomem ?_
      · -- `hΨsub`: emitted `Ψ` names ⊆ `c'.Ψ` names (= `factoryNames c'.F`, since `c'.Ψ = fnCtx c'.F`)
        intro nm hnm
        have hnode := foldl_obligationPrefix_Ψ_names c' _ nm hnm
        -- `c'.Ψ.map fst = (fnCtx c'.F).map fst = factoryNames c'.F`
        show nm ∈ (Lambda.Factory.fnCtx c'.F).map (·.1)
        simpa only [Lambda.Factory.fnCtx, List.map_map, factoryNames, funcSig,
          Function.comp] using hnode
      · -- `([].foldl step c₀).Φ = []` (obligationPrefix preserves Φ = [])
        show ((obligationPrefix c' _).foldl OblCtx.step {}).Φ = []
        exact foldl_obligationPrefix_Φ c' _ {}
      · -- `hcov`: this bpfx's own command bodies narrow `c'.Ψ → emitted Ψ` (they are seeds)
        intro n hn σ hσ
        -- `n ∈ bpfx.flatMap cmdBodyRefs` ⊆ seeds (the `.varDef v => …/.assume e => …` seed summand
        -- IS `cmdBodyRefs`); resolve `n`, show it reachable-ordered, land it in the emitted `Ψ`.
        obtain ⟨f, hres, hfsig, hnode⟩ := mem_fnCtx_resolves c'.F hσ
        have hseed : n ∈ (exprFnRefs ob
            ++ bpfx.flatMap (fun | .assume e => exprFnRefs e | .varDef v => exprFnRefs v.body | _ => [])
            ++ c'.axioms.flatMap exprFnRefs
            ++ c'.distincts.flatMap (fun es => es.flatMap exprFnRefs)) := by
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
          -- `bpfx.flatMap cmdBodyRefs = bpfx.flatMap (that seed fn)` (defeq on `cmdBodyRefs`)
          obtain ⟨c, hcmem, hnc⟩ := List.mem_flatMap.mp hn
          exact List.mem_flatMap.mpr ⟨c, hcmem, by cases c <;> simp_all [cmdBodyRefs]⟩
        have hfns := mem_reachableOrdered_of_seed c'.F _ hseed hnode
        have := funcSig_mem_obligationPrefix_Ψ c' _ [] hfns hres
        rw [hfsig] at this; simpa using this
  · -- `obligationWF`: the obligation `ob` is bool-typed at `Q.Φ`/`Q.Ψ`.
    -- `ob` types at `(bpfx-folded Φ, c'.Ψ)` (body typing); `Q.Φ` equals that Φ (obligationPrefix
    -- doesn't touch Φ); narrow `c'.Ψ → Q.Ψ` via the reachability keystone.
    show LExpr.HasSimpType
        ((_ ++ bpfx).foldl OblCtx.step {}).Φ ((_ ++ bpfx).foldl OblCtx.step {}).Ψ [] ob _
    -- abbreviation for the reachable-ordered function names emitted for this obligation
    generalize hseeds : (exprFnRefs ob
      ++ bpfx.flatMap (fun | .assume e => exprFnRefs e | .varDef v => exprFnRefs v.body | _ => [])
      ++ c'.axioms.flatMap exprFnRefs
      ++ c'.distincts.flatMap (fun es => es.flatMap exprFnRefs)) = seeds
    -- (1) `ob` types at `(bpfx-folded-from-{} Φ, c'.Ψ)`
    have hob := bodyObligations_ob_typed hpre [] rfl bpfx ob hbomem
    -- (2) `Q.Φ = (bpfx-folded-from-{} Φ)` since obligationPrefix preserves Φ
    have hΦeq : ((obligationPrefix c' (reachableOrdered c'.F seeds) ++ bpfx).foldl OblCtx.step {}).Φ
              = (bpfx.foldl OblCtx.step {}).Φ := by
      rw [List.foldl_append]
      exact foldl_step_Φ_congr bpfx _ {} (foldl_obligationPrefix_Φ c' (reachableOrdered c'.F seeds) {})
    rw [hΦeq]
    -- (3) narrow `c'.Ψ → Q.Ψ`: obligation refs are seeds, so their entries survive
    refine HasSimpType_restrict_Ψ ?_ hob
    -- goal Ψ target is `((obligationPrefix c' (reachableOrdered c'.F seeds) ++ bpfx).foldl step {}).Ψ`
    exact restrict_Ψ_side_condition c' seeds bpfx ob
      (fun n hn => hseeds ▸ List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hn)))

/-- **Emitted obligations are well-formed.** Every `OblProgram` in `toOblPrograms p` is
    `OblProgramWF`, given `Program.WF p`. The `CoreCtx.init`-seeded corollary of
    `toOblProgramsFrom_WF`. -/
theorem toOblPrograms_wf {p : Program} (hwf : Program.WF p)
    (hseedFF : CoreCtx.SeedFactoryFuncsWF) :
    ∀ Q ∈ toOblPrograms p, OblProgramWF Q :=
  toOblProgramsFrom_WF CoreCtx.init p.decls hwf CoreCtx.init_Good
    hseedFF CoreCtx.init_SeedWF

/-- **A model satisfies a `bodyObligations` prefix.** Every `.assume e` command's `e` denotes `true`
    and every `.varDef v` is pinned (`fvarVal` at `v` equals `⟦v.body⟧`) — exactly the path facts the
    fired `assumeLive`/`assertPass`/`initDetLive` steps witness, and exactly what
    `LambdaModelSatisfiesAsms`/`VarDefs.Consistent` need for the `bpfx` portion of `Q.cmds`.
    `.fvarDecl` (havoc) and other commands carry no obligation. -/
def PrefixSat (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) (pfx : List OblCommand) : Prop :=
  (∀ e, OblCommand.assume e ∈ pfx → Denotes opInterp fvarVal e true) ∧
  (∀ v, OblCommand.varDef v ∈ pfx →
    ∃ h : LExpr.HasTypeA [] v.body v.ty, VarDef.Consistent opInterp fvarVal v h)

/-- **The run↔`bodyObligations` correspondence (Half A of the model transfer).** A non-failing run
    from `⟨ss, false⟩` through the fired path to a config headed by `assert l b md :: rest'` traces a
    root-to-assert path in `bodyObligations pfx ss`: there is a produced `(bpfx, b)` whose prefix
    `bpfx` the model satisfies (`PrefixSat` — its assumes fired true, its varDefs pinned). Threads the
    already-fired accumulator `pfx` (with `PrefixSat` for it) so the `ite`/init/assume recursion lines
    up with the `PStep` rules. Proven by induction on the run length via `PStepStar.uncons`, casing on
    the leading statement (the `Preprocessed` shape rules out non-preprocessed heads). -/
theorem run_corresponds_bodyObligations {opInterp fvarVal} {Ψ : FnCtx} :
    ∀ {Φ : FVarCtx} {ss : Statements}, Statements.Preprocessed Ψ Φ ss →
    ∀ (pfx : List OblCommand), PrefixSat opInterp fvarVal pfx →
    ∀ {l b md rest'},
      PStepStar opInterp fvarVal ⟨ss, false⟩ ⟨Statement.assert l b md :: rest', false⟩ →
      ∃ bpfx, (bpfx, b) ∈ bodyObligations pfx ss ∧ PrefixSat opInterp fvarVal bpfx := by
  intro Φ ss hpre
  induction hpre with
  | nil Φ =>
      -- empty body cannot run to a nonempty assert-headed config
      intro pfx _ l b md rest' hrun
      rcases hrun.uncons with heq | ⟨c₂, hstep, _⟩
      · exact absurd (PConfig.mk.injEq .. ▸ heq).1 (by simp)
      · nomatch hstep
  | assume Φ l' b' md' rest hb hrest ih =>
      intro pfx hpsat l b md rest' hrun
      rcases hrun.uncons with heq | ⟨c₂, hstep, hrun'⟩
      · exact absurd (PConfig.mk.injEq .. ▸ heq).1 (by simp)
      · -- the only step from an `assume`-headed config is `assumeLive` into `⟨rest, false⟩`
        cases hstep with
        | assumeLive _ _ _ _ _ hbtrue =>
            rw [bodyObligations]
            -- extend the accumulator with `.assume b'` (which fired true)
            refine ih (pfx ++ [OblCommand.assume b']) ?_ hrun'
            refine ⟨fun e he => ?_, fun v hv => ?_⟩
            · rcases List.mem_append.mp he with h | h
              · exact hpsat.1 e h
              · rw [List.mem_singleton] at h; cases h; exact hbtrue
            · rcases List.mem_append.mp hv with h | h
              · exact hpsat.2 v h
              · rw [List.mem_singleton] at h; cases h
  | assert Φ l' b' md' rest hb hrest ih =>
      intro pfx hpsat l b md rest' hrun
      rcases hrun.uncons with heq | ⟨c₂, hstep, hrun'⟩
      · -- reflexive: this assert is the target; take the head `(pfx, b')`
        obtain ⟨hwork, _⟩ := PConfig.mk.injEq .. ▸ heq
        rw [List.cons.injEq] at hwork
        obtain ⟨hst, _⟩ := hwork
        cases hst
        rw [bodyObligations]
        exact ⟨pfx, List.mem_cons_self .., hpsat⟩
      · -- a step: `assertPass` (into rest, live) or `assertFail` (flips to failed, impossible here)
        cases hstep with
        | assertPass _ _ _ _ _ hbtrue =>
            -- the target `(bpfx, b)` lands in the recursive tail; the tail resumes from the same `pfx`
            -- (a discharged `assert` is not added to the path condition, matching the non-blocking
            -- semantics), so the accumulator is unchanged and `hpsat` carries through.
            obtain ⟨bpfx, hmem, hsat⟩ := ih pfx hpsat hrun'
            rw [bodyObligations]
            exact ⟨bpfx, List.mem_cons_of_mem _ hmem, hsat⟩
        | assertFail _ _ _ _ _ _ =>
            -- steps to `⟨rest, true⟩`; but `hrun' : … → ⟨assert.., false⟩` needs failed=false start
            exact absurd (hrun'.not_failed_of_not_failed rfl) (by simp)
  | initDet Φ name ty mτ e md' rest hmono he hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpsat l b md rest' hrun
      rcases hrun.uncons with heq | ⟨c₂, hstep, hrun'⟩
      · exact absurd (PConfig.mk.injEq .. ▸ heq).1 (by simp)
      · -- the only step from an `init .det`-headed config is `initDetLive` into `⟨rest, false⟩`,
        -- carrying `hpin : VarDef.Consistent … ⟨name.name, mτ', e⟩`
        cases hstep with
        | initDetLive _ _ mτ' _ _ _ _ hmono' hpinTy hpin =>
            -- `initDecl` uses `mτ` from `hmono`; the step's `mτ'` from `hmono'` agrees
            rw [bodyObligations]
            simp only [initDecl, hmono]
            have hmτ : mτ' = mτ := by rw [hmono'] at hmono; exact Option.some.injEq .. ▸ hmono
            subst hmτ
            have hsat' : PrefixSat opInterp fvarVal (pfx ++ [OblCommand.varDef ⟨name.name, mτ', e⟩]) := by
              refine ⟨fun e' he' => ?_, fun v hv => ?_⟩
              · rcases List.mem_append.mp he' with h | h
                · exact hpsat.1 e' h
                · rw [List.mem_singleton] at h; cases h
              · rcases List.mem_append.mp hv with h | h
                · exact hpsat.2 v h
                · rw [List.mem_singleton] at h; cases h; exact ⟨hpinTy, hpin⟩
            exact ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ', e⟩]) hsat' hrun'
  | initNondet Φ name ty mτ md' rest hmono hsimp hfreshΦ hfreshΨ hnres hrest ih =>
      intro pfx hpsat l b md rest' hrun
      rcases hrun.uncons with heq | ⟨c₂, hstep, hrun'⟩
      · exact absurd (PConfig.mk.injEq .. ▸ heq).1 (by simp)
      · -- the only step from an `init .nondet`-headed config is `initNondet` into `⟨rest, false⟩`
        cases hstep with
        | initNondet _ _ _ _ _ =>
            rw [bodyObligations]
            simp only [initDecl, hmono]
            have hsat' : PrefixSat opInterp fvarVal (pfx ++ [OblCommand.fvarDecl name.name mτ]) := by
              refine ⟨fun e' he' => ?_, fun v hv => ?_⟩
              · rcases List.mem_append.mp he' with h | h
                · exact hpsat.1 e' h
                · rw [List.mem_singleton] at h; cases h
              · rcases List.mem_append.mp hv with h | h
                · exact hpsat.2 v h
                · rw [List.mem_singleton] at h; cases h
            exact ih (pfx ++ [OblCommand.fvarDecl name.name mτ]) hsat' hrun'
  | ite Φ thenb elseb md' rest hthen helse hrest ihthen ihelse ihrest =>
      intro pfx hpsat l b md rest' hrun
      rcases hrun.uncons with heq | ⟨c₂, hstep, hrun'⟩
      · exact absurd (PConfig.mk.injEq .. ▸ heq).1 (by simp)
      · -- three sibling branches: then / else / continuation, each from the same `pfx`
        rw [bodyObligations]
        cases hstep with
        | iteLeft _ _ _ _ _ =>
            obtain ⟨bpfx, hmem, hsat⟩ := ihthen pfx hpsat hrun'
            exact ⟨bpfx, List.mem_append_left _ (List.mem_append_left _ hmem), hsat⟩
        | iteRight _ _ _ _ _ =>
            obtain ⟨bpfx, hmem, hsat⟩ := ihelse pfx hpsat hrun'
            exact ⟨bpfx, List.mem_append_left _ (List.mem_append_right _ hmem), hsat⟩
        | iteRest _ _ _ _ _ =>
            obtain ⟨bpfx, hmem, hsat⟩ := ihrest pfx hpsat hrun'
            exact ⟨bpfx, List.mem_append_right _ hmem, hsat⟩

/-! ## Half-B fold bookkeeping: `Q`'s accumulated fields as prefix ⊎ command origin

The folded `assumptions`/`varDefs`/`distincts` of a command list are exactly the base context's plus
one entry per `.assume`/`.varDef`/`.distinct` command. So `e ∈ (cmds.foldl step c).assumptions` iff
`e ∈ c.assumptions` or `.assume e ∈ cmds` — the origin tracking that routes each `Q.assumptions`
element to its justification (a `bpfx` assume ⟹ `hpsat`, a global assume ⟹ `hax`/`hfnax`/`hdist`). -/

/-- `assumptions` after folding: base ⊎ every `.assume`-command payload. -/
theorem mem_foldl_assumptions {cmds : List OblCommand} :
    ∀ {c : OblCtx} {e : Expression.Expr},
      e ∈ (cmds.foldl OblCtx.step c).assumptions ↔
      e ∈ c.assumptions ∨ OblCommand.assume e ∈ cmds := by
  induction cmds with
  | nil => intro c e; simp [List.foldl]
  | cons cmd rest ih =>
      intro c e
      rw [List.foldl_cons, ih]
      cases cmd <;>
        simp only [OblCtx.step, List.mem_cons, List.mem_append,
          List.not_mem_nil, OblCommand.assume.injEq, reduceCtorEq, false_or, or_false,
          or_assoc]

/-- `varDefs` after folding: base ⊎ every `.varDef`-command payload. -/
theorem mem_foldl_varDefs {cmds : List OblCommand} :
    ∀ {c : OblCtx} {v : VarDef},
      v ∈ (cmds.foldl OblCtx.step c).varDefs ↔
      v ∈ c.varDefs ∨ OblCommand.varDef v ∈ cmds := by
  induction cmds with
  | nil => intro c v; simp [List.foldl]
  | cons cmd rest ih =>
      intro c v
      rw [List.foldl_cons, ih]
      cases cmd <;>
        simp only [OblCtx.step, List.mem_cons, List.mem_append,
          List.not_mem_nil, OblCommand.varDef.injEq, reduceCtorEq, false_or, or_false,
          eq_comm, or_assoc]

/-- `distincts` after folding: base ⊎ every `.distinct`-command payload. -/
theorem mem_foldl_distincts {cmds : List OblCommand} :
    ∀ {c : OblCtx} {es : List Expression.Expr},
      es ∈ (cmds.foldl OblCtx.step c).distincts ↔
      es ∈ c.distincts ∨ OblCommand.distinct es ∈ cmds := by
  induction cmds with
  | nil => intro c es; simp [List.foldl]
  | cons cmd rest ih =>
      intro c es
      rw [List.foldl_cons, ih]
      cases cmd <;>
        simp only [OblCtx.step, List.mem_cons, List.mem_append,
          List.not_mem_nil, OblCommand.distinct.injEq, reduceCtorEq, false_or, or_false,
          eq_comm, or_assoc]

/-- `defs` after folding: base ⊎ every `.fnDef`-command payload. -/
theorem mem_foldl_defs {cmds : List OblCommand} :
    ∀ {c : OblCtx} {d : FnDef},
      d ∈ (cmds.foldl OblCtx.step c).defs ↔
      d ∈ c.defs ∨ OblCommand.fnDef d ∈ cmds := by
  induction cmds with
  | nil => intro c d; simp [List.foldl]
  | cons cmd rest ih =>
      intro c d
      rw [List.foldl_cons, ih]
      cases cmd <;>
        simp only [OblCtx.step, List.mem_cons, List.mem_append,
          List.not_mem_nil, OblCommand.fnDef.injEq, reduceCtorEq, false_or, or_false,
          eq_comm, or_assoc]

/-- The commands `obligationPrefix c fns` emits are only `fnDecl`/`fnDef`/`distinct`/`assume`, never
    `.varDef`. So a `.varDef` in `obligationPrefix c fns ++ bpfx` must come from `bpfx`. -/
theorem obligationPrefix_no_varDef (c : CoreCtx) (fns : List String) (v : VarDef) :
    OblCommand.varDef v ∉ obligationPrefix c fns := by
  unfold obligationPrefix
  intro h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · -- emitFuncDecls: each emitted cmd is fnDecl/fnDef, never varDef
        obtain ⟨g, _, hg⟩ := List.mem_filterMap.mp h
        rcases hgc : c.F[g]? with _ | f
        · rw [hgc] at hg; simp at hg
        · rw [hgc] at hg; simp only [Option.map_some, Option.some.injEq] at hg
          -- `hg : emitFuncDecl f = .varDef v`; `emitFuncDecl f` is `.fnDef`/`.fnDecl`
          unfold emitFuncDecl at hg; split at hg <;> simp at hg
      · -- emitFuncAxioms: each emitted cmd is .assume, never varDef
        obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp h
        rcases hgc : c.F[g]? with _ | f
        · rw [hgc] at hg; simp at hg
        · rw [hgc] at hg; simp only [Option.map_some, Option.getD_some, funcAxiomAssumes] at hg
          obtain ⟨x, _, hx⟩ := List.mem_map.mp hg; simp at hx
    · obtain ⟨x, _, hx⟩ := List.mem_map.mp h; simp at hx
  · obtain ⟨x, _, hx⟩ := List.mem_map.mp h; simp at hx

/-- **Every `.assume` command in `obligationPrefix c fns` denotes `true`.** Such an `e` is either an
    emitted function axiom (`emitFuncAxioms`, so `e ∈ f.axioms` for a reachable factory `f` ⟹ `e ∈
    c.fnAxioms` by `SeedWF`, denoting true via `hfnax`) or a global axiom (`c.axioms.map .assume`,
    denoting true via `hax`). The distinct/decl commands are not `.assume`s. -/
theorem obligationPrefix_assume_denotes (c : CoreCtx) (fns : List String)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (hseed : c.SeedWF)
    (hax : ∀ e ∈ c.axioms, Denotes opInterp fvarVal e true)
    (hfnax : ∀ e ∈ c.fnAxioms, Denotes opInterp fvarVal e true)
    (e : Expression.Expr) (he : OblCommand.assume e ∈ obligationPrefix c fns) :
    Denotes opInterp fvarVal e true := by
  unfold obligationPrefix at he
  rcases List.mem_append.mp he with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · -- emitFuncDecls: only fnDecl/fnDef, never assume
        obtain ⟨g, _, hg⟩ := List.mem_filterMap.mp h
        rcases hgc : c.F[g]? with _ | f
        · rw [hgc] at hg; simp at hg
        · rw [hgc] at hg; simp only [Option.map_some, Option.some.injEq] at hg
          unfold emitFuncDecl at hg; split at hg <;> simp at hg
      · -- emitFuncAxioms: `e ∈ f.axioms` for a factory `f` ⟹ `e ∈ c.fnAxioms` (SeedWF) ⟹ `hfnax`
        obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp h
        rcases hgc : c.F[g]? with _ | f
        · rw [hgc] at hg; simp at hg
        · rw [hgc] at hg
          simp only [Option.map_some, Option.getD_some, funcAxiomAssumes] at hg
          obtain ⟨x, hxmem, hx⟩ := List.mem_map.mp hg
          rw [OblCommand.assume.injEq] at hx; subst hx
          have hfmem : f ∈ c.F.toArray := Factory.getElem?_is_some_implies_mem hgc
          exact hfnax x (hseed.2 f hfmem x hxmem)
    · -- distinct commands are not assumes
      obtain ⟨x, _, hx⟩ := List.mem_map.mp h; simp at hx
  · -- global axioms `c.axioms.map .assume`
    obtain ⟨x, hxmem, hx⟩ := List.mem_map.mp h
    rw [OblCommand.assume.injEq] at hx; subst hx
    exact hax x hxmem

/-- **Pairwise-distinctness transports across a type re-annotation.** Two well-typings of the same
    `es` (at `τ` and `τ₀`) give the same denotation list up to the type index, so the `Pairwise`
    fact transfers. `τ`/`τ₀`/witnesses are plain parameters (no `.choose`), so `es` can be cased
    freely: empty is trivial, and any element pins `τ = τ₀` (`HasTypeA_unique`) — then the lists are
    definitionally equal (proof-irrelevant witnesses). Feeds `distincts_sat_of_global`. -/
theorem distinctSat_reannotate {Φ Ψ : FVarCtx} {opInterp : Lambda.OpInterp simpTcInterp}
    {fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp} {es : List Expression.Expr}
    {τ τ₀ : LMonoTy}
    (hτ : ∀ e ∈ es, LExpr.HasSimpType Φ Ψ [] e τ)
    (hτ₀ : ∀ e ∈ es, LExpr.HasTypeA [] e τ₀)
    (hpw₀ : (es.attach.map (fun x => simpDenote opInterp fvarVal .nil x.1 τ₀ (hτ₀ x.1 x.2))).Pairwise (· ≠ ·)) :
    (es.attach.map (fun x => simpDenote opInterp fvarVal .nil x.1 τ
      (HasSimpType_implies_HasTypeA (hτ x.1 x.2)))).Pairwise (· ≠ ·) := by
  by_cases hemp : es = []
  · subst hemp; simp
  · obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil es hemp
    have hττ₀ : τ = τ₀ :=
      HasTypeA_unique (HasSimpType_implies_HasTypeA (hτ e0 he0)) (hτ₀ e0 he0)
    subst hττ₀
    -- same type now; the two maps agree by proof-irrelevance of the `HasTypeA` witnesses
    have : (es.attach.map (fun x => simpDenote opInterp fvarVal .nil x.1 τ
            (HasSimpType_implies_HasTypeA (hτ x.1 x.2))))
        = es.attach.map (fun x => simpDenote opInterp fvarVal .nil x.1 τ (hτ₀ x.1 x.2)) := by
      apply List.map_congr_left; intro x _; congr 1
    rw [this]; exact hpw₀

/-- **`Q`'s distinctness groups all come from `c.distincts`, and the model satisfies them.** The only
    `.distinct` commands in `Q.cmds = obligationPrefix c fns ++ bpfx` are `obligationPrefix`'s global
    `c.distincts.map .distinct` (`bpfx`/emit decls contribute none), and `hdist`'s `DistinctHolds`
    gives pairwise-distinctness at some shared type, transported to `DistinctSat` at the WF-chosen
    type via `distinctSat_reannotate`. -/
theorem distincts_sat_of_global (c : CoreCtx) (fns : List String)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (hdist : ∀ es ∈ c.distincts, DistinctHolds opInterp fvarVal es)
    (Q : OblProgram) (bpfx : List OblCommand)
    (hQcmds : Q.cmds = obligationPrefix c fns ++ bpfx)
    (hbpfx_nodist : ∀ es, OblCommand.distinct es ∉ bpfx)
    (hwfQ : OblProgramWF Q) :
    LambdaModelSatisfiesDistincts Q hwfQ opInterp fvarVal := by
  intro es hes
  -- `es ∈ Q.distincts` ⇒ `.distinct es ∈ Q.cmds`; not in `bpfx`, so in `obligationPrefix`, so global
  have hescmd : OblCommand.distinct es ∈ Q.cmds := by
    have := (mem_foldl_distincts (cmds := Q.cmds) (c := {}) (es := es)).mp hes
    simpa using this
  rw [hQcmds] at hescmd
  have hglobal : es ∈ c.distincts := by
    rcases List.mem_append.mp hescmd with h | h
    · -- `obligationPrefix = ((emitFuncDecls ++ emitFuncAxioms) ++ distinct.map) ++ axioms.map`;
      -- the only distincts are `c.distincts.map .distinct`
      unfold obligationPrefix at h
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · -- emitFuncDecls: fnDecl/fnDef only
            obtain ⟨g, _, hg⟩ := List.mem_filterMap.mp h
            rcases hgc : c.F[g]? with _ | f
            · rw [hgc] at hg; simp at hg
            · rw [hgc] at hg; simp only [Option.map_some, Option.some.injEq] at hg
              unfold emitFuncDecl at hg; split at hg <;> simp at hg
          · -- emitFuncAxioms: assume only
            obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp h
            rcases hgc : c.F[g]? with _ | f
            · rw [hgc] at hg; simp at hg
            · rw [hgc] at hg; simp only [Option.map_some, Option.getD_some, funcAxiomAssumes] at hg
              obtain ⟨x, _, hx⟩ := List.mem_map.mp hg; simp at hx
        · -- distinct commands: `c.distincts.map .distinct`
          obtain ⟨x, hxmem, hx⟩ := List.mem_map.mp h
          rw [OblCommand.distinct.injEq] at hx; subst hx; exact hxmem
      · -- global axioms: assume only
        obtain ⟨x, _, hx⟩ := List.mem_map.mp h; simp at hx
    · exact absurd h (hbpfx_nodist es)
  -- `hglobal : es ∈ c.distincts` ⇒ `DistinctHolds` at some `τ₀`; transport to `DistinctSat` at the
  -- WF-chosen `τ` via `distinctSat_reannotate` (same exprs, `τ = τ₀` by `HasTypeA_unique`).
  obtain ⟨τ₀, hty₀, hpw₀⟩ := hdist es hglobal
  show DistinctSat opInterp fvarVal es _ _
  unfold DistinctSat
  exact distinctSat_reannotate
    (fun e he => (hwfQ.distinctsWF es hes).choose_spec.2 e he) hty₀ hpw₀

/-! ## Connector 1a support: fvar→bvar denotation transport -/

/-- **`substTyVars` distributes over the iterated arrow.** Stated directly on
    `List.foldr LMonoTy.arrow` (which `funcSig`/`FnDef.OpConsistent` use, and which is definitionally
    `mkArrow'`). Turns the emitted head's `TyDenote` type into the `SortDenote (mkArrow …)` shape
    `SortDenote.applyArgs` consumes. -/
theorem substTyVars_foldr_arrow (ret : LMonoTy) :
    ∀ (argTys : List LMonoTy),
    LMonoTy.substTyVars simpTyVarVal (List.foldr LMonoTy.arrow ret argTys)
    = LSort.mkArrow (LMonoTy.substTyVars simpTyVarVal ret)
        (argTys.map (LMonoTy.substTyVars simpTyVarVal))
  | [] => rfl
  | a :: as => by
      rw [show LMonoTy.substTyVars simpTyVarVal (List.foldr LMonoTy.arrow ret (a :: as))
            = LSort.tcons "arrow" [LMonoTy.substTyVars simpTyVarVal a,
                LMonoTy.substTyVars simpTyVarVal (List.foldr LMonoTy.arrow ret as)] from rfl]
      rw [substTyVars_foldr_arrow ret as]; rfl

/-- Reindex a `BVarVal` over `argTys` as an `HList SortDenote` over `argTys.map substTyVars` — the
    argument list `SortDenote.applyArgs` (and `InterpConsistentBody`) consume. Definitional, since
    `TyDenote ρ a = SortDenote (a.substTyVars ρ)`. -/
def reindexArgs :
    (argTys : List LMonoTy) → Lambda.BVarVal simpTcInterp simpTyVarVal argTys →
    HList (Lambda.SortDenote simpTcInterp) (argTys.map (LMonoTy.substTyVars simpTyVarVal))
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons x (reindexArgs _ xs)

private theorem cast_arrow_app_1a {A A' B B' : Type} (hA : A = A') (hB : B = B')
    (hAB : (A → B) = (A' → B')) (f : A → B) (x : A) :
    (cast hAB f) (cast hA x) = cast hB (f x) := by
  subst hA; subst hB; rfl

/-- **The `applyBVarVal ↔ SortDenote.applyArgs` bridge (Lambda side).** Applying a curried head to a
    `BVarVal` (as `FnDef.OpConsistent` does) equals applying the same head — reshaped across
    `substTyVars_foldr_arrow` to the `mkArrow` sort — to the reindexed argument HList (as
    `InterpConsistentBody` does). Peels one argument per step via `cast_arrow_app_1a`. -/
theorem applyBVarVal_eq_applyArgs (ret : LMonoTy) :
    (argTys : List LMonoTy) →
    (hd : Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow ret argTys)) →
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal argTys) →
    applyBVarVal argTys ret hd bvarVal
      = Lambda.SortDenote.applyArgs simpTcInterp
          (cast (congrArg (Lambda.SortDenote simpTcInterp) (substTyVars_foldr_arrow ret argTys)) hd)
          (reindexArgs argTys bvarVal)
  | [], hd, .nil => by
      simp only [applyBVarVal, reindexArgs]; rfl
  | a :: as, hd, .cons x xs => by
      show applyBVarVal as ret (hd x) xs = _
      rw [applyBVarVal_eq_applyArgs ret as (hd x) xs]
      have hstep : Lambda.SortDenote.applyArgs simpTcInterp
            (cast (congrArg (Lambda.SortDenote simpTcInterp) (substTyVars_foldr_arrow ret (a :: as))) hd)
            (reindexArgs (a :: as) (.cons x xs))
          = Lambda.SortDenote.applyArgs simpTcInterp
              ((cast (congrArg (Lambda.SortDenote simpTcInterp)
                  (substTyVars_foldr_arrow ret (a :: as))) hd) x)
              (reindexArgs as xs) := rfl
      rw [hstep]
      congr 1
      have hA : Lambda.TyDenote simpTcInterp simpTyVarVal a
          = Lambda.SortDenote simpTcInterp (LMonoTy.substTyVars simpTyVarVal a) := rfl
      have hB : Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow ret as)
          = Lambda.SortDenote simpTcInterp
              (LSort.mkArrow (LMonoTy.substTyVars simpTyVarVal ret)
                (as.map (LMonoTy.substTyVars simpTyVarVal))) :=
        congrArg (Lambda.SortDenote simpTcInterp) (substTyVars_foldr_arrow ret as)
      have hbig := cast_arrow_app_1a hA hB
        (congrArg (Lambda.SortDenote simpTcInterp) (substTyVars_foldr_arrow ret (a :: as))) hd x
      rw [cast_eq] at hbig; exact hbig.symm

/-- **`emitFuncDecl f = .fnDef d` inversion.** Only the non-recursive-with-body branch emits a `.fnDef`,
    and it emits exactly the fvar→bvar-lifted record. Recovers `f`'s non-recursiveness, its body, and
    `d`'s field values. -/
theorem emitFuncDecl_fnDef_inv (f : LFunc CoreLParams) (d : FnDef) (h : emitFuncDecl f = .fnDef d) :
    f.isRecursive = false ∧ ∃ body, f.body = some body ∧
      d = { name := f.name.name, argTys := f.inputs.values, retTy := f.output,
            body := LExpr.substFvarsLifting body (funcBvarSubst f) } := by
  unfold emitFuncDecl at h
  split at h
  · rename_i body hnr hbody
    rw [OblCommand.fnDef.injEq] at h
    exact ⟨hnr, body, hbody, h.symm⟩
  · exact absurd h (by simp)

/-- **`.fnDef d ∈ emitFuncDecls F fns` provenance.** A declaration command emitted by `emitFuncDecls`
    resolves to a factory function `g ∈ fns` whose `emitFuncDecl` is that `.fnDef d`. -/
theorem mem_emitFuncDecls_fnDef (F : Lambda.Factory CoreLParams) (fns : List String) (d : FnDef)
    (h : OblCommand.fnDef d ∈ emitFuncDecls F fns) :
    ∃ g f, g ∈ fns ∧ F[g]? = some f ∧ emitFuncDecl f = .fnDef d := by
  unfold emitFuncDecls at h
  obtain ⟨g, hg, hgeq⟩ := List.mem_filterMap.mp h
  rcases hgc : F[g]? with _ | f
  · rw [hgc] at hgeq; simp at hgeq
  · rw [hgc] at hgeq; simp only [Option.map_some, Option.some.injEq] at hgeq
    exact ⟨g, f, hg, hgc, hgeq⟩

/-- **`emitFuncAxioms` emits only `.assume`s.** So a `.fnDef` in `obligationPrefix` must come from the
    `emitFuncDecls` phase, not the axioms/distinct/global-axiom tail. -/
theorem obligationPrefix_fnDef_mem_decls (c : CoreCtx) (fns : List String) (d : FnDef)
    (h : OblCommand.fnDef d ∈ obligationPrefix c fns) :
    OblCommand.fnDef d ∈ emitFuncDecls c.F fns := by
  unfold obligationPrefix at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact h
      · -- emitFuncAxioms: assume only
        obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp h
        rcases hgc : c.F[g]? with _ | f
        · rw [hgc] at hg; simp at hg
        · rw [hgc] at hg; simp only [Option.map_some, Option.getD_some, funcAxiomAssumes] at hg
          obtain ⟨x, _, hx⟩ := List.mem_map.mp hg; simp at hx
    · obtain ⟨x, _, hx⟩ := List.mem_map.mp h; simp at hx
  · obtain ⟨x, _, hx⟩ := List.mem_map.mp h; simp at hx


/-! ## Connector 1a: the per-function `InterpConsistentBody → FnDef.OpConsistent` bridge

`emitFunc_OpConsistent` chains: LHS `applyBVarVal (opInterp head) bvarVal`
=[`applyBVarVal_eq_applyArgs`] `applyArgs (opInterp head') (reindexArgs bvarVal)`
=[`InterpConsistentBody`] `denote (fvarVal.withArgs bindings args) .nil body`
=[`substFvarsLifting_denote` + `denote_suffix_irrel`] `denote bvarVal (substFvarsLifting body …)` =
RHS. The supporting alignment lemmas discharge the fvar↔bvar reindex and the `substFvarsLifting_denote`
wiring. -/

/-- The ICB/`FnDef` binding list's second projection is `f.inputs.values` type-substituted. -/
theorem inputs_bindings_snd (f : LFunc CoreLParams) :
    (f.inputs.map (fun (p : CoreLParams.Identifier × LMonoTy) => (p.1, LMonoTy.substTyVars simpTyVarVal p.2))).map Prod.snd
    = f.inputs.values.map (LMonoTy.substTyVars simpTyVarVal) := by
  rw [ListMap.values_eq_map_snd, List.map_map, List.map_map]; rfl

/-- The ICB/`FnDef` binding list's first projection is `f.inputs.keys`. -/
theorem inputs_bindings_fst (f : LFunc CoreLParams) :
    (f.inputs.map (fun (p : CoreLParams.Identifier × LMonoTy) => (p.1, LMonoTy.substTyVars simpTyVarVal p.2))).map Prod.fst
    = f.inputs.keys := by
  rw [ListMap.keys_eq_map_fst, List.map_map]; rfl

/-- Casting an `opInterp` value along a sort equality re-indexes it to `opInterp` at the new sort. -/
theorem cast_opInterp (opInterp : Lambda.OpInterp simpTcInterp) (name : String) {X Y : LSort}
    (h : X = Y) : cast (congrArg (Lambda.SortDenote simpTcInterp) h) (opInterp name X) = opInterp name Y := by
  subst h; rfl

/-- `SortDenote.applyArgs` on a fixed head is invariant under casting its arg-sort list. -/
theorem applyArgs_cast_congr (name : String) (opInterp : Lambda.OpInterp simpTcInterp)
    (retS : LSort) {S1 S2 : List LSort} (h : S1 = S2) (args : HList (Lambda.SortDenote simpTcInterp) S1) :
    Lambda.SortDenote.applyArgs simpTcInterp (opInterp name (LSort.mkArrow retS S1)) args
    = Lambda.SortDenote.applyArgs simpTcInterp (opInterp name (LSort.mkArrow retS S2)) (HList.cast h args) := by
  subst h; rfl

/-- **HList extensionality**: two HLists over the same index list are equal if all lookups agree. -/
theorem HList.ext {α} {β : α → Type} : ∀ {as : List α} (h1 h2 : HList β as),
    (∀ i (a : α) (hi : as[i]? = some a), h1.get i hi = h2.get i hi) → h1 = h2
  | [], .nil, .nil, _ => rfl
  | a :: as, .cons x xs, .cons y ys, hget => by
      have hx : x = y := by have := hget 0 a (by simp); simpa using this
      subst hx; congr 1
      exact HList.ext xs ys (fun i b hi => by have := hget (i+1) b (by simpa using hi); simpa using this)

/-- `reindexArgs`'s `i`-th lookup is the `i`-th `bvarVal` component. -/
theorem reindexArgs_get :
    ∀ (argTys : List LMonoTy) (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal argTys)
      (i : Nat) (a : LMonoTy) (hia : argTys[i]? = some a)
      (hi : (argTys.map (LMonoTy.substTyVars simpTyVarVal))[i]? = some (LMonoTy.substTyVars simpTyVarVal a)),
      (reindexArgs argTys bvarVal).get i hi = bvarVal.get i hia
  | a :: as, .cons x xs, 0, a', hia, hi => by have : a = a' := by simpa using hia
                                              subst this; simp [reindexArgs]
  | a :: as, .cons x xs, i+1, a', hia, hi => by
      simp only [reindexArgs, HList.get_cons_succ]
      exact reindexArgs_get as xs i a' (by simpa using hia) (by simpa using hi)

/-- `funcBvarSubst`'s replacement values are the range-indexed bvars. -/
theorem funcBvarSubst_values (f : LFunc CoreLParams) :
    (funcBvarSubst f).map Prod.snd = (List.range f.inputs.length).map (fun i => (LExpr.bvar () i : Expression.Expr)) := by
  rw [funcBvarSubst_eq_map, List.map_map]; rfl

/-- The `i`-th `funcBvarSubst` replacement value (for `i` in range) is `.bvar () i`. -/
theorem funcBvarSubst_values_getElem (f : LFunc CoreLParams) (i : Nat) (h : i < f.inputs.length) :
    ((funcBvarSubst f).map Prod.snd)[i]? = some (LExpr.bvar () i) := by
  rw [funcBvarSubst_values, List.getElem?_map, List.getElem?_range h]; rfl

theorem funcBvarSubst_length (f : LFunc CoreLParams) : (funcBvarSubst f).length = f.inputs.length := by
  rw [funcBvarSubst_eq_map]; simp

theorem inputs_values_length (f : LFunc CoreLParams) : f.inputs.values.length = f.inputs.length := by
  rw [ListMap.values_eq_map_snd]; simp

/-- **`denoteArgs` of the `funcBvarSubst` replacement bvars is `reindexArgs`.** Each replacement `.bvar () i`
    denotes (under `bvarVal`) to `bvarVal.get i`, matching `reindexArgs`. The `h_denotes` obligation of
    `substFvarsLifting_denote`. -/
theorem denoteArgs_funcBvarSubst_eq_reindex
    (f : LFunc CoreLParams) (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal f.inputs.values)
    (h_wt : List.Forall₂ (LExpr.HasTypeA f.inputs.values)
        ((funcBvarSubst f).map Prod.snd) f.inputs.values) :
    Lambda.denoteArgs simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
        ((funcBvarSubst f).map Prod.snd) f.inputs.values h_wt
    = reindexArgs f.inputs.values bvarVal := by
  apply HList.ext
  intro i s hi
  have hlt : i < f.inputs.values.length := by
    have := List.getElem?_eq_some_iff.mp hi
    simpa using this.1
  obtain ⟨a, hia⟩ : ∃ a, f.inputs.values[i]? = some a := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hsa : s = LMonoTy.substTyVars simpTyVarVal a := by
    rw [List.getElem?_map, hia] at hi; simpa using hi.symm
  subst hsa
  rw [reindexArgs_get f.inputs.values bvarVal i a hia hi]
  have hbv : ((funcBvarSubst f).map Prod.snd)[i]? = some (LExpr.bvar () i) := by
    apply funcBvarSubst_values_getElem; rw [← inputs_values_length]; exact hlt
  rw [Lambda.denoteArgs_get (tcInterp := simpTcInterp) (opInterp := opInterp) (fvarVal := fvarVal)
      (vt := simpTyVarVal) (bvarVal := bvarVal) h_wt i hbv hia hi]
  rw [Lambda.denote_bvar]

/-- A range-bvar list `[.bvar (pre+0), …, .bvar (pre+n-1)]` is `Forall₂`-typed at `pre ++ Δ` by `Δ`. -/
theorem forall2_bvars_go (Δ : List LMonoTy) :
    ∀ (pre : List LMonoTy), List.Forall₂ (LExpr.HasTypeA (pre ++ Δ))
        ((List.range Δ.length).map (fun i => (LExpr.bvar () (pre.length + i) : Expression.Expr))) Δ := by
  induction Δ with
  | nil => intro pre; exact .nil
  | cons a as ih =>
      intro pre
      rw [show (a :: as).length = as.length + 1 from rfl, List.range_succ_eq_map, List.map_cons]
      refine List.Forall₂.cons ?_ ?_
      · simp only [Nat.add_zero]
        exact LExpr.HasTypeA.bvar (by rw [List.getElem?_append_right (by omega)]; simp)
      · have := ih (pre ++ [a])
        simp only [List.length_append, List.length_singleton] at this
        rw [List.append_assoc] at this
        rw [List.map_map]
        simpa [Nat.add_assoc, Nat.add_comm 1, Function.comp] using this

/-- The `funcBvarSubst` replacement bvars are `Forall₂`-typed at `f.inputs.values` by `f.inputs.values`. -/
theorem h_wt_lemma (f : LFunc CoreLParams) :
    List.Forall₂ (LExpr.HasTypeA f.inputs.values)
      ((funcBvarSubst f).map Prod.snd) f.inputs.values := by
  rw [funcBvarSubst_values]
  have := forall2_bvars_go f.inputs.values []
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at this
  rw [inputs_values_length] at this
  exact this

/-- `f.inputs.keys.zip f.inputs.values` recovers `f.inputs` (as a plain list). -/
theorem keys_zip_values (f : LFunc CoreLParams) : f.inputs.keys.zip f.inputs.values = f.inputs.toList := by
  rw [ListMap.keys_eq_map_fst, ListMap.values_eq_map_snd]
  show (f.inputs.map Prod.fst).zip (f.inputs.map Prod.snd) = f.inputs
  induction f.inputs with
  | nil => rfl
  | cons hd tl ih => cases hd; simp [List.zip]

/-- A `CoreIdent` is determined by its name (metadata is `Unit`). -/
theorem coreident_ext_name {a b : CoreLParams.Identifier} (h : a.name = b.name) : a = b := by
  cases a; cases b; simp_all

/-- **`Map.find?` / `funcFVarCtx`-membership compatibility (list form).** For a name-nodup assoc list,
    a `find?` hit and a name-indexed `funcFVarCtx`-style membership agree on the value. -/
theorem find_compat_go (m : List (CoreLParams.Identifier × LMonoTy)) (hnd : (m.map Prod.fst).Nodup)
    (name : CoreLParams.Identifier) (t : LMonoTy)
    (hfind : Map.find? m name = some t)
    (σ : LMonoTy) (hmem : (name.name, σ) ∈ m.map (fun (p : CoreLParams.Identifier × LMonoTy) => (p.1.name, p.2))) :
    σ = t := by
  induction m with
  | nil => simp [Map.find?] at hfind
  | cons hd tl ih =>
      obtain ⟨hid, hty⟩ := hd
      rw [List.map_cons, List.nodup_cons] at hnd
      simp only [Map.find?] at hfind
      rw [List.map_cons, List.mem_cons] at hmem
      by_cases hkey : hid = name
      · rw [if_pos hkey] at hfind
        have ht : hty = t := by simpa using hfind
        rcases hmem with h | h
        · rw [Prod.mk.injEq] at h; rw [← ht]; exact h.2
        · exfalso
          obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
          rw [Prod.mk.injEq] at hpe
          apply hnd.1
          have hp1 : p.1 = hid := coreident_ext_name (by rw [hpe.1, hkey])
          exact List.mem_map.mpr ⟨p, hp, hp1⟩
      · rw [if_neg hkey] at hfind
        rcases hmem with h | h
        · rw [Prod.mk.injEq] at h
          exfalso; apply hkey
          exact (coreident_ext_name h.1).symm
        · exact ih hnd.2 hfind h

/-- The `hcompat` premise `HasSimpType_fvars_annotated` needs at `tyMap = f.inputs.keys.zip f.inputs.values`,
    `Φ = funcFVarCtx f`: a `find?` hit matches any `funcFVarCtx`-membership value. -/
theorem funcFVarCtx_compat (f : LFunc CoreLParams) (hkeys : f.inputs.keys.Nodup)
    (name : CoreLParams.Identifier) (t : LMonoTy)
    (hfind : Map.find? (f.inputs.keys.zip f.inputs.values) name = some t)
    (σ : LMonoTy) (hmem : (name.name, σ) ∈ funcFVarCtx f) :
    σ = t := by
  rw [keys_zip_values] at hfind
  have hfind' : Map.find? f.inputs.toList name = some t := hfind
  refine find_compat_go f.inputs.toList ?_ name t hfind' σ hmem
  rw [← ListMap.keys_eq_map_fst]; exact hkeys

/-- `funcBvarSubst`'s keys are `f.inputs.keys`. -/
theorem funcBvarSubst_keys (f : LFunc CoreLParams) : (funcBvarSubst f).map Prod.fst = f.inputs.keys := by
  rw [funcBvarSubst_eq_map, List.map_map, ListMap.keys_eq_map_fst]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [Function.comp, List.getElem_map, List.getElem_range]
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h1 ⊢; omega),
        List.getElem_map, Option.getD_some]

/- **`fvars_annotated_by` from `HasSimpType`.** A body well-typed at fvar context `Φ` has every applied
   free-variable head annotated consistently with any `tyMap` whose entries `Φ` agrees with — exactly the
   `substFvarsLifting_denote` annotation premise for the source body. Mutual with the spine version. -/
mutual
theorem HasSimpType_fvars_annotated {tyMap : Map CoreLParams.Identifier LMonoTy}
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : List LMonoTy} {body : Expression.Expr} {τ : LMonoTy}
    (hcompat : ∀ (name : CoreLParams.Identifier) (t : LMonoTy),
        Map.find? tyMap name = some t → ∀ σ, (name.name, σ) ∈ Φ → σ = t)
    (he : LExpr.HasSimpType Φ Ψ Δ body τ) :
    Lambda.fvars_annotated_by tyMap body := by
  match he with
  | .const c _ => exact True.intro
  | .bvar i t _ _ => exact True.intro
  | .app fn arg rty hspine => exact AppSpine_fvars_annotated hcompat hspine
  | .fvarNullary f t rty hspine => exact AppSpine_fvars_annotated hcompat hspine
  | .ite c t t' d hc ht he_ =>
    exact ⟨HasSimpType_fvars_annotated hcompat hc,
           HasSimpType_fvars_annotated hcompat ht,
           HasSimpType_fvars_annotated hcompat he_⟩
  | .eq e1 e2 t _ he1 he2 =>
    exact ⟨HasSimpType_fvars_annotated hcompat he1, HasSimpType_fvars_annotated hcompat he2⟩
  | .quant qty qbody qk qname qtr qτtr _ htr hbody =>
    -- `fvars_annotated_by (.quant … tr body) = annotated tr ∧ annotated body`; both from IH now
    exact ⟨HasSimpType_fvars_annotated hcompat htr, HasSimpType_fvars_annotated hcompat hbody⟩

theorem AppSpine_fvars_annotated {tyMap : Map CoreLParams.Identifier LMonoTy}
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : List LMonoTy} {body : Expression.Expr}
    {acc : List LMonoTy} {rty : LMonoTy}
    (hcompat : ∀ (name : CoreLParams.Identifier) (t : LMonoTy),
        Map.find? tyMap name = some t → ∀ σ, (name.name, σ) ∈ Φ → σ = t)
    (hspine : LExpr.AppSpine Φ Ψ Δ body acc rty) :
    Lambda.fvars_annotated_by tyMap body := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    exact ⟨AppSpine_fvars_annotated hcompat hrest, HasSimpType_fvars_annotated hcompat harg⟩
  | .fvar f τ acc' rty hmem hcollect hbase =>
    intro ty' hfind
    exact hcompat f ty' hfind τ hmem
  | .op o oty acc' rty hop hcollect => exact True.intro
  | .fnOp o oty acc' rty hmem hnpre hcollect hbase => exact True.intro
termination_by structural hspine
end

/-- **Connector 1a, per function.** For a non-recursive factory function `f` whose (source) body types
    at its fvar-formal context and whose model consistency is `InterpConsistentBody`, the emitted `fnDef`
    `d` (fvar→bvar-lifted body) is `FnDef.OpConsistent`. The bridge chains `applyBVarVal_eq_applyArgs`,
    `InterpConsistentBody`, `substFvarsLifting_denote`, and `denote_suffix_irrel` (body closed at 0). -/
theorem emitFunc_OpConsistent {Ψ : FnCtx} (f : LFunc CoreLParams) (body : Expression.Expr)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (hkeys : f.inputs.keys.Nodup)
    (hbodyty : LExpr.HasSimpType (funcFVarCtx f) Ψ [] body f.output)
    (icb : Lambda.LFunc.InterpConsistentBody simpTcInterp opInterp f body)
    (d : FnDef)
    (hd : d = { name := f.name.name, argTys := f.inputs.values, retTy := f.output,
                body := LExpr.substFvarsLifting body (funcBvarSubst f) })
    (htA : LExpr.HasTypeA d.argTys d.body d.retTy) :
    d.OpConsistent opInterp fvarVal htA := by
  subst hd
  unfold FnDef.OpConsistent
  intro bvarVal
  simp only []
  rw [applyBVarVal_eq_applyArgs f.output f.inputs.values _ bvarVal]
  rw [cast_opInterp opInterp f.name.name (substTyVars_foldr_arrow f.output f.inputs.values)]
  have hbind := inputs_bindings_snd f
  rw [applyArgs_cast_congr f.name.name opInterp (LMonoTy.substTyVars simpTyVarVal f.output) hbind.symm
        (reindexArgs f.inputs.values bvarVal)]
  have hicb := icb simpTyVarVal fvarVal (HasSimpType_implies_HasTypeA hbodyty)
      (HList.cast hbind.symm (reindexArgs f.inputs.values bvarVal))
  rw [hicb]
  show LExpr.denote simpTcInterp opInterp
      (fvarVal.withArgs _ (HList.cast hbind.symm (reindexArgs f.inputs.values bvarVal)))
      simpTyVarVal .nil body f.output _
    = LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
        (LExpr.substFvarsLifting body (funcBvarSubst f)) f.output htA
  have hbodyA0 : LExpr.HasTypeA [] body f.output := HasSimpType_implies_HasTypeA hbodyty
  have hbodyAout : LExpr.HasTypeA f.inputs.values body f.output :=
    HasTypeA_weaken hbodyA0 (Lambda.HasTypeA_nil_lcAt hbodyA0)
  have h_wt := h_wt_lemma f
  have h_keys : (funcBvarSubst f).map Prod.fst
      = (f.inputs.map (fun (p : CoreLParams.Identifier × LMonoTy) =>
          (p.1, LMonoTy.substTyVars simpTyVarVal p.2))).map Prod.fst := by
    rw [inputs_bindings_fst f, funcBvarSubst_keys]
  have h_len : (funcBvarSubst f).length
      = (f.inputs.map (fun (p : CoreLParams.Identifier × LMonoTy) =>
          (p.1, LMonoTy.substTyVars simpTyVarVal p.2))).length := by
    rw [funcBvarSubst_length]; simp
  have h_tys_len : f.inputs.values.length = (funcBvarSubst f).length := by
    rw [funcBvarSubst_length, inputs_values_length]
  have h_annot : Lambda.fvars_annotated_by
      (((funcBvarSubst f).map Prod.fst).zip f.inputs.values) body := by
    apply HasSimpType_fvars_annotated (Ψ := Ψ) (Δ := []) _ hbodyty
    intro nm tt hfind σ hσ
    rw [funcBvarSubst_keys] at hfind
    exact funcFVarCtx_compat f hkeys nm tt hfind σ hσ
  have hsfd := substFvarsLifting_denote simpTcInterp opInterp fvarVal simpTyVarVal
      (body := body) (τ := f.output)
      (bindings := funcBvarSubst f)
      (sortBindings := f.inputs.map (fun (p : CoreLParams.Identifier × LMonoTy) =>
          (p.1, LMonoTy.substTyVars simpTyVarVal p.2)))
      (Δ_outer := f.inputs.values)
      bvarVal hbodyAout htA
      (HList.cast hbind.symm (reindexArgs f.inputs.values bvarVal))
      h_keys h_len (tys := f.inputs.values) h_tys_len hbind h_wt ?_ h_annot
  · rw [hsfd]
    exact (Lambda.denote_suffix_irrel simpTcInterp opInterp _ simpTyVarVal
      (Δ₁ := []) (Δ₂ := f.inputs.values) (Δ₂' := [])
      (Lambda.HasTypeA_nil_lcAt hbodyA0) hbodyAout hbodyA0 .nil bvarVal .nil).symm
  · rw [denoteArgs_funcBvarSubst_eq_reindex f opInterp fvarVal bvarVal h_wt]

/-- The source body typing + key-nodup a resolved non-recursive factory function contributes, read off
    `FactoryFuncsWF` (body typed at the reconstruction prefix, lifted to the full `fnCtx c.F`). -/
theorem factory_func_body_typed {c : CoreCtx} (hffwf : c.FactoryFuncsWF)
    {g : String} {f : LFunc CoreLParams} (hres : c.F[g]? = some f)
    (hnr : f.isRecursive = false) {body : Expression.Expr} (hbody : f.body = some body) :
    f.inputs.keys.Nodup ∧
    LExpr.HasSimpType (funcFVarCtx f) (Lambda.Factory.fnCtx c.F) [] body f.output := by
  have hfmem : f ∈ c.F.toArray.toList :=
    Array.mem_def.mp (Factory.getElem?_is_some_implies_mem hres)
  obtain ⟨pre, suf, hsplit⟩ := List.append_of_mem hfmem
  obtain ⟨hnres, hkeys, _hbnr, hbodyPre⟩ := hffwf pre f suf hsplit
  refine ⟨hkeys, ?_⟩
  have hfnceq : Lambda.Factory.fnCtx c.F = pre.map funcSig ++ (f :: suf).map funcSig := by
    rw [Lambda.Factory.fnCtx, hsplit, List.map_append]
  rw [hfnceq]
  exact HasSimpType_mono_Ψ _ (hbodyPre hnr body hbody)


/-- **A factory element's `getElem` is a member of its array.** (Plain-`getElem` companion of
    `Factory.getElem?_is_some_implies_mem`; unfolds `Factory.get`.) -/
theorem fac_getElem_mem {F : Lambda.Factory CoreLParams} {g : String} (hg : g ∈ F) :
    (F[g]'hg) ∈ F.toArray := by
  change Lambda.Factory.get F g hg ∈ F.toArray
  unfold Lambda.Factory.get; exact Array.getElem_mem _

/-- **A factory element's name matches its key.** (Plain-`getElem` companion of `Factory.getElem?_name`.) -/
theorem fac_getElem_name {F : Lambda.Factory CoreLParams} {g : String} (hg : g ∈ F) :
    (F[g]'hg).name.name = g := by
  change (Lambda.Factory.get F g hg).name.name = g
  unfold Lambda.Factory.get; exact F.nameMapConsistent hg

/-- **The reconstructed factory agrees with `Core.Factory` on the seed's names.** For `g ∈ Core.Factory`,
    `c.F[g] = Core.Factory[g]`: `Core.Factory[g]` is a member of `Core.Factory.toArray` (with name `g`),
    hence — since `SeedWF` makes `Core.Factory.toArray` an array prefix of `c.F.toArray` — a member of
    `c.F.toArray`, and name-nodup (`mem_name_eq_getElem`) pins `c.F[g]` to it. -/
theorem cF_eq_coreFactory {c : CoreCtx} (extra : List (LFunc CoreLParams))
    (hext : c.F.toArray.toList = Core.Factory.toArray.toList ++ extra)
    {g : String} (hg : g ∈ Core.Factory) :
    ∃ (hg' : g ∈ c.F), c.F[g]'hg' = Core.Factory[g]'hg := by
  have hmemcF : (Core.Factory[g]'hg) ∈ c.F.toArray := by
    rw [Array.mem_def, hext, List.mem_append]
    exact Or.inl (Array.mem_def.mp (fac_getElem_mem hg))
  exact Factory.mem_name_eq_getElem hmemcF (fac_getElem_name hg)

/-- **`InterpConsistent` restricts along the `SeedWF` prefix to `Core.Factory`.** A model consistent
    with the reconstructed `c.F` is consistent with `Core.Factory` (its seed): each seed function
    resolves to the same `LFunc` in both (`cF_eq_coreFactory`), so `hFC`'s body/eval clauses transport. -/
theorem interpConsistent_coreFactory_of_cF {c : CoreCtx}
    {opInterp : Lambda.OpInterp simpTcInterp}
    (hseed : c.SeedWF)
    (hFC : Lambda.Factory.InterpConsistent simpTcInterp opInterp c.F) :
    Lambda.Factory.InterpConsistent simpTcInterp opInterp Core.Factory := by
  obtain ⟨⟨extra, hext⟩, _⟩ := hseed
  refine ⟨?_, ?_⟩
  · intro g hg body hbody
    obtain ⟨hg', heq⟩ := cF_eq_coreFactory extra hext hg
    have := hFC.1 g hg' body (by rw [heq]; exact hbody)
    rw [heq] at this; exact this
  · intro g hg ceval hceval
    obtain ⟨hg', heq⟩ := cF_eq_coreFactory extra hext hg
    have := hFC.2 g hg' ceval (by rw [heq]; exact hceval)
    rw [heq] at this; exact this

/-- **Connector 1b — `OpInterpConsistent` from a factory-consistent model.** A model consistent with
    `c.F` (which, by `SeedWF`, extends the default `Core.Factory`) interprets each built-in operator as
    its concrete Lean function. Restricts `hFC` to `Core.Factory` (`interpConsistent_coreFactory_of_cF`)
    and applies the seed builtin-consistency premise `hbc` (discharged downstream — including the
    guarded div/mod ops via the model-chosen div-by-zero values it supplies). The premise yields
    `divByZero`/`modByZero` existentially; the emitted obligation program's `Valid` quantifies over
    them, so they thread through the model-transfer discharge. -/
theorem opInterpConsistent_of_factoryConsistent {c : CoreCtx}
    {opInterp : Lambda.OpInterp simpTcInterp}
    (hbc : CoreCtx.SeedBuiltinConsistent)
    (hseed : c.SeedWF)
    (hFC : Lambda.Factory.InterpConsistent simpTcInterp opInterp c.F) :
    ∃ divByZero modByZero, OpInterpConsistent divByZero modByZero opInterp :=
  hbc (interpConsistent_coreFactory_of_cF hseed hFC)

/-- **Connector 1a — `FnDefs.OpConsistent` from a factory-consistent model.** Every emitted `fnDef`
    `d ∈ P.defs` (the fvar→bvar lift of some reachable non-recursive factory function `f`'s body) is
    op-consistent. Provenance: `d ∈ P.defs` ⟹ `.fnDef d ∈ obligationPrefix` (not `bpfx`, which carries
    no `fnDef`) ⟹ resolves to a factory `f` with `emitFuncDecl f = .fnDef d`; `FactoryFuncsWF` supplies
    `f`'s source-body typing (+ key-nodup) and `hFC`'s `InterpConsistentBody` clause supplies the model
    consistency, both fed to the per-function bridge `emitFunc_OpConsistent`. -/
theorem fnDefsOpConsistent_of_factoryConsistent {c : CoreCtx} {fns : List String}
    {opInterp : Lambda.OpInterp simpTcInterp}
    {fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp}
    (hffwf : c.FactoryFuncsWF)
    (hFC : Lambda.Factory.InterpConsistent simpTcInterp opInterp c.F)
    {P : OblProgram} {bpfx : List OblCommand}
    (hcmds : P.cmds = obligationPrefix c fns ++ bpfx)
    (hbpfx_nofndef : ∀ d, OblCommand.fnDef d ∉ bpfx)
    (ht : ∀ d ∈ P.defs, LExpr.HasTypeA d.argTys d.body d.retTy) :
    FnDefs.OpConsistent opInterp fvarVal P.defs ht := by
  intro d hd
  -- Provenance: `d ∈ P.defs` ⟹ `.fnDef d ∈ P.cmds`; not in `bpfx`, so in `emitFuncDecls`.
  have hdcmd : OblCommand.fnDef d ∈ P.cmds := by
    have := (mem_foldl_defs (cmds := P.cmds) (c := {}) (d := d)).mp hd
    simpa using this
  rw [hcmds] at hdcmd
  have hdecls : OblCommand.fnDef d ∈ emitFuncDecls c.F fns := by
    rcases List.mem_append.mp hdcmd with h | h
    · exact obligationPrefix_fnDef_mem_decls c fns d h
    · exact absurd h (hbpfx_nofndef d)
  obtain ⟨g, f, hg, hres, hemit⟩ := mem_emitFuncDecls_fnDef c.F fns d hdecls
  obtain ⟨hnr, body, hbody, hdeq⟩ := emitFuncDecl_fnDef_inv f d hemit
  obtain ⟨hkeys, hbodyty⟩ := factory_func_body_typed hffwf hres hnr hbody
  -- ICB for `f` from `hFC`'s body clause (bridge `F[g]? = some f` ↔ `F[g] = f`).
  have hgmem : g ∈ c.F := Factory.getElem?_some_implies_mem hres
  have hFf : c.F[g] = f := Factory.getElem?_some_getElem hres
  have icb : Lambda.LFunc.InterpConsistentBody simpTcInterp opInterp f body := by
    have := hFC.1 g hgmem body (by rw [hFf]; exact hbody)
    rw [hFf] at this; exact this
  exact emitFunc_OpConsistent (Ψ := Lambda.Factory.fnCtx c.F) f body opInterp fvarVal
    hkeys hbodyty icb d hdeq (ht d hd)

/-- **Half B — the model-transfer discharge.** Given the factory-consistent model (`hFC`), the prefix
    axiom/fn-axiom/distinct facts (`hax`/`hfnax`/`hdist`, from `ProcValid`) with `SeedWF` (so every
    emitted fn-axiom is a `c.fnAxioms` entry), and the fired-path facts (`hpsat : PrefixSat` — `bpfx`
    assumes denote true, its varDefs pinned), `OblProgram.Valid Q` forces `Q.obligation` to denote
    `true`. Discharges the five hypotheses at the model:
      • `OpInterpConsistent` ← `opInterpConsistent_of_factoryConsistent` (1b);
      • `FnDefs.OpConsistent Q.defs` ← `fnDefsOpConsistent_of_factoryConsistent` (1a);
      • `VarDefs.Consistent Q.varDefs` ← every `.varDef ∈ Q.cmds` is in `bpfx` (globals have none,
        `obligationPrefix_no_varDef`), pinned by `hpsat.2`;
      • `LambdaModelSatisfiesAsms Q` ← every `.assume e ∈ Q.cmds` is a `bpfx` assume (`hpsat.1`) or an
        `obligationPrefix` assume — a global axiom (`hax`) or an emitted fn-axiom (`hfnax` via `SeedWF`);
      • `LambdaModelSatisfiesDistincts Q` ← every `.distinct ∈ Q.cmds` is a global distinct (`hdist`). -/
theorem obligationValid_denotes (c : CoreCtx) (ss : Statements) (fns : List String)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (hbc : CoreCtx.SeedBuiltinConsistent)
    (hffwf : c.FactoryFuncsWF)
    (hseed : c.SeedWF)
    (hFC : Lambda.Factory.InterpConsistent simpTcInterp opInterp c.F)
    (hax : ∀ e ∈ c.axioms, Denotes opInterp fvarVal e true)
    (hfnax : ∀ e ∈ c.fnAxioms, Denotes opInterp fvarVal e true)
    (hdist : ∀ es ∈ c.distincts, DistinctHolds opInterp fvarVal es)
    (Q : OblProgram) (bpfx : List OblCommand) (b : Expression.Expr)
    (hQcmds : Q.cmds = obligationPrefix c fns ++ bpfx)
    (hQob : Q.obligation = b)
    (hpsat : PrefixSat opInterp fvarVal bpfx)
    (hbpfx_nodist : ∀ es, OblCommand.distinct es ∉ bpfx)
    (hbpfx_nofndef : ∀ d, OblCommand.fnDef d ∉ bpfx)
    (hwfQ : OblProgramWF Q) (hVQ : OblProgram.Valid Q hwfQ) :
    Denotes opInterp fvarVal Q.obligation true := by
  -- (1) connectors 1a/1b — op-consistency of the model with the emitted defs/builtins. The
  --     SMT-LIB-faithful div-by-zero model supplies `divByZero`/`modByZero` (the model's own at-zero
  --     values); `OblProgram.Valid` quantifies over them, so they are inferred at `hVQ` from `hOpCon`.
  obtain ⟨divByZero, modByZero, hOpCon⟩ :
      ∃ divByZero modByZero, OpInterpConsistent divByZero modByZero opInterp :=
    opInterpConsistent_of_factoryConsistent hbc hseed hFC
  have hFnDefs : FnDefs.OpConsistent opInterp fvarVal Q.defs
      (fun d hd => ((hwfQ.defsWF) d hd).hasTypeA) :=
    fnDefsOpConsistent_of_factoryConsistent hffwf hFC hQcmds hbpfx_nofndef _
  -- (2) `VarDefs.Consistent`: every `.varDef ∈ Q.cmds` is a `bpfx` varDef (obligationPrefix has none),
  --     pinned by `hpsat.2`.
  have hVarDefs : VarDefs.Consistent opInterp fvarVal Q.varDefs
      (fun v hv => (hwfQ.varDefsWF v hv).hasTypeA) := by
    intro v hv
    -- `v ∈ Q.varDefs`; via the fold, `.varDef v ∈ Q.cmds = obligationPrefix ++ bpfx`
    have hvcmd : OblCommand.varDef v ∈ Q.cmds := by
      have := (mem_foldl_varDefs (cmds := Q.cmds) (c := {}) (v := v)).mp hv
      simpa using this
    rw [hQcmds] at hvcmd
    rcases List.mem_append.mp hvcmd with h | h
    · exact absurd h (obligationPrefix_no_varDef c fns v)
    · -- from `bpfx`: `hpsat.2` gives the pin, up to the WF `HasTypeA` witness (proof-irrel)
      obtain ⟨hty, hpin⟩ := hpsat.2 v h
      have hwty : LExpr.HasTypeA [] v.body v.ty := (hwfQ.varDefsWF v hv).hasTypeA
      -- `VarDef.Consistent` is functional in the `HasTypeA` witness (proof_irrel)
      rw [VarDef.Consistent] at hpin ⊢
      rw [proof_irrel hty hwty] at hpin
      exact hpin
  -- (3) `LambdaModelSatisfiesAsms`: every `.assume e ∈ Q.cmds` denotes true.
  have hAsms : LambdaModelSatisfiesAsms Q hwfQ opInterp fvarVal := by
    intro e he
    -- `e ∈ Q.assumptions` ⇒ `.assume e ∈ Q.cmds = obligationPrefix ++ bpfx`
    have hecmd : OblCommand.assume e ∈ Q.cmds := by
      have := (mem_foldl_assumptions (cmds := Q.cmds) (c := {}) (e := e)).mp he
      simpa using this
    -- `e` denotes true (global axiom / emitted fn-axiom / bpfx assume), converted to the WF witness
    apply Denotes.simpDenote_eq
    rw [hQcmds] at hecmd
    rcases List.mem_append.mp hecmd with h | h
    · exact obligationPrefix_assume_denotes c fns opInterp fvarVal hseed hax hfnax e h
    · exact hpsat.1 e h
  -- (4) `LambdaModelSatisfiesDistincts`: every `.distinct ∈ Q.cmds` is a global distinct (`hdist`).
  have hDists : LambdaModelSatisfiesDistincts Q hwfQ opInterp fvarVal :=
    distincts_sat_of_global c fns opInterp fvarVal hdist Q bpfx hQcmds hbpfx_nodist hwfQ
  -- assemble: `OblProgram.Valid Q` forces `⟦Q.obligation⟧ = true`, i.e. `Denotes Q.obligation true`
  exact ⟨HasSimpType_implies_HasTypeA hwfQ.obligationWF,
    hVQ divByZero modByZero opInterp hOpCon fvarVal hFnDefs hVarDefs hAsms hDists⟩

/-- **Per-procedure validity from its emitted obligations.** If every `OblProgram` emitted for a
    procedure body `ss` at prefix `c` is `OblProgram.Valid`, then no reachable configuration of `ss`
    fails (`ProcValid c ss`).

    Uses `PStepStar.first_failure` to name the violated obligation: a run to a failed config passes
    through a first `assertFail` on some `assert b`, whose run prefix is a `bodyObligations` path,
    giving an emitted `Q = ⟨obligationPrefix c fns ++ bpfx, b⟩`. `OblProgram.Valid Q` (discharging
    its consistency/assumption/distinct hypotheses from the factory-consistent model — connectors
    1a/1b, the pin⟺varDef equivalence, and the fired assume/pass steps) forces `Denotes b true`,
    contradicting the `assertFail`'s `Denotes b false`. The model-transfer discharge is the deferred
    content. -/
theorem procValid_of_obligationsValid {c : CoreCtx} {ss : Statements}
    (hpre : Statements.Preprocessed c.Ψ [] ss)
    (hbc : CoreCtx.SeedBuiltinConsistent)
    (hffwf : c.FactoryFuncsWF)
    (hseed : c.SeedWF)
    (hWF : ∀ Q ∈ procObligations c ss, OblProgramWF Q)
    (hV : ∀ Q ∈ procObligations c ss, ∀ (hwfQ : OblProgramWF Q), OblProgram.Valid Q hwfQ) :
    ProcValid c ss := by
  intro opInterp fvarVal hFC hax hfnax hdist cfg hrun
  -- Suppose the run reached a failed config; derive a contradiction via first-failure extraction.
  match hcf : cfg.failed with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨d, d', hd_run, hstep, hdf, hd'f⟩ := hrun.first_failure rfl hcf
      obtain ⟨l, b, md, rest, hwork, hd_eq, _hd'_eq, hb_false⟩ :=
        hstep.assertFail_of_flip hdf hd'f
      -- Half A (proven): the run prefix traces a `bodyObligations` path to `assert b`, giving an
      -- emitted `Q = ⟨obligationPrefix c fns ++ bpfx, b⟩ ∈ procObligations c ss` whose `bpfx` the
      -- model satisfies (`PrefixSat`: its assumes fired true, its varDefs pinned).
      have hd_run' : PStepStar opInterp fvarVal ⟨ss, false⟩
          ⟨Statement.assert l b md :: rest, false⟩ := by
        have : d = ⟨Statement.assert l b md :: rest, false⟩ := by rw [hd_eq, hwork]
        rwa [this] at hd_run
      obtain ⟨bpfx, hbomem, hpsat⟩ := run_corresponds_bodyObligations hpre [] ⟨by simp, by simp⟩ hd_run'
      -- the emitted `Q` for this `(bpfx, b)` pair (the `procObligations` map image), with its
      -- concrete command list `obligationPrefix c fns ++ bpfx` exposed for the discharge.
      obtain ⟨Q, hQmem, fns, hQcmds, hQob⟩ :
          ∃ Q ∈ procObligations c ss, ∃ fns,
            Q.cmds = obligationPrefix c fns ++ bpfx ∧ Q.obligation = b := by
        refine ⟨_, List.mem_map.mpr ⟨(bpfx, b), hbomem, rfl⟩, _, rfl, rfl⟩
      have hwfQ : OblProgramWF Q := hWF Q hQmem
      -- Half B: `OblProgram.Valid Q` at this model forces `Q.obligation` (`= b`) to denote `true`;
      -- discharge its hypotheses from the factory-consistent model + `PrefixSat`, then contradict.
      have hbpfx_nodist : ∀ es, OblCommand.distinct es ∉ bpfx :=
        bodyObligations_no_distinct hpre [] (by simp) bpfx b hbomem
      have hbpfx_nofndef : ∀ d, OblCommand.fnDef d ∉ bpfx :=
        bodyObligations_no_fnDef hpre [] (by simp) bpfx b hbomem
      have hbtrue : Denotes opInterp fvarVal Q.obligation true :=
        obligationValid_denotes c ss fns opInterp fvarVal hbc hffwf hseed hFC hax hfnax hdist
          Q bpfx b hQcmds hQob hpsat hbpfx_nodist hbpfx_nofndef hwfQ (hV Q hQmem hwfQ)
      rw [hQob] at hbtrue
      exact absurd (Denotes.functional hbtrue hb_false) (by simp)

/-- **Layer-1 soundness.** If every emitted obligation program is `OblProgram.Valid`, the
    preprocessed program is `Program.Valid`. Contrapositive of a model transfer.

    Plan. Per procedure, unfold `ProcValid`; fix a factory-consistent model refuting it (satisfying
    prefix axioms/distincts but driving the body to a reachable `failed`). By `failed_mono` +
    first-failure extraction, at the first failing `assert b` on that path `Denotes … b false`, and
    the run prefix corresponds to a root-to-assert path in `bodyObligations`, giving an emitted
    `Q = ⟨obligationPrefix c fns ++ bpfx, b⟩ ∈ toOblPrograms p`. Discharge `OblProgram.Valid Q`'s
    hypotheses at the model:
      • `OpInterpConsistent` ← `Factory.InterpConsistent c.F`'s `InterpConsistentEval` (1b);
      • `FnDefs.OpConsistent` (emitted fnDefs) ← its `InterpConsistentBody` clause + fvar→bvar lift
        `substFvarsLifting_denote` (1a);
      • `VarDefs.Consistent` (emitted varDefs) ← each `initDetLive` step's `hpin` (pin ⟺ varDef);
      • assumptions ← prefix axioms/fn-axioms (given) + path assumes/passed-asserts (their
        `assumeLive`/`assertPass` steps fired ⇒ `Denotes … true`);
      • distincts ← prefix distincts (given).
    `OblProgram.Valid Q` then forces `Denotes … b true`; `Denotes` functional (`proof_irrel`) ⇒
    contradiction with `Denotes … b false`. Hence no reachable config fails.

    This top-level statement reduces (via `procValid_of_obligationsValid` +
    `PStepStar.first_failure`) to the per-obligation model transfer; the fold bookkeeping
    (`ValidFrom` over `decls`) is discharged here, the model transfer remains deferred. -/
theorem program_valid_of_oblProgramsValid {p : Program} (hwf : Program.WF p)
    (hbc : CoreCtx.SeedBuiltinConsistent)
    (hseedFF : CoreCtx.SeedFactoryFuncsWF)
    (hValid : ∀ Q (hQ : Q ∈ toOblPrograms p), OblProgram.Valid Q (toOblPrograms_wf hwf hseedFF Q hQ)) :
    Program.Valid p := by
  -- `Program.Valid p = ValidFrom p.decls init`. Generalize over the fold: prove `ValidFrom decls c`
  -- for any `c`, provided every `Q` emitted from `c`-onward is `OblProgram.Valid`.
  unfold Program.Valid
  suffices h : ∀ (decls : List Decl) (c : CoreCtx), Program.WFfrom decls c → c.Good →
      c.FactoryFuncsWF → c.SeedWF →
      (∀ Q ∈ toOblProgramsFrom decls c, ∀ (hwfQ : OblProgramWF Q), OblProgram.Valid Q hwfQ) →
      Program.ValidFrom decls c by
    apply h p.decls CoreCtx.init hwf CoreCtx.init_Good hseedFF CoreCtx.init_SeedWF
    intro Q hQmem _hwfQ
    -- `toOblPrograms p = toOblProgramsFrom p.decls init`; the `OblProgramWF` arg is proof-irrelevant.
    exact hValid Q hQmem
  intro decls
  induction decls with
  | nil => intro c _ _ _ _ _; trivial
  | cons d rest ih =>
    intro c hwfrom hgood hffwf hseed hobl
    obtain ⟨hdWF, hrestWF⟩ := hwfrom
    refine ⟨?_, ?_⟩
    · -- the head conjunct: `ProcValid` if `d` is a structured proc, else trivial
      cases d with
      | proc p' md =>
        cases hb : p'.body with
        | structured ss =>
            simp only [hb]
            -- `hpre` from the proc's `declWF`; `hWF Q` from `toOblProgramsFrom_declWF` reused per-Q
            have hpre : Statements.Preprocessed c.Ψ [] ss := by
              rw [CoreCtx.declWF, hb] at hdWF
              obtain ⟨ss', hss'eq, hpre', _⟩ := hdWF
              cases hss'eq; exact hpre'
            refine procValid_of_obligationsValid hpre hbc hffwf hseed (fun Q hQ => ?_) (fun Q hQ hwfQ => ?_)
            · -- `OblProgramWF Q`: `Q ∈ procObligations c ss ⊆ toOblPrograms`; reuse `toOblPrograms_wf`
              have hmem : Q ∈ toOblProgramsFrom (Decl.proc p' md :: rest) c := by
                rw [toOblProgramsFrom]; simp only [hb, List.mem_append]; exact Or.inl hQ
              exact toOblProgramsFrom_WF c (Decl.proc p' md :: rest) ⟨hdWF, hrestWF⟩ hgood hffwf
                hseed Q hmem
            · apply hobl Q _ hwfQ
              rw [toOblProgramsFrom]
              simp only [hb, List.mem_append]
              exact Or.inl hQ
        | cfg _ => simp only [hb]
      | func _ _ => trivial
      | type _ _ => trivial
      | ax _ _ => trivial
      | distinct _ _ _ => trivial
      | recFuncBlock _ _ => trivial
    · -- the tail: apply the IH at the stepped context; obligations from the tail are a suffix of
      -- `toOblProgramsFrom (d :: rest) c = here ++ toOblProgramsFrom rest (c.step d)`.
      apply ih (c.step d) hrestWF (hgood.step hdWF) (hffwf.step hdWF) (hseed.step d)
      intro Q hQ hwfQ
      apply hobl Q _ hwfQ
      cases d with
      | proc p' md =>
          cases hb : p'.body with
          | structured ss =>
              simp only [toOblProgramsFrom, hb, List.mem_append]; exact Or.inr hQ
          | cfg _ =>
              simp only [toOblProgramsFrom, hb, List.nil_append]; exact hQ
      | func _ _ => simp only [toOblProgramsFrom, List.nil_append]; exact hQ
      | type _ _ => simp only [toOblProgramsFrom, List.nil_append]; exact hQ
      | ax _ _ => simp only [toOblProgramsFrom, List.nil_append]; exact hQ
      | distinct _ _ _ => simp only [toOblProgramsFrom, List.nil_append]; exact hQ
      | recFuncBlock _ _ => simp only [toOblProgramsFrom, List.nil_append]; exact hQ

end Core.Preprocessed
