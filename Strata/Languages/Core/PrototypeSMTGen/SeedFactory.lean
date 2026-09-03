/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public meta import Lean.Elab.Command
import all Strata.Languages.Core.PrototypeSMTGen.Core
import all Strata.Languages.Core.PrototypeSMTGen.BuiltinConsistent

/-!
# Seed-factory well-formedness for the default `Core.Factory`

Discharges the `CoreCtx.SeedFactoryFuncsWF` (= `CoreCtx.init.FactoryFuncsWF`) and
`CoreCtx.SeedBuiltinConsistent` premises of the Layer-1 theorems for the concrete default
`Core.Factory`. Each per-function requirement holds for the factory:
  • name non-reserved: `f.name.name ≠ "$__bv{n}"` for all `n`;
  • `f.inputs.keys.Nodup`;
  • bodied ⟹ non-recursive;
  • the non-recursive body typing, vacuously (every `Core.Factory` function has `body = none`).

These facts are established by `native_decide` over the concrete factory array. Two `native_decide`
limitations (both stemming from the missing compiled `DecidableEq (LExpr CoreLParams.mono)` /
`CoreIdent`×`LMonoTy` IR) are routed around:
  • `keys.Nodup` (keys are `CoreIdent`) is decided as `(keys.map (·.name)).Nodup` (a `List String`,
    IR available) and lifted back via `nodup_of_map`;
  • the reserved-name conjunct is decided per-name via `name.toList.head? ≠ some '$'` (a `List Char`
    fact), since `s!"$__bv{n}"` always begins with `'$'`.

Key results: `init_FactoryFuncsWF`, `init_SeedBuiltinConsistent`, `toOblPrograms_wf'`,
`program_valid_of_oblProgramsValid'`.
-/

open Core Lambda Imperative Std Core.Construct Core.ModelTransfer Core.Preprocessed

namespace Core.SeedFactory

/-- `Nodup` transfers back along a `map` (if the mapped list is `Nodup`, so is the original). -/
theorem nodup_of_map {α β} (g : α → β) (l : List α) (h : (l.map g).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun hm => h.1 (List.mem_map_of_mem hm), ih h.2⟩

/-- `s!"$__bv{n}"` begins with `'$'` (its `toList` head is `'$'`). -/
theorem bv_toList_head (n : Nat) : (s!"$__bv{n}").toList.head? = some '$' := by
  show (("$__bv" ++ toString n)).toList.head? = some '$'
  rw [String.toList_append]; rfl

/-- A name whose `toList` head is not `'$'` is not a reserved `$__bv{n}` name. -/
theorem ne_bv_of_head {name : String} (h : name.toList.head? ≠ some '$') (n : Nat) :
    name ≠ s!"$__bv{n}" := by
  intro heq; exact h (heq ▸ bv_toList_head n)

/-! ## The `native_decide`-decidable factory facts (routed around the IR gaps) -/

meta section

/-- Every `Core.Factory` function is bodyless. -/
theorem all_bodyless : ∀ f ∈ Core.Factory.toArray, f.body = none := by native_decide

/-- Every `Core.Factory` function's input-key NAMES are `Nodup` (a `List String` fact). -/
theorem all_keys_name_nodup : ∀ f ∈ Core.Factory.toArray,
    (f.inputs.keys.map (·.name)).Nodup := by native_decide

/-- No `Core.Factory` function name begins with `'$'`. -/
theorem all_head_ne : ∀ f ∈ Core.Factory.toArray,
    f.name.name.toList.head? ≠ some '$' := by native_decide

end -- meta section

/-- **The seed factory `Core.Factory` is function-well-formed** (`init.FactoryFuncsWF`). Discharges the
    `SeedFactoryFuncsWF` premise of the top-level Layer-1 theorems. Each conjunct holds for the concrete
    factory: names are non-reserved and key-nodup (`native_decide`), all functions are bodyless (so the
    bodied⟹non-recursive and body-typing clauses are vacuous). -/
theorem init_FactoryFuncsWF : CoreCtx.SeedFactoryFuncsWF := by
  intro pre f suf hsplit
  -- `f ∈ Core.Factory.toArray` from the split of its toList (`init.F = Core.Factory`)
  have hfmem : f ∈ Core.Factory.toArray := by
    have hmemList : f ∈ (Core.Factory.toArray).toList := by
      rw [show (Core.Factory.toArray).toList = pre ++ f :: suf from hsplit]
      exact List.mem_append_right pre (List.mem_cons_self)
    exact Array.mem_def.mpr hmemList
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- non-reserved name
    exact ne_bv_of_head (all_head_ne f hfmem)
  · -- keys nodup, via the name-projected nodup
    exact nodup_of_map (·.name) f.inputs.keys (all_keys_name_nodup f hfmem)
  · -- bodied ⟹ non-recursive: vacuous, `f.body = none`
    intro body hbody; rw [all_bodyless f hfmem] at hbody; exact absurd hbody (by simp)
  · -- body typing: vacuous, `f.body = none`
    intro _ body hbody; rw [all_bodyless f hfmem] at hbody; exact absurd hbody (by simp)

/-- **The seed builtin-consistency premise holds for the default `Core.Factory`** (`SeedBuiltinConsistent`).
    Discharges the `SeedBuiltinConsistent` premise of the top-level Layer-1 theorems by delegating to
    `BuiltinConsistent.opInterpConsistent_of_coreFactory`, including the guarded div/mod ops via the
    SMT-LIB-faithful model-chosen div-by-zero values it supplies. -/
theorem init_SeedBuiltinConsistent : CoreCtx.SeedBuiltinConsistent :=
  fun hIC => ⟨_, _, Core.BuiltinConsistent.opInterpConsistent_of_coreFactory hIC⟩

/-! ## Premise-free entry points for the default `Core.Factory`

The general Layer-1 theorems are parameterized over any seed-well-formed factory (`hseedFF`) and the
seed builtin-consistency fact (`hbc`). These wrappers discharge those premises for the concrete
default factory, giving callers a hypothesis-free interface.
-/

/-- **Emitted obligations are well-formed** (default `Core.Factory`, premise discharged). The
    `init_FactoryFuncsWF`-specialized `toOblPrograms_wf`. -/
theorem toOblPrograms_wf' {p : Program} (hwf : Program.WF p) :
    ∀ Q ∈ toOblPrograms p, OblProgramWF Q :=
  toOblPrograms_wf hwf init_FactoryFuncsWF

/-- **Program validity from obligation validity** (default `Core.Factory`, premise discharged). The
    `init_FactoryFuncsWF`-specialized `program_valid_of_oblProgramsValid`. -/
theorem program_valid_of_oblProgramsValid' {p : Program} (hwf : Program.WF p)
    (hValid : ∀ Q (hQ : Q ∈ toOblPrograms p),
      OblProgram.Valid Q (toOblPrograms_wf hwf init_FactoryFuncsWF Q hQ)) :
    Program.Valid p :=
  program_valid_of_oblProgramsValid hwf init_SeedBuiltinConsistent init_FactoryFuncsWF hValid

end Core.SeedFactory
