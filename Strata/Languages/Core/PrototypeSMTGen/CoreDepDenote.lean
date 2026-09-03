/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
import all Strata.Languages.Core.PrototypeSMTGen.Core

/-!
# Dependently-typed operational semantics for Core Layer 1

A reformulation of `Core`'s small-step semantics in the shape of the production `EvalCmd`/`Config`
split, designed to make typing-stuckness structurally impossible: a step cannot be formed from an
ill-typed command, so ill-typedness is excluded from the domain.

`CmdPreprocessed` is a context-transformer typing judgment for a single leaf command, and
`Preprocessed` is the whole-body well-formedness built from it. `PStep` is the per-command step
relation (the `EvalCmd` analog): it takes the command's well-formedness witness whole and projects
the typing it needs. `PStepStar` is the traversal relation (sequencing and branching, the
`Config`-level analog): it carries the statement list and its whole-list `Preprocessed` witness as a
threaded index, so well-formedness flows forward one step at a time. Validity (`ProcValid`,
`Program.ValidFrom`, `Program.Valid`) is stated in a `Denotes`-free, witness-carrying form, and
Layer-1 soundness is proven against the emitted obligations.

This file is standalone; build it directly with
`lake build Strata.Languages.Core.PrototypeSMTGen.CoreDepDenote`.

Key definitions: `CmdPreprocessed`, `Preprocessed`, `PStep`, `PStepStar`, `ProcValid`,
`Program.Valid`. Key results: `PStepStar.failed_mono`, `failing_run_corresponds`,
`obligationValidW_denotes`, `procValid_of_obligationsValid`, `program_valid_of_oblProgramsValid`.
-/

open Core Lambda Imperative Std Core.Construct Core.ModelTransfer

namespace Core.Preprocessed.Dep

/-! ## `CmdPreprocessed`: single-command well-formedness

`CmdPreprocessed Ψ Φ cmd Φ'`: the leaf command `cmd` is well-formed in context `Φ` and yields output
context `Φ'`. This is a context-transformer typing judgment: the output context is an index, so the
`init` monotype `mτ` is data carried in `Φ' = Φ ++ [(name, mτ)]`, threading by unification. It is
`PStep`'s typing index and the base for the local `Preprocessed` below. The four constructors are
the leaf commands; branching (`.ite`) lives on the traversal, and `cover` is a no-op with no rule.
-/
inductive CmdPreprocessed (Ψ : FnCtx) : (Φ : FVarCtx) → Statement → (Φ' : FVarCtx) → Prop where
  | assume (Φ : FVarCtx) (l : String) (b : Expression.Expr) (md : MetaData Expression)
           (hb : LExpr.HasSimpType Φ Ψ [] b (.tcons "bool" [])) :
      CmdPreprocessed Ψ Φ (Statement.assume l b md) Φ
  | assert (Φ : FVarCtx) (l : String) (b : Expression.Expr) (md : MetaData Expression)
           (hb : LExpr.HasSimpType Φ Ψ [] b (.tcons "bool" [])) :
      CmdPreprocessed Ψ Φ (Statement.assert l b md) Φ
  | initDet (Φ : FVarCtx) (name : Expression.Ident) (ty : Expression.Ty) (mτ : LMonoTy)
            (e : Expression.Expr) (md : MetaData Expression)
            (hmono : ty.toMonoType? = some mτ) (he : LExpr.HasSimpType Φ Ψ [] e mτ)
            (hfreshΦ : name.name ∉ Φ.map (·.1)) (hfreshΨ : name.name ∉ Ψ.map (·.1))
            (hnres : ∀ n : Nat, name.name ≠ s!"$__bv{n}") :
      CmdPreprocessed Ψ Φ (Statement.init name ty (.det e) md) (Φ ++ [(name.name, mτ)])
  | initNondet (Φ : FVarCtx) (name : Expression.Ident) (ty : Expression.Ty) (mτ : LMonoTy)
               (md : MetaData Expression) (hmono : ty.toMonoType? = some mτ)
               (hsimp : LExpr.MonoTyIsSimp mτ)
               (hfreshΦ : name.name ∉ Φ.map (·.1)) (hfreshΨ : name.name ∉ Ψ.map (·.1))
               (hnres : ∀ n : Nat, name.name ≠ s!"$__bv{n}") :
      CmdPreprocessed Ψ Φ (Statement.init name ty .nondet md) (Φ ++ [(name.name, mτ)])

/-- **Body typing of a WF `assume`.** Projects the bool-typing of `b` from `CmdPreprocessed`. -/
theorem CmdPreprocessed.assume_hb {Ψ Φ Φ'} {l b md}
    (wfc : CmdPreprocessed Ψ Φ (Statement.assume l b md) Φ') :
    LExpr.HasSimpType Φ Ψ [] b (.tcons "bool" []) := by
  cases wfc with | assume _ _ _ hb => exact hb

/-- **Body typing of a WF `assert`.** -/
theorem CmdPreprocessed.assert_hb {Ψ Φ Φ'} {l b md}
    (wfc : CmdPreprocessed Ψ Φ (Statement.assert l b md) Φ') :
    LExpr.HasSimpType Φ Ψ [] b (.tcons "bool" []) := by
  cases wfc with | assert _ _ _ hb => exact hb

/-- **Inversion of a WF `.det` `init`** — recovers `mτ` (matching the output index `Φ'`), the body
    typing, and the freshness side-conditions. -/
theorem CmdPreprocessed.initDet_inv {Ψ Φ Φ'} {name ty e md}
    (wfc : CmdPreprocessed Ψ Φ (Statement.init name ty (.det e) md) Φ') :
    ∃ mτ, Φ' = Φ ++ [(name.name, mτ)] ∧ ty.toMonoType? = some mτ ∧ LExpr.HasSimpType Φ Ψ [] e mτ ∧
      name.name ∉ Φ.map (·.1) ∧ name.name ∉ Ψ.map (·.1) ∧
      (∀ n : Nat, name.name ≠ s!"$__bv{n}") := by
  cases wfc with
  | initDet _ _ mτ _ _ hmono he hfreshΦ hfreshΨ hnres =>
      exact ⟨mτ, rfl, hmono, he, hfreshΦ, hfreshΨ, hnres⟩

/-- **Inversion of a WF `.nondet` `init`** (havoc). -/
theorem CmdPreprocessed.initNondet_inv {Ψ Φ Φ'} {name ty md}
    (wfc : CmdPreprocessed Ψ Φ (Statement.init name ty .nondet md) Φ') :
    ∃ mτ, Φ' = Φ ++ [(name.name, mτ)] ∧ ty.toMonoType? = some mτ ∧ LExpr.MonoTyIsSimp mτ ∧
      name.name ∉ Φ.map (·.1) ∧ name.name ∉ Ψ.map (·.1) ∧
      (∀ n : Nat, name.name ≠ s!"$__bv{n}") := by
  cases wfc with
  | initNondet _ _ mτ _ hmono hsimp hfreshΦ hfreshΨ hnres =>
      exact ⟨mτ, rfl, hmono, hsimp, hfreshΦ, hfreshΨ, hnres⟩

/-- **Body typing of a WF `.det` `init`, at the output-index monotype `mτ`.** Projects `e`'s typing
    directly from `wf`, with `mτ` pinned by `wf`'s output index `Φ ++ [(name, mτ)]`. The `.det`
    analog of `assume_hb`/`assert_hb`. -/
theorem CmdPreprocessed.initDet_he {Ψ Φ mτ} {name ty e md}
    (wf : CmdPreprocessed Ψ Φ (Statement.init name ty (.det e) md) (Φ ++ [(name.name, mτ)])) :
    LExpr.HasSimpType Φ Ψ [] e mτ := by
  obtain ⟨mτ', hΦ', _, he, _⟩ := wf.initDet_inv
  have hmτ : mτ' = mτ := by
    simp only [List.append_right_inj, List.cons.injEq, Prod.mk.injEq] at hΦ'; exact hΦ'.1.2.symm
  subst hmτ; exact he

/-! ## `Preprocessed`: whole-body well-formedness

Whole-body well-formedness built from `CmdPreprocessed`. A leaf command's clause is just
`CmdPreprocessed` (the single-command judgment), whose output-context index threads the tail's
context by unification; `.ite` (nondet branching) and `nil` are the two structural clauses.
Factoring every leaf through `CmdPreprocessed` lets the traversal (`PStepStar`) and the whole-body
well-formedness share one command judgment.

The `consPreprocessed` lemma below is the intro rule threading a command well-formedness into a
whole-body one.
-/
inductive Preprocessed (Ψ : FnCtx) : (Φ : FVarCtx) → Statements → Prop where
  /-- Empty body. -/
  | nil (Φ : FVarCtx) : Preprocessed Ψ Φ []
  /-- A leaf command (`assume`/`assert`/`init`) via `CmdPreprocessed`, then the tail at the command's
      OUTPUT context `Φ'` (threaded by the index — grown for `init`, unchanged otherwise). -/
  | cons (Φ Φ' : FVarCtx) (cmd : Statement) (rest : Statements)
         (wfc : CmdPreprocessed Ψ Φ cmd Φ')
         (hrest : Preprocessed Ψ Φ' rest) :
      Preprocessed Ψ Φ (cmd :: rest)
  /-- Nondeterministic branching: both branches and the continuation are preprocessed at the CURRENT
      `Φ` (branch declarations do not leak into `rest`), matching the terminal-`ite` semantics. -/
  | ite (Φ : FVarCtx) (thenb elseb : Statements) (md : MetaData Expression) (rest : Statements)
        (hthen : Preprocessed Ψ Φ thenb) (helse : Preprocessed Ψ Φ elseb)
        (hrest : Preprocessed Ψ Φ rest) :
      Preprocessed Ψ Φ (Stmt.ite .nondet thenb elseb md :: rest)

/-- **Inversion for a leading `.ite`** over `Preprocessed` — the branch and continuation witnesses. -/
theorem preprocessed_ite_inv {Ψ Φ} {thenb elseb md rest}
    (h : Preprocessed Ψ Φ (Stmt.ite .nondet thenb elseb md :: rest)) :
    Preprocessed Ψ Φ thenb ∧ Preprocessed Ψ Φ elseb ∧ Preprocessed Ψ Φ rest := by
  cases h with
  | cons Φ Φ' cmd rest wfc hrest => nomatch wfc   -- an `.ite` head is not a `CmdPreprocessed` command
  | ite Φ thenb elseb md rest hthen helse hrest => exact ⟨hthen, helse, hrest⟩

/-! ## Emitter lemmas over `Preprocessed`

Proven over this file's `Preprocessed` by induction (`nil`/`cons`/`ite`); the `cons` case does
`cases wfc` on the command well-formedness to recover the four leaf shapes.
`bodyObligations`/`initDecl`/`cmdBodyRefs`/`stmtsFnRefs` are predicate-agnostic.
-/

/-- `bodyObligations` prefixes contain no `.distinct`. -/
theorem bodyObligations_no_distinct {Ψ Φ ss} (hpre : Preprocessed Ψ Φ ss) :
    ∀ (pfx : List OblCommand), (∀ es, OblCommand.distinct es ∉ pfx) →
      ∀ bpfx ob, (bpfx, ob) ∈ bodyObligations pfx ss →
      ∀ es, OblCommand.distinct es ∉ bpfx := by
  induction hpre with
  | nil Φ => intro pfx _ bpfx ob hmem; simp [bodyObligations] at hmem
  | cons Φ Φ' cmd rest wfc hrest ih =>
      intro pfx hpfx bpfx ob hmem
      cases wfc with
      | assume l b md hb =>
          rw [bodyObligations] at hmem
          refine ih (pfx ++ [OblCommand.assume b]) (fun es hc => ?_) bpfx ob hmem
          rcases List.mem_append.mp hc with h | h
          · exact hpfx es h
          · rw [List.mem_singleton] at h; exact OblCommand.noConfusion h
      | assert l b md hb =>
          rw [bodyObligations] at hmem
          rcases List.mem_cons.mp hmem with heq | htl
          · rw [Prod.mk.injEq] at heq; rw [heq.1]; exact hpfx
          · exact ih pfx hpfx bpfx ob htl
      | initDet name ty mτ e md hmono he hfreshΦ hfreshΨ hnres =>
          rw [bodyObligations] at hmem; simp only [initDecl, hmono] at hmem
          refine ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]) (fun es hc => ?_) bpfx ob hmem
          rcases List.mem_append.mp hc with h | h
          · exact hpfx es h
          · rw [List.mem_singleton] at h; exact OblCommand.noConfusion h
      | initNondet name ty mτ md hmono hsimp hfreshΦ hfreshΨ hnres =>
          rw [bodyObligations] at hmem; simp only [initDecl, hmono] at hmem
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

/-- `bodyObligations` prefixes contain no `.fnDef`. -/
theorem bodyObligations_no_fnDef {Ψ Φ ss} (hpre : Preprocessed Ψ Φ ss) :
    ∀ (pfx : List OblCommand), (∀ d, OblCommand.fnDef d ∉ pfx) →
      ∀ bpfx ob, (bpfx, ob) ∈ bodyObligations pfx ss →
      ∀ d, OblCommand.fnDef d ∉ bpfx := by
  induction hpre with
  | nil Φ => intro pfx _ bpfx ob hmem; simp [bodyObligations] at hmem
  | cons Φ Φ' cmd rest wfc hrest ih =>
      intro pfx hpfx bpfx ob hmem
      cases wfc with
      | assume l b md hb =>
          rw [bodyObligations] at hmem
          refine ih (pfx ++ [OblCommand.assume b]) (fun d hc => ?_) bpfx ob hmem
          rcases List.mem_append.mp hc with h | h
          · exact hpfx d h
          · rw [List.mem_singleton] at h; exact OblCommand.noConfusion h
      | assert l b md hb =>
          rw [bodyObligations] at hmem
          rcases List.mem_cons.mp hmem with heq | htl
          · rw [Prod.mk.injEq] at heq; rw [heq.1]; exact hpfx
          · exact ih pfx hpfx bpfx ob htl
      | initDet name ty mτ e md hmono he hfreshΦ hfreshΨ hnres =>
          rw [bodyObligations] at hmem; simp only [initDecl, hmono] at hmem
          refine ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ, e⟩]) (fun d hc => ?_) bpfx ob hmem
          rcases List.mem_append.mp hc with h | h
          · exact hpfx d h
          · rw [List.mem_singleton] at h; exact OblCommand.noConfusion h
      | initNondet name ty mτ md hmono hsimp hfreshΦ hfreshΨ hnres =>
          rw [bodyObligations] at hmem; simp only [initDecl, hmono] at hmem
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

/-- Every emitted obligation's seeds are ⊆ the body's refs. -/
theorem bodyObligations_seeds_subset {Ψ Φ ss} (hpre : Preprocessed Ψ Φ ss) :
    ∀ (pfx : List OblCommand) bpfx ob, (bpfx, ob) ∈ bodyObligations pfx ss →
      (∀ n ∈ exprFnRefs ob, n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs ss) ∧
      (∀ n ∈ bpfx.flatMap cmdBodyRefs, n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs ss) := by
  induction hpre with
  | nil Φ => intro pfx bpfx ob hmem; simp [bodyObligations] at hmem
  | cons Φ Φ' cmd rest wfc hrest ih =>
      intro pfx bpfx ob hmem
      cases wfc with
      | assume l b md hb =>
          rw [bodyObligations] at hmem
          obtain ⟨ihob, ihpfx⟩ := ih (pfx ++ [OblCommand.assume b]) bpfx ob hmem
          have hss : stmtsFnRefs (Statement.assume l b md :: rest) = exprFnRefs b ++ stmtsFnRefs rest := by
            simp only [stmtsFnRefs]
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
      | assert l b md hb =>
          rw [bodyObligations] at hmem
          have hss : stmtsFnRefs (Statement.assert l b md :: rest) = exprFnRefs b ++ stmtsFnRefs rest := by
            simp only [stmtsFnRefs]
          rcases List.mem_cons.mp hmem with heq | htl
          · rw [Prod.mk.injEq] at heq
            obtain ⟨hbpfx, hob⟩ := heq; subst hbpfx; subst hob
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
      | initDet name ty mτ e md hmono he hfreshΦ hfreshΨ hnres =>
          rw [bodyObligations] at hmem; simp only [initDecl, hmono] at hmem
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
      | initNondet name ty mτ md hmono hsimp hfreshΦ hfreshΨ hnres =>
          rw [bodyObligations] at hmem; simp only [initDecl, hmono] at hmem
          obtain ⟨ihob, ihpfx⟩ := ih (pfx ++ [OblCommand.fvarDecl name.name mτ]) bpfx ob hmem
          have hss : stmtsFnRefs (Statement.init name ty .nondet md :: rest) = stmtsFnRefs rest := by
            simp only [stmtsFnRefs]
          have reloc : ∀ n, n ∈ (pfx ++ [OblCommand.fvarDecl name.name mτ]).flatMap cmdBodyRefs
                ++ stmtsFnRefs rest →
              n ∈ pfx.flatMap cmdBodyRefs ++ stmtsFnRefs (Statement.init name ty .nondet md :: rest) := by
            intro n hn; rw [hss, List.flatMap_append] at *
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, cmdBodyRefs] at hn
            rcases List.mem_append.mp hn with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ h
          exact ⟨fun n hn => reloc n (ihob n hn), fun n hn => reloc n (ihpfx n hn)⟩
  | ite Φ thenb elseb md rest hthen helse hrest ihthen ihelse ihrest =>
      intro pfx bpfx ob hmem
      rw [bodyObligations] at hmem
      have hss : stmtsFnRefs (Stmt.ite .nondet thenb elseb md :: rest)
          = (stmtsFnRefs thenb ++ stmtsFnRefs elseb) ++ stmtsFnRefs rest := by simp only [stmtsFnRefs]
      rcases List.mem_append.mp hmem with h | hr
      · rcases List.mem_append.mp h with ht | he'
        · obtain ⟨ihob, ihpfx⟩ := ihthen pfx bpfx ob ht
          rw [hss]
          refine ⟨fun n hn => ?_, fun n hn => ?_⟩
          · rcases List.mem_append.mp (ihob n hn) with hp | hs
            · exact List.mem_append_left _ hp
            · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hs))
          · rcases List.mem_append.mp (ihpfx n hn) with hp | hs
            · exact List.mem_append_left _ hp
            · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hs))
        · obtain ⟨ihob, ihpfx⟩ := ihelse pfx bpfx ob he'
          rw [hss]
          refine ⟨fun n hn => ?_, fun n hn => ?_⟩
          · rcases List.mem_append.mp (ihob n hn) with hp | hs
            · exact List.mem_append_left _ hp
            · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hs))
          · rcases List.mem_append.mp (ihpfx n hn) with hp | hs
            · exact List.mem_append_left _ hp
            · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hs))
      · obtain ⟨ihob, ihpfx⟩ := ihrest pfx bpfx ob hr
        rw [hss]
        refine ⟨fun n hn => ?_, fun n hn => ?_⟩
        · rcases List.mem_append.mp (ihob n hn) with hp | hs
          · exact List.mem_append_left _ hp
          · exact List.mem_append_right _ (List.mem_append_right _ hs)
        · rcases List.mem_append.mp (ihpfx n hn) with hp | hs
          · exact List.mem_append_left _ hp
          · exact List.mem_append_right _ (List.mem_append_right _ hs)

/-! ## `PStep`: the command relation (the `EvalCmd` analog)

One leaf command, pre-state → post-state. The signature is the arrow
`(Φ, cmd, wf, fIn) → (Φ', fOut)` with all inputs grouped then both outputs adjacent. `wf` is taken
whole and the rule's value condition denotes at the typing projected from it via the
`preprocessed_*_inv` lemmas, so `PStep` cannot be formed from an ill-typed command — the domain
excludes it, making typing-stuckness structurally impossible.

Per-command semantics (matching `Core.PStep`'s leaf cases):
  • `assume b`  — steps iff `b` denotes true; false is pruned (no inhabitant), `f ↦ f`.
  • `assert b`  — true ⇒ `f ↦ f`; false ⇒ `f ↦ true` (the sole flag writer).
  • `init x:=e` (`.det`) — steps iff the model pins `x` to `⟦e⟧`; mismatch pruned; `f ↦ f`,
    `Φ ↦ Φ++[(x,mτ)]`.
  • `init x:=*` (havoc) / `cover` — no-op, `f ↦ f` (havoc grows `Φ`, `cover` does not).
Branching lives on `PStepStar` (the `Config`-level structure).
-/

/-- **The command step relation.** One leaf command as the pre→post arrow
    `(Φ, cmd, wf, fIn) → (Φ', fOut)`: inputs `(Φ, cmd, wf, fIn)` grouped — with the command
    well-formedness `wf : CmdPreprocessed Ψ Φ cmd` a genuine index — then outputs `(Φ', fOut)`. `Φ'`
    is the context transition owned by the step (unchanged for assume/assert, `Φ ++ [(name, mτ)]` for
    init). The value condition denotes at the typing projected from `wf` (`assume_hb`/`assert_hb`).
    `PStep` cannot be formed from an ill-typed command (no `wf` to give), so typing-stuckness is
    excluded from the domain. -/
inductive PStep {Ψ : FnCtx} (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) :
    (Φ : FVarCtx) → (cmd : Statement) → {Φ' : FVarCtx} → CmdPreprocessed Ψ Φ cmd Φ' →
    (fIn : Bool) → (fOut : Bool) → Prop where
  /-- `assume b` on a live path (`b` denotes TRUE at the typing projected from `wf`); `Φ' = Φ`. -/
  | assumeLive (Φ : FVarCtx) (l : String) (b : Expression.Expr) (md : MetaData Expression) (f : Bool)
               (wf : CmdPreprocessed Ψ Φ (Statement.assume l b md) Φ)
               (hv : (simpDenote opInterp fvarVal .nil b (.tcons "bool" [])
                       (HasSimpType_implies_HasTypeA wf.assume_hb) : Bool) = true) :
      PStep opInterp fvarVal Φ (Statement.assume l b md) wf f f
  /-- `assert b` that HOLDS: flag unchanged; `Φ' = Φ`. -/
  | assertPass (Φ : FVarCtx) (l : String) (b : Expression.Expr) (md : MetaData Expression) (f : Bool)
               (wf : CmdPreprocessed Ψ Φ (Statement.assert l b md) Φ)
               (hv : (simpDenote opInterp fvarVal .nil b (.tcons "bool" [])
                       (HasSimpType_implies_HasTypeA wf.assert_hb) : Bool) = true) :
      PStep opInterp fvarVal Φ (Statement.assert l b md) wf f f
  /-- `assert b` that FAILS: flag set to `true` (the sole writer); `Φ' = Φ`. -/
  | assertFail (Φ : FVarCtx) (l : String) (b : Expression.Expr) (md : MetaData Expression) (f : Bool)
               (wf : CmdPreprocessed Ψ Φ (Statement.assert l b md) Φ)
               (hv : (simpDenote opInterp fvarVal .nil b (.tcons "bool" [])
                       (HasSimpType_implies_HasTypeA wf.assert_hb) : Bool) = false) :
      PStep opInterp fvarVal Φ (Statement.assert l b md) wf f true
  /-- `init x := e` (`.det`) on a live path: the model pins `x` to `⟦e⟧`. Output context is `wf`'s
      index `Φ ++ [(name, mτ)]`, with `mτ` threading by unification from `wf`. The pin `hpin` is a
      plain proposition at `wf`'s body typing, projected from `wf` via `initDet_he`. -/
  | initDetLive (Φ : FVarCtx) (name : Expression.Ident) (ty : Expression.Ty) (mτ : LMonoTy)
                (e : Expression.Expr) (md : MetaData Expression) (f : Bool)
                (wf : CmdPreprocessed Ψ Φ (Statement.init name ty (.det e) md)
                        (Φ ++ [(name.name, mτ)]))
                (hpin : VarDef.Consistent opInterp fvarVal ⟨name.name, mτ, e⟩
                          (HasSimpType_implies_HasTypeA wf.initDet_he)) :
      PStep opInterp fvarVal Φ (Statement.init name ty (.det e) md) wf f f
  /-- `init x := *` (havoc): no-op flag; OUTPUT context `wf`'s index `Φ ++ [(name, mτ)]`. -/
  | initNondet (Φ : FVarCtx) (name : Expression.Ident) (ty : Expression.Ty) (mτ : LMonoTy)
               (md : MetaData Expression) (f : Bool)
               (wf : CmdPreprocessed Ψ Φ (Statement.init name ty .nondet md)
                       (Φ ++ [(name.name, mτ)])) :
      PStep opInterp fvarVal Φ (Statement.init name ty .nondet md) wf f f

/-- **`failed` is monotone under one command step.** `assertFail` is the only writer; every other
    rule copies `f`. -/
theorem PStep.failed_mono {Ψ} {opInterp fvarVal} {Φ Φ'} {cmd : Statement}
    {wf : CmdPreprocessed Ψ Φ cmd Φ'} {fIn fOut : Bool}
    (h : PStep (Ψ := Ψ) opInterp fvarVal Φ cmd wf fIn fOut) : fIn = true → fOut = true := by
  cases h <;> simp_all

/-- **Compose a command well-formedness with a tail well-formedness into a whole-body
    `Preprocessed`.** The command witness `wfc : CmdPreprocessed Ψ Φ cmd Φ'` and the tail's
    `hrest : Preprocessed Ψ Φ' rest` are exactly the fields of `Preprocessed.cons`, so composition is
    the constructor. This is how well-formedness flows forward in the traversal. -/
theorem consPreprocessed {Ψ} {Φ Φ'} {cmd : Statement} {rest : Statements}
    (wfc : CmdPreprocessed Ψ Φ cmd Φ')
    (hrest : Preprocessed Ψ Φ' rest) :
    Preprocessed Ψ Φ (cmd :: rest) :=
  .cons Φ Φ' cmd rest wfc hrest

/-! ## `PStepStar`: the traversal (sequencing and branching, the `Config`-level analog)

Carries the whole statement list `ss` and its whole-list `Preprocessed` witness as a threaded index,
with the flag threading `fIn → fOut`. It is cons-shaped so well-formedness flows forward: `consCmd`
runs one leaf `PStep` and composes the tail's well-formedness via `consPreprocessed`. Branching is
here (three `.ite` constructors), matching production's `Config`-level structure. The per-step `Φ'`
of a `consCmd` is constructor-local, so `induction`/`cases` never wide-inverts a `PStep`.
-/

/-- **The traversal relation.** `PStepStar Ψ … Φ ss wf fIn fOut` : starting the well-formed body
    `ss` (WF witness `wf`) with failure flag `fIn`, some execution path ends with flag `fOut`. -/
inductive PStepStar {Ψ : FnCtx} (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) :
    (Φ : FVarCtx) → (ss : Statements) → Preprocessed Ψ Φ ss →
    (fIn : Bool) → (fOut : Bool) → Prop where
  /-- Empty body: flag unchanged. -/
  | nil (Φ : FVarCtx) (wf : Preprocessed Ψ Φ []) (f : Bool) :
      PStepStar opInterp fvarVal Φ [] wf f f
  /-- One leaf command, then the tail. WF flows FORWARD: the command WF `wfc : CmdPreprocessed …`
      (which `hstep` is indexed by) composes with the tail WF `hrestwf` via `consPreprocessed` to
      form THIS node's whole-list index — a single witness.
      `Φ'` is the command's output context (constructor-local). -/
  | consCmd (Φ Φ' : FVarCtx) (cmd : Statement) (rest : Statements) (fIn fMid fOut : Bool)
            (wfc : CmdPreprocessed Ψ Φ cmd Φ')
            (hstep : PStep (Ψ := Ψ) opInterp fvarVal Φ cmd wfc fIn fMid)
            (hrestwf : Preprocessed Ψ Φ' rest)
            (hrest : PStepStar opInterp fvarVal Φ' rest hrestwf fMid fOut) :
      PStepStar opInterp fvarVal Φ (cmd :: rest) (consPreprocessed wfc hrestwf) fIn fOut
  /-- `.ite` — branch into the THEN body (self-contained; WF projected from `wf`). -/
  | iteLeft (Φ : FVarCtx) (thenb elseb : Statements) (md : MetaData Expression) (rest : Statements)
            (fIn fOut : Bool)
            (wf : Preprocessed Ψ Φ (Stmt.ite .nondet thenb elseb md :: rest))
            (hthen : PStepStar opInterp fvarVal Φ thenb (preprocessed_ite_inv wf).1 fIn fOut) :
      PStepStar opInterp fvarVal Φ (Stmt.ite .nondet thenb elseb md :: rest) wf fIn fOut
  /-- `.ite` — branch into the ELSE body (self-contained). -/
  | iteRight (Φ : FVarCtx) (thenb elseb : Statements) (md : MetaData Expression) (rest : Statements)
             (fIn fOut : Bool)
             (wf : Preprocessed Ψ Φ (Stmt.ite .nondet thenb elseb md :: rest))
             (helse : PStepStar opInterp fvarVal Φ elseb (preprocessed_ite_inv wf).2.1 fIn fOut) :
      PStepStar opInterp fvarVal Φ (Stmt.ite .nondet thenb elseb md :: rest) wf fIn fOut
  /-- `.ite` — the continuation `rest` after the branch (from the PRE-branch context/flag). -/
  | iteRest (Φ : FVarCtx) (thenb elseb : Statements) (md : MetaData Expression) (rest : Statements)
            (fIn fOut : Bool)
            (wf : Preprocessed Ψ Φ (Stmt.ite .nondet thenb elseb md :: rest))
            (hcont : PStepStar opInterp fvarVal Φ rest (preprocessed_ite_inv wf).2.2 fIn fOut) :
      PStepStar opInterp fvarVal Φ (Stmt.ite .nondet thenb elseb md :: rest) wf fIn fOut

/-- **`failed` is monotone along a traversal.** If a path starts failed it ends failed. Front-first
    induction (cons): the head command preserves the flag (`PStep.failed_mono`), the tail by IH. -/
theorem PStepStar.failed_mono {Ψ} {opInterp fvarVal} {Φ ss wf} {fIn fOut : Bool}
    (h : PStepStar (Ψ := Ψ) opInterp fvarVal Φ ss wf fIn fOut) : fIn = true → fOut = true := by
  induction h with
  | nil => exact id
  | consCmd Φ Φ' cmd rest fIn fMid fOut wfc hstep hrestwf hrest ih =>
      exact fun hf => ih (hstep.failed_mono hf)
  | iteLeft _ _ _ _ _ _ _ _ _ ih => exact ih
  | iteRight _ _ _ _ _ _ _ _ _ ih => exact ih
  | iteRest _ _ _ _ _ _ _ _ _ ih => exact ih

/-! ## Validity (per-procedure, at its prefix context), `Denotes`-free

`ProcValid` takes the whole-body well-formedness witness `hpre` and the axiom/distinct/reachable
function-axiom typing witnesses as explicit parameters (all available from the emitter's
well-formedness facts: `CoreCtx.Good` for `axioms`/`distincts`, and `declWF .proc`'s reachable
function-axiom clause). Every model-satisfaction hypothesis is stated via raw `simpDenote … = true`,
keeping the whole validity layer witness-carrying, consistent with `PStep`/`PStepStar`.

Function axioms are scoped to reachable functions, matching `declWF .proc`: a blanket
`∀ ax ∈ c.fnAxioms` clause is unsatisfiable (the default factory's polymorphic Map/Sequence seed
axioms quantify over type variables and cannot be `HasSimpType`-typed), so satisfaction is asserted
only where a `HasSimpType` witness exists — the reachable functions' axioms.
-/

/-- **A distinctness group holds — witness-carrying.** At the shared base type `τ` (from `Good`),
    the elements denote to PAIRWISE-DISTINCT values, via RAW `simpDenote` at the supplied per-element
    typing witnesses `hτ`. The `Denotes`-free analog of `Core.Preprocessed.DistinctHolds`. -/
def DistinctHoldsW (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (es : List Expression.Expr) (τ : LMonoTy)
    (hτ : ∀ e ∈ es, LExpr.HasTypeA [] e τ) : Prop :=
  (es.attach.map (fun x => simpDenote opInterp fvarVal .nil x.1 τ (hτ x.1 x.2))).Pairwise (· ≠ ·)

/-- **Body validity of one procedure at prefix-context `c`** — the dependent-denote, `Denotes`-free
    form. Parameters carry the typing witnesses:
      • `hpre`  — the body `ss` is `Preprocessed` at `c.Ψ` (empty `Φ`); the head index every
        `PStepStar` run is seeded with;
      • `haxT`  — each global axiom is bool-typed (from `CoreCtx.Good`);
      • `hfaxT` — each REACHABLE function's axioms are bool-typed (from `declWF .proc`);
      • `hdT`   — each distinct group has a shared base-type typing (from `CoreCtx.Good`).
    For every factory-consistent model that SATISFIES those axioms/distincts (stated via raw
    `simpDenote`), no traversal path from `⟨ss, false⟩` ends failed. -/
def ProcValid (c : CoreCtx) (ss : Statements)
    (hpre  : Preprocessed c.Ψ [] ss)
    (haxT  : ∀ e ∈ c.axioms, LExpr.HasSimpType [] c.Ψ [] e (.tcons "bool" []))
    (hfaxT : ∀ g ∈ reachableFuncs c.F (c.procSeeds ss), ∀ f, c.F[g]? = some f →
              ∀ ax ∈ f.axioms, LExpr.HasSimpType [] c.Ψ [] ax (.tcons "bool" []))
    (hdT   : ∀ es ∈ c.distincts, 2 ≤ es.length ∧ ∃ τ, LExpr.MonoTyIsBase τ ∧
              ∀ e ∈ es, LExpr.HasSimpType [] c.Ψ [] e τ) : Prop :=
  ∀ (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp),
    Lambda.Factory.InterpConsistent simpTcInterp opInterp c.F →
    -- global axioms hold (raw `simpDenote` at their `Good` typing witnesses)
    (∀ e (he : e ∈ c.axioms),
      (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA (haxT e he)) : Bool) = true) →
    -- reachable function axioms hold (raw `simpDenote` at their `declWF .proc` typing witnesses)
    (∀ g (hg : g ∈ reachableFuncs c.F (c.procSeeds ss)) f (hf : c.F[g]? = some f)
       ax (hax : ax ∈ f.axioms),
      (simpDenote opInterp fvarVal .nil ax (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA (hfaxT g hg f hf ax hax)) : Bool) = true) →
    -- distinct groups hold (witness-carrying)
    (∀ es (hes : es ∈ c.distincts),
      DistinctHoldsW opInterp fvarVal es (hdT es hes).2.choose
        (fun e he => HasSimpType_implies_HasTypeA ((hdT es hes).2.choose_spec.2 e he))) →
    ∀ fOut, PStepStar (Ψ := c.Ψ) opInterp fvarVal [] ss hpre false fOut → fOut = false

/-! ## `Program.ValidFrom` / `Program.Valid`: the prefix-fold and headline notion

The fold carries `CoreCtx.Good c` as a threading invariant (preserved by `CoreCtx.Good.step`). At
each `.proc`, `Good` supplies the axiom/distinct typing witnesses (`haxT`, `hdT`), and `declWF .proc`
supplies `hpre` and `hfaxT`.
-/

/-- **Fold the prefix context and require `ProcValid` at each procedure's own prefix,** supplying
    the typing witnesses from `Good` + `declWF .proc`. Uses the parameter-form `ProcValid` (all
    witnesses explicit, fully `Denotes`-free).

    Takes the `Good` invariant + the per-decl `declWF` facts so it can supply typing witnesses to
    `ProcValid`. It is structurally recursive on `decls` and threads `Good` via `Good.step`. -/
def Program.ValidFrom : (decls : List Decl) → (c : CoreCtx) → c.Good →
    Program.WFfrom decls c → Prop
  | [], _, _, _ => True
  | d :: rest, c, hgood, hwf =>
    (match d with
     | .proc p _ =>
        match p.body with
        | .structured ss =>
            ∀ (hpre : Preprocessed c.Ψ [] ss)
              (hfaxT : ∀ g ∈ reachableFuncs c.F (c.procSeeds ss), ∀ f, c.F[g]? = some f →
                        ∀ ax ∈ f.axioms, LExpr.HasSimpType [] c.Ψ [] ax (.tcons "bool" [])),
              ProcValid c ss hpre hgood.1 hfaxT hgood.2
        | .cfg _ => True
     | _ => True) ∧
    Program.ValidFrom rest (c.step d) (hgood.step hwf.1) hwf.2

/-- **The preprocessed Core program is VALID** — every procedure's obligations hold, each at the
    declaration context accumulated up to that procedure. Dependent-denote, `Denotes`-free form.
    Takes `Program.WF` so it can thread `Good` + `declWF` down to each proc. -/
def Program.Valid (p : Program) (hwf : Program.WF p) : Prop :=
  Program.ValidFrom p.decls CoreCtx.init CoreCtx.init_Good hwf

/-! ## Soundness

Fully proven (no `sorry`), `Denotes`-free throughout. The proven call tree:

    program_valid_of_oblProgramsValid           -- headline: emitted-obls-valid ⟹ Program.Valid p hwf
      └─ procValid_of_obligationsValid           -- per-proc; failing run ↦ contradiction
           ├─ failing_run_corresponds             -- failing run ↦ an EMITTED obligation OF `ss`
           └─ obligationValidW_denotes            -- model-transfer bridge (reachable-scoped, raw simpDenote)

Every satisfaction hypothesis is raw `simpDenote … witness = true`, with the collision at the top
closed by proof-irrelevance on the typing witness. Function
axioms are reachable-scoped: the bridge queries axioms only of functions emitted for the obligation,
all reachable, bridged to the proc seeds via `bodyObligations_seeds_subset` and `reachableFuncs_mono`.

`OblProgram.Valid`, `toOblPrograms`, `procObligations`, `bodyObligations`, `OblProgramWF`,
`SeedBuiltinConsistent`, `SeedFactoryFuncsWF`, and the model-transfer helpers
(`distincts_sat_of_global`, `fnDefsOpConsistent_of_factoryConsistent`, …) are reused from `Core`
(emitter side). `SeedBuiltinConsistent`/`SeedFactoryFuncsWF` remain premises here, discharged for the
concrete factory downstream in `SeedFactory`.
-/

/-- **First-failure ↔ obligation correspondence.** A failing traversal of `ss` (from the accumulated
    obligation prefix `pfx`, which the model satisfies) reaches an emitted obligation
    `(bpfx, b) ∈ bodyObligations pfx ss` whose prefix the model also satisfies and whose goal `b`
    denotes false. `pfx` threads the fired path (mirroring `bodyObligations`'s own accumulator), so
    the reached assert is provably an obligation of `ss`.

    The prefix-satisfaction predicate is `Core.Preprocessed.PrefixSat` (erased-`OblCommand` side).
    Proven by a single induction on the traversal: the `assertFail` case is the target obligation, and
    flag-preserving commands recurse with `pfx` extended exactly as `bodyObligations` accumulates. -/
theorem failing_run_corresponds {Ψ} {opInterp fvarVal}
    {Φ ss} {wf : Preprocessed Ψ Φ ss} {fIn fOut : Bool}
    (pfx : List OblCommand) (hpfx : Core.Preprocessed.PrefixSat opInterp fvarVal pfx)
    (h : PStepStar (Ψ := Ψ) opInterp fvarVal Φ ss wf fIn fOut) (hfi : fIn = false)
    (hfo : fOut = true) :
    ∃ bpfx b, (bpfx, b) ∈ bodyObligations pfx ss ∧
      Core.Preprocessed.PrefixSat opInterp fvarVal bpfx ∧
      ∃ hb : LExpr.HasTypeA [] b (.tcons "bool" []),
        (simpDenote opInterp fvarVal .nil b (.tcons "bool" []) hb : Bool) = false := by
  -- Induct on the traversal; `pfx`/`hpfx`/`hfi`/`hfo` generalized so the IH applies at the extended
  -- prefixes each command contributes (mirroring `bodyObligations`'s own accumulator recursion).
  -- `hfi : fIn = false` rules out the `nil`/started-failed cases; flag-preserving commands recurse
  -- with the same `false` start, and `assertFail` is the target (never recurses).
  induction h generalizing pfx with
  | nil Φ wf f =>
      -- `nil`: `fOut = fIn = f`; `hfi : f = false` and `hfo : f = true` contradict.
      subst hfi; exact absurd hfo (by simp)
  | consCmd Φ Φ' cmd rest fIn fMid fOut wfc hstep hrestwf hrest ih =>
      -- `bodyObligations pfx (cmd :: rest)` reduces by the leading command; `cases hstep` splits on
      -- which leaf rule fired.
      cases hstep with
      | assertFail l b md f wf hv =>
          -- THIS failing assert is the target obligation `(pfx, b)`, the head of `bodyObligations`.
          rw [bodyObligations]
          exact ⟨pfx, b, List.mem_cons_self .., hpfx, _, hv⟩
      | assertPass l b md f wf hv =>
          -- discharged assert: tail resumes from the SAME `pfx`; flag preserved (fMid = f = fIn).
          rw [bodyObligations]
          obtain ⟨bpfx, b', hmem, hsat, hb⟩ := ih pfx hpfx hfi hfo
          exact ⟨bpfx, b', List.mem_cons_of_mem _ hmem, hsat, hb⟩
      | assumeLive l b md f wf hv =>
          -- extend the accumulator with `.assume b` (fired true), then recurse (flag preserved).
          rw [bodyObligations]
          refine ih (pfx ++ [OblCommand.assume b]) ⟨fun e he => ?_, fun v hv' => ?_⟩ hfi hfo
          · rcases List.mem_append.mp he with h | h
            · exact hpfx.1 e h
            · rw [List.mem_singleton] at h; cases h
              exact ⟨_, hv⟩
          · rcases List.mem_append.mp hv' with h | h
            · exact hpfx.2 v h
            · rw [List.mem_singleton] at h; cases h
      | initDetLive name ty mτ e md f wf hpin =>
          -- `mτ` comes DIRECTLY from the step (its `wf` index / field); `hmono`/`he` from inversion.
          rw [bodyObligations]
          obtain ⟨mτ', hΦ', hmono, he, _⟩ := wf.initDet_inv
          -- `mτ' = mτ` from the shared output index `Φ ++ [(name, ·)]`.
          have hmτ : mτ' = mτ := by
            simp only [List.append_right_inj, List.cons.injEq, Prod.mk.injEq] at hΦ'; exact hΦ'.1.2.symm
          subst hmτ
          simp only [initDecl, hmono]
          refine ih (pfx ++ [OblCommand.varDef ⟨name.name, mτ', e⟩])
            ⟨fun e' he' => ?_, fun v hv' => ?_⟩ hfi hfo
          · rcases List.mem_append.mp he' with h | h
            · exact hpfx.1 e' h
            · rw [List.mem_singleton] at h; cases h
          · rcases List.mem_append.mp hv' with h | h
            · exact hpfx.2 v h
            · rw [List.mem_singleton] at h; cases h
              -- `hpin` IS the consistency (a plain proposition now); supply it as the varDef pin.
              exact ⟨_, hpin⟩
      | initNondet name ty mτ md f wf =>
          -- `mτ` from the step; `hmono` from inversion.
          rw [bodyObligations]
          obtain ⟨mτ', hΦ', hmono, _⟩ := wf.initNondet_inv
          have hmτ : mτ' = mτ := by
            simp only [List.append_right_inj, List.cons.injEq, Prod.mk.injEq] at hΦ'; exact hΦ'.1.2.symm
          subst hmτ
          simp only [initDecl, hmono]
          refine ih (pfx ++ [OblCommand.fvarDecl name.name mτ'])
            ⟨fun e' he' => ?_, fun v hv' => ?_⟩ hfi hfo
          · rcases List.mem_append.mp he' with h | h
            · exact hpfx.1 e' h
            · rw [List.mem_singleton] at h; cases h
          · rcases List.mem_append.mp hv' with h | h
            · exact hpfx.2 v h
            · rw [List.mem_singleton] at h; cases h
  | iteLeft Φ thenb elseb md rest fIn fOut wf hthen ih =>
      rw [bodyObligations]
      obtain ⟨bpfx, b', hmem, hsat, hb⟩ := ih pfx hpfx hfi hfo
      exact ⟨bpfx, b', List.mem_append_left _ (List.mem_append_left _ hmem), hsat, hb⟩
  | iteRight Φ thenb elseb md rest fIn fOut wf helse ih =>
      rw [bodyObligations]
      obtain ⟨bpfx, b', hmem, hsat, hb⟩ := ih pfx hpfx hfi hfo
      exact ⟨bpfx, b', List.mem_append_left _ (List.mem_append_right _ hmem), hsat, hb⟩
  | iteRest Φ thenb elseb md rest fIn fOut wf hcont ih =>
      rw [bodyObligations]
      obtain ⟨bpfx, b', hmem, hsat, hb⟩ := ih pfx hpfx hfi hfo
      exact ⟨bpfx, b', List.mem_append_right _ hmem, hsat, hb⟩

/-- **Model-transfer bridge — reachable-scoped, raw-`simpDenote`.** The
    dependent-denote analog of `Core.Preprocessed.obligationValid_denotes`. Given a factory-consistent
    model that satisfies the global axioms, the REACHABLE function axioms, and the distinct groups
    (all via raw `simpDenote`, matching `ProcValid`'s hypotheses), plus `OblProgram.Valid Q` for the
    emitted `Q = ⟨obligationPrefix c fns ++ bpfx, b⟩` whose `bpfx` the model satisfies (`PrefixSat`),
    the obligation `Q.obligation` denotes TRUE (at some typing witness).

    Two design points: (i) the function-axiom hypothesis is scoped to `reachableFuncs` (the
    polymorphic seed axioms have no `HasSimpType` witness, so a blanket clause is unsatisfiable);
    (ii) all satisfaction hypotheses are raw `simpDenote`. The soundness discharge routes
    function-axiom satisfaction through the reachability bridges (`bodyObligations_seeds_subset` /
    `reachableFuncs_mono`). Discharges the four preconditions (op/fnDef consistency, varDef pins,
    distincts), with the assume path reachable-scoped. -/
theorem obligationValidW_denotes (c : CoreCtx) (ss : Statements) (fns : List String)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (hbc : CoreCtx.SeedBuiltinConsistent) (hffwf : c.FactoryFuncsWF) (hseed : c.SeedWF)
    (hFC : Lambda.Factory.InterpConsistent simpTcInterp opInterp c.F)
    -- typing witnesses (from `Good` + `declWF .proc`), and satisfaction stated at them:
    (haxT  : ∀ e ∈ c.axioms, LExpr.HasSimpType [] c.Ψ [] e (.tcons "bool" []))
    (hfaxT : ∀ g ∈ reachableFuncs c.F (c.procSeeds ss), ∀ f, c.F[g]? = some f →
              ∀ ax ∈ f.axioms, LExpr.HasSimpType [] c.Ψ [] ax (.tcons "bool" []))
    (hdT   : ∀ es ∈ c.distincts, 2 ≤ es.length ∧ ∃ τ, LExpr.MonoTyIsBase τ ∧
              ∀ e ∈ es, LExpr.HasSimpType [] c.Ψ [] e τ)
    (hax : ∀ e (he : e ∈ c.axioms),
      (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA (haxT e he)) : Bool) = true)
    (hfnax : ∀ g (hg : g ∈ reachableFuncs c.F (c.procSeeds ss)) f (hf : c.F[g]? = some f)
       ax (hax : ax ∈ f.axioms),
      (simpDenote opInterp fvarVal .nil ax (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA (hfaxT g hg f hf ax hax)) : Bool) = true)
    (hdist : ∀ es (hes : es ∈ c.distincts),
      DistinctHoldsW opInterp fvarVal es (hdT es hes).2.choose
        (fun e he => HasSimpType_implies_HasTypeA ((hdT es hes).2.choose_spec.2 e he)))
    (Q : OblProgram) (bpfx : List OblCommand) (b : Expression.Expr)
    -- the emitted functions `fns` are all reachable from the PROC seeds (call site: obligation
    -- seeds ⊆ procSeeds via `bodyObligations_seeds_subset`, then `reachableFuncs_mono`).
    (hfns_sub : ∀ g ∈ fns, g ∈ reachableFuncs c.F (c.procSeeds ss))
    (hQcmds : Q.cmds = obligationPrefix c fns ++ bpfx)
    (_hQob : Q.obligation = b)
    (hpsat : Core.Preprocessed.PrefixSat opInterp fvarVal bpfx)
    (hbpfx_nodist : ∀ es, OblCommand.distinct es ∉ bpfx)
    (hbpfx_nofndef : ∀ d, OblCommand.fnDef d ∉ bpfx)
    (hwfQ : OblProgramWF Q) (hVQ : OblProgram.Valid Q hwfQ) :
    ∃ hb : LExpr.HasTypeA [] Q.obligation (.tcons "bool" []),
      (simpDenote opInterp fvarVal .nil Q.obligation (.tcons "bool" []) hb : Bool) = true := by
  -- Discharge the four preconditions; the assume path is reachable-scoped (a blanket `c.fnAxioms`
  -- clause is unprovable — polymorphic seeds).
  refine ⟨HasSimpType_implies_HasTypeA hwfQ.obligationWF, ?_⟩
  -- (1) op-consistency: the div-by-zero model supplies `divByZero`/`modByZero`, inferred at `hVQ`
  --     from `hOpCon`.
  obtain ⟨divByZero, modByZero, hOpCon⟩ :
      ∃ divByZero modByZero, OpInterpConsistent divByZero modByZero opInterp :=
    opInterpConsistent_of_factoryConsistent hbc hseed hFC
  -- (1a) emitted fnDefs op-consistent.
  have hFnDefs : FnDefs.OpConsistent opInterp fvarVal Q.defs
      (fun d hd => ((hwfQ.defsWF) d hd).hasTypeA) :=
    fnDefsOpConsistent_of_factoryConsistent hffwf hFC hQcmds hbpfx_nofndef _
  -- (2) varDefs pinned: any `.varDef ∈ Q.cmds` is a `bpfx` varDef, pinned by `hpsat.2`.
  have hVarDefs : VarDefs.Consistent opInterp fvarVal Q.varDefs
      (fun v hv => (hwfQ.varDefsWF v hv).hasTypeA) := by
    intro v hv
    have hvcmd : OblCommand.varDef v ∈ Q.cmds := by
      have := (mem_foldl_varDefs (cmds := Q.cmds) (c := {}) (v := v)).mp hv; simpa using this
    rw [hQcmds] at hvcmd
    rcases List.mem_append.mp hvcmd with h | h
    · exact absurd h (obligationPrefix_no_varDef c fns v)
    · obtain ⟨hty, hpin⟩ := hpsat.2 v h
      have hwty : LExpr.HasTypeA [] v.body v.ty := (hwfQ.varDefsWF v hv).hasTypeA
      rw [VarDef.Consistent] at hpin ⊢; rw [proof_irrel hty hwty] at hpin; exact hpin
  -- (3) assumptions — REACHABLE-SCOPED assume discharge.
  have hAsms : LambdaModelSatisfiesAsms Q hwfQ opInterp fvarVal := by
    intro e he
    have hecmd : OblCommand.assume e ∈ Q.cmds := by
      have := (mem_foldl_assumptions (cmds := Q.cmds) (c := {}) (e := e)).mp he; simpa using this
    -- goal: `⟦e⟧ = true` at the WF witness. Obtain `⟦e⟧ = true` at SOME witness, then proof-irrel.
    -- `hsome : Denotes … e true` (the existential); `Denotes.simpDenote_eq` transports it to the
    -- specific WF witness the goal uses (by proof-irrelevance).
    suffices hsome : Core.Preprocessed.Denotes opInterp fvarVal e true by
      exact Core.Preprocessed.Denotes.simpDenote_eq hsome _
    rw [hQcmds] at hecmd
    rcases List.mem_append.mp hecmd with h | h
    · -- from `obligationPrefix`: a global axiom (`hax`) or an EMITTED (reachable) fn-axiom (`hfnax`).
      unfold obligationPrefix at h
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with hdecl | hfnaxm
          · -- emitFuncDecls: fnDecl/fnDef only, never assume
            obtain ⟨g, _, hg⟩ := List.mem_filterMap.mp hdecl
            rcases hgc : c.F[g]? with _ | f
            · rw [hgc] at hg; simp at hg
            · rw [hgc] at hg; simp only [Option.map_some, Option.some.injEq] at hg
              unfold emitFuncDecl at hg; split at hg <;> simp at hg
          · -- emitFuncAxioms: `e ∈ f.axioms` for `f = c.F[g]?`, `g ∈ fns` (reachable) ⟹ `hfnax`
            obtain ⟨g, hgmem, hg⟩ := List.mem_flatMap.mp hfnaxm
            rcases hgc : c.F[g]? with _ | f
            · rw [hgc] at hg; simp at hg
            · rw [hgc] at hg
              simp only [Option.map_some, Option.getD_some, funcAxiomAssumes] at hg
              obtain ⟨x, hxmem, hx⟩ := List.mem_map.mp hg
              rw [OblCommand.assume.injEq] at hx; subst hx
              exact ⟨_, hfnax g (hfns_sub g hgmem) f hgc x hxmem⟩
        · -- global distincts: not assumes
          obtain ⟨x, _, hx⟩ := List.mem_map.mp h; simp at hx
      · -- global axioms `c.axioms.map .assume`
        obtain ⟨x, hxmem, hx⟩ := List.mem_map.mp h
        rw [OblCommand.assume.injEq] at hx; subst hx
        exact ⟨_, hax x hxmem⟩
    · -- from `bpfx`: `hpsat.1` gives `Denotes e true = ∃ h, simpDenote … = true`
      exact hpsat.1 e h
  -- (4) distincts — convert our `DistinctHoldsW` to Core's `DistinctHolds`.
  have hDists : LambdaModelSatisfiesDistincts Q hwfQ opInterp fvarVal :=
    distincts_sat_of_global c fns opInterp fvarVal
      (fun es hes => ⟨(hdT es hes).2.choose,
        (fun e he => HasSimpType_implies_HasTypeA ((hdT es hes).2.choose_spec.2 e he)),
        hdist es hes⟩)
      Q bpfx hQcmds hbpfx_nodist hwfQ
  -- assemble
  exact hVQ divByZero modByZero opInterp hOpCon fvarVal hFnDefs hVarDefs hAsms hDists

/-- **Per-procedure soundness.** Given the emitted obligations of `ss` are all `OblProgram.Valid`,
    `ss` is `ProcValid` at `c`. The dependent-denote analog of
    `Core.Preprocessed.procValid_of_obligationsValid`, adapted to our parameter-form `ProcValid`:
    take a failing run, get the offending emitted obligation via `failing_run_corresponds`, and
    collide its `OblProgram.Valid`-forced truth against the run's false-denotation. -/
theorem procValid_of_obligationsValid {c : CoreCtx} {ss : Statements}
    (hpre : Preprocessed c.Ψ [] ss)
    (haxT  : ∀ e ∈ c.axioms, LExpr.HasSimpType [] c.Ψ [] e (.tcons "bool" []))
    (hfaxT : ∀ g ∈ reachableFuncs c.F (c.procSeeds ss), ∀ f, c.F[g]? = some f →
              ∀ ax ∈ f.axioms, LExpr.HasSimpType [] c.Ψ [] ax (.tcons "bool" []))
    (hdT   : ∀ es ∈ c.distincts, 2 ≤ es.length ∧ ∃ τ, LExpr.MonoTyIsBase τ ∧
              ∀ e ∈ es, LExpr.HasSimpType [] c.Ψ [] e τ)
    (hbc : CoreCtx.SeedBuiltinConsistent)
    (hffwf : c.FactoryFuncsWF)
    (hseed : c.SeedWF)
    (hWF : ∀ Q ∈ procObligations c ss, OblProgramWF Q)
    (hV : ∀ Q ∈ procObligations c ss, ∀ (hwfQ : OblProgramWF Q), OblProgram.Valid Q hwfQ) :
    ProcValid c ss hpre haxT hfaxT hdT := by
  -- Unfold `ProcValid`: fix a factory-consistent model satisfying axioms/fn-axioms/distincts and a
  -- run ending `fOut`. Suppose `fOut = true`; contradiction.
  intro opInterp fvarVal hFC hax hfnax hdist fOut hrun
  match hfo : fOut with
  | false => rfl
  | true =>
      exfalso
      -- The failing run reaches an EMITTED obligation `(bpfx, b)` of `ss` (from the empty,
      -- trivially-satisfied prefix), which the model satisfies and whose goal `b` denotes FALSE.
      -- (`hrun` here already has target flag `true` after the match.)
      obtain ⟨bpfx, b, hbomem, hpsat, hbA, hb_false⟩ :=
        failing_run_corresponds [] ⟨by simp, by simp⟩ hrun rfl rfl
      -- The emitted `Q` for `(bpfx, b)` (image of the `procObligations` map), with its concrete
      -- `obligationPrefix c fns ++ bpfx` shape and reachable `fns` exposed.
      obtain ⟨Q, hQmem, fns, hQcmds, hQob, hfns_sub⟩ :
          ∃ Q ∈ procObligations c ss, ∃ fns,
            Q.cmds = obligationPrefix c fns ++ bpfx ∧ Q.obligation = b ∧
            ∀ g ∈ fns, g ∈ reachableFuncs c.F (c.procSeeds ss) := by
        refine ⟨_, List.mem_map.mpr ⟨(bpfx, b), hbomem, rfl⟩, _, rfl, rfl, fun g hg => ?_⟩
        -- `fns = reachableOrdered c.F seeds ⊆ reachableFuncs c.F seeds`; obligation seeds ⊆ procSeeds.
        have hgreach : g ∈ reachableFuncs c.F _ := (List.mem_filter.mp hg).2 |> of_decide_eq_true
        obtain ⟨hsubob, hsubbpfx⟩ := bodyObligations_seeds_subset hpre [] bpfx b hbomem
        refine reachableFuncs_mono c.F (fun x hx => ?_) g hgreach
        unfold CoreCtx.procSeeds
        rcases List.mem_append.mp hx with h | hdist
        · rcases List.mem_append.mp h with h2 | hax'
          · rcases List.mem_append.mp h2 with hob | hbp
            · have := hsubob x hob; simp only [List.flatMap_nil, List.nil_append] at this
              exact List.mem_append_left _ (List.mem_append_left _ this)
            · have := hsubbpfx x hbp; simp only [List.flatMap_nil, List.nil_append] at this
              exact List.mem_append_left _ (List.mem_append_left _ this)
          · exact List.mem_append_left _ (List.mem_append_right _ hax')
        · exact List.mem_append_right _ hdist
      have hwfQ : OblProgramWF Q := hWF Q hQmem
      -- Model transfer (reachable-scoped, raw-`simpDenote` bridge): `OblProgram.Valid Q` forces
      -- `⟦Q.obligation⟧ = true`, contradicting `hb_false`.
      have hbtrue := obligationValidW_denotes c ss fns opInterp fvarVal hbc hffwf hseed hFC
        haxT hfaxT hdT hax hfnax hdist Q bpfx b hfns_sub hQcmds hQob hpsat
        (bodyObligations_no_distinct hpre [] (by simp) bpfx b hbomem)
        (bodyObligations_no_fnDef hpre [] (by simp) bpfx b hbomem) hwfQ (hV Q hQmem hwfQ)
      -- `hbtrue : ⟦Q.obligation⟧ = true` at SOME witness; `hb_false : ⟦b⟧ = false`; `Q.obligation = b`.
      -- Proof-irrelevance identifies the two witnesses, so `true = false`.
      rw [hQob] at hbtrue
      obtain ⟨hbA', hbtrue'⟩ := hbtrue
      rw [proof_irrel hbA' hbA] at hbtrue'
      rw [hbtrue'] at hb_false
      exact absurd hb_false (by simp)

/-- **Layer-1 soundness.** If every emitted obligation program is
    `OblProgram.Valid`, the preprocessed program is `Program.Valid`. Headline of the dependent-denote
    development, analog of `Core.Preprocessed.program_valid_of_oblProgramsValid`: folds `ValidFrom`
    over `decls`, discharging each proc via `procValid_of_obligationsValid`. -/
theorem program_valid_of_oblProgramsValid {p : Program} (hwf : Program.WF p)
    (hbc : CoreCtx.SeedBuiltinConsistent)
    (hseedFF : CoreCtx.SeedFactoryFuncsWF)
    (hValid : ∀ Q (hQ : Q ∈ toOblPrograms p), OblProgram.Valid Q (toOblPrograms_wf hwf hseedFF Q hQ)) :
    Program.Valid p hwf := by
  -- `Program.Valid p hwf = ValidFrom p.decls init init_Good hwf`. Generalize the fold over `decls`,
  -- `c`, and the threaded proof params `hgood`/`hwfrom` (proof-irrelevant), given every `Q` emitted
  -- from `c`-onward is `OblProgram.Valid`.
  unfold Program.Valid
  suffices h : ∀ (decls : List Decl) (c : CoreCtx) (hgood : c.Good) (hwfrom : Program.WFfrom decls c),
      c.FactoryFuncsWF → c.SeedWF →
      (∀ Q ∈ toOblProgramsFrom decls c, ∀ (hwfQ : OblProgramWF Q), OblProgram.Valid Q hwfQ) →
      Program.ValidFrom decls c hgood hwfrom by
    exact h p.decls CoreCtx.init CoreCtx.init_Good hwf hseedFF CoreCtx.init_SeedWF
      (fun Q hQmem _hwfQ => hValid Q hQmem)
  intro decls
  induction decls with
  | nil => intro c hgood hwfrom _ _ _; trivial
  | cons d rest ih =>
    intro c hgood hwfrom hffwf hseed hobl
    refine ⟨?_, ?_⟩
    · -- head conjunct: `ProcValid` (∀ its witnesses) if `d` is a structured proc, else trivial
      cases d with
      | proc p' md =>
        cases hb : p'.body with
        | structured ss =>
            simp only [hb]
            intro hpre hfaxT
            -- `hWF` (per-Q `OblProgramWF`) and `hV` (per-Q validity) both come from the emitted
            -- obligations being a prefix-slice of `toOblProgramsFrom (proc :: rest) c`.
            have hmemQ : ∀ Q ∈ procObligations c ss,
                Q ∈ toOblProgramsFrom (Decl.proc p' md :: rest) c := by
              intro Q hQ; rw [toOblProgramsFrom]; simp only [hb, List.mem_append]; exact Or.inl hQ
            refine procValid_of_obligationsValid hpre hgood.1 hfaxT hgood.2 hbc hffwf hseed
              (fun Q hQ => toOblProgramsFrom_WF c (Decl.proc p' md :: rest) hwfrom hgood hffwf hseed
                Q (hmemQ Q hQ))
              (fun Q hQ hwfQ => hobl Q (hmemQ Q hQ) hwfQ)
        | cfg _ => simp only [hb]
      | func _ _ => trivial
      | type _ _ => trivial
      | ax _ _ => trivial
      | distinct _ _ _ => trivial
      | recFuncBlock _ _ => trivial
    · -- tail: IH at the stepped context; tail obligations are a suffix of `toOblProgramsFrom (d::rest) c`
      apply ih (c.step d) (hgood.step hwfrom.1) hwfrom.2 (hffwf.step hwfrom.1) (hseed.step d)
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

end Core.Preprocessed.Dep
