/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
import all Strata.Languages.Core.PrototypeSMTGen.Core

open Core Lambda Imperative Std Core.Construct Core.Preprocessed Core.ModelTransfer Strata.SMT

/-!
# End-to-end soundness of the Core → SMT encoder

The whole encoder as a single function and its top-level soundness theorem. The encoder is a
two-stage map: stage 1 (`toOblPrograms`) fans a preprocessed `Program` into one `OblProgram` per
`assert`; stage 2 (`encode`) turns each `OblProgram` into an `SMTProgram`. `toSMTPrograms` is their
composition, so one `Except` value captures the whole compile.

The headline `program_valid_of_toSMTPrograms_unsat` is stated about that composition: on a
well-formed program the encoder always succeeds, and unsatisfiability of every emitted SMT program
implies the source `Program` is valid. It is factory-generic — parameterized over the seed
well-formedness (`SeedFactoryFuncsWF`) and builtin-consistency (`SeedBuiltinConsistent`) premises —
and composes the two stage theorems, Stage 1
`program_valid_of_oblProgramsValid` and Stage 2 `oblProgram_valid_of_smtUnsat`, with Stage-2
totality (`encode_succeeds`) lifted over the fan-out. The default-`Core.Factory` specialization
(discharging both premises via `SeedFactory`) is demonstrated in the tests.
-/

namespace Core.Preprocessed

/-- The whole encoder as one function: fan a `Program` out to its obligation programs, then encode
    each into an `SMTProgram` (or the first encode error). -/
def toSMTPrograms (p : Program) : Except Format (List SMTProgram) :=
  (toOblPrograms p).mapM encode

/-- The `mapM` membership bridge in `Except`: if a list encodes to `bs`, every element `a` encodes
    to some `b ∈ bs`. -/
theorem mapM_mem {α β ε} {l : List α} {f : α → Except ε β} {bs : List β}
    (h : l.mapM f = .ok bs) : ∀ a ∈ l, ∃ b, f a = .ok b ∧ b ∈ bs := by
  induction l generalizing bs with
  | nil => intro a ha; simp at ha
  | cons hd tl ih =>
    intro a ha
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · exact absurd h (by simp)
    · rename_i b hb
      split at h
      · exact absurd h (by simp)
      · rename_i bs' hbs'
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp ha with rfl | htl
        · exact ⟨b, hb, List.mem_cons_self ..⟩
        · obtain ⟨b', hb', hmem'⟩ := ih hbs' a htl
          exact ⟨b', hb', List.mem_cons_of_mem _ hmem'⟩

/-- **End-to-end soundness (factory-generic).** For any factory satisfying seed well-formedness
    (`hseedFF`) and builtin consistency (`hbc`), on a well-formed preprocessed program the whole
    encoder succeeds (so the `.error` branch is `False`), and on success unsatisfiability of every
    emitted SMT program implies the program is `Valid`. Composes Stage 1
    (`program_valid_of_oblProgramsValid`) and Stage 2 (`oblProgram_valid_of_smtUnsat`), with
    totality from `encode_succeeds` lifted over the fan-out by `mapM_succeeds`. -/
theorem program_valid_of_toSMTPrograms_unsat {p : Program} (hwf : Program.WF p)
    (hbc : CoreCtx.SeedBuiltinConsistent) (hseedFF : CoreCtx.SeedFactoryFuncsWF) :
    match toSMTPrograms p with
    | .ok progs => (∀ prog ∈ progs, SMTProgram.Unsat prog) → Program.Valid p
    | .error _  => False := by
  -- Totality: every obligation is WF (Stage 1) ⇒ encodes (Stage 2), so `mapM encode` succeeds.
  obtain ⟨progs, henc⟩ : ∃ progs, toSMTPrograms p = .ok progs :=
    mapM_succeeds (toOblPrograms p) encode
      (fun Q hQ => encode_succeeds (toOblPrograms_wf hwf hseedFF Q hQ))
  rw [henc]
  intro hunsat
  refine program_valid_of_oblProgramsValid hwf hbc hseedFF (fun Q hQ => ?_)
  -- `Q`'s emitted SMT program sits in `progs` (Stage 1 output threaded through `mapM encode`).
  obtain ⟨prog, hprogenc, hprogmem⟩ := mapM_mem henc Q hQ
  -- Stage 2: SMT-unsat of `prog` ⟹ `OblProgram.Valid Q` (WF witness is the same term).
  have h2 := oblProgram_valid_of_smtUnsat (toOblPrograms_wf hwf hseedFF Q hQ)
  rw [hprogenc] at h2
  exact h2 (hunsat prog hprogmem)

end Core.Preprocessed
