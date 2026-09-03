## A high-level summary of the simplified SMT-encoder prototype at `Language/Core/PrototypeSMTGen/`

A self-contained, machine-checked prototype of Strata's Core → SMT pipeline.
The prototype encodes Core preprocessed `Program` → my definition of SMT query as `SMTProgram`.
We have an end-to-end soundness proof for the prototype: if every emitted SMT query is unsatisfiable, the preprocessed program is valid.

This directory is structured such that the computable encoder code and the related proofs are in the same file.
This was developed before the existence of a separate monomorphization pass.
Some of the proof workarounds due to the presence of polymorphic Factory functions are no longer relevant.

An SMT query is represented by `SMTProgram` rather than the `SMTQuery` in `DL/SMT/DenoteTypedSMTQuery` (which was developed later than the prototype).
The satisfiability definitions are therefore separately defined on `SMTProgram` as well.
Nevertheless, `SMTProgram` has been adapted to use the typed SMT `Term` semantics in `DL/SMT/DenoteTyped.lean`, which was originated from a previously developed SMT `Term` semantics in the prototype.

**Supported fragment.** Base sorts `bool`, `int`, `string`, `bitvec` (no reals); integer arithmetic
(`+ - * / mod`, unary neg) and comparisons (`< <= > >=`); boolean connectives (not, and, or, implies,
iff); equality; quantifiers; free variables; user-defined function *declarations* (opaque) and
*definitions* (interpreted); deterministic and nondeterministic program variables;
global axioms and `distinct` assumptions. The prototype consumes an already-*preprocessed* Core
program (explicit variable-initialization decls, topologically ordered function decls).

---

## The pipeline at a glance

```
 Core Program (preprocessed)
      |   Stage 1 - PrototypeSMTGen/Core.lean:  toOblPrograms
      |   * prefix fold building a CoreCtx (factory + axioms + distincts)
      |   * one OblProgram per `assert` (fan-out)
      |   * per-obligation reachability pruning of unreferenced functions
      v
 List OblProgram    (OblCommand = fnDecl | fnDef | fvarDecl | varDef | assume | distinct  +  one obligation Expr)
      |   Stage 2 - PrototypeSMTGen/Construct.lean:  encode / encodeUnsat / encodeIncremental
      |   * OblCtx prefix fold (declare-before-use)
      |   * LExpr -> SMT Term via toSMTTerm  (PrototypeSMTGen/FunDef.lean)
      v
 SMTProgram = List SMTCommand   (declareFun | defineFun | assert | checkSat | checkSatAssuming)
      |
      v
{ UNSAT per query }  ==>  Program.Valid
```

The whole encoder is packaged as one function in `PrototypeSMTGen/Soundness.lean`:

```lean
def toSMTPrograms (p : Program) : Except Format (List SMTProgram) :=
  (toOblPrograms p).mapM encode
```

---

## Semantics targeted

Soundness is stated against denotational semantics on both sides:

- **Source meaning** - `simpDenote`, a `HasTypeA`-indexed denotation of Core expressions, and
  `Denotes opInterp fvarVal e b := exists h : HasTypeA [] e bool, simpDenote ... = b`.
  (The existential quantification over `HasTypeA` in `Denotes` can make the specifications confusing,
  hence the attempt at avoiding it in `CoreDepDenote.lean` so that denotation takes a well-typedness parameter at program level too.)
- **SMT term meaning** - `Term.denoteTyped ufInterp smtEnv divByZero modByZero tm smtTy htc`
  (the mainline typed SMT semantics in `Strata/DL/SMT/DenoteTyped.lean`).
- **Obligation-program validity** - `OblProgram.Valid` (`PrototypeSMTGen/ModelTransfer.lean`):
  for every definition-consistent Lambda model satisfying the assumptions and `distinct`s, the
  obligation denotes `true` (a logical-consequence statement). The denotation goes through the
  interpretation of an `OblCtx` that is constructed by stepping through an `OblProgram`.
- **SMT unsatisfiability** - `SMTProgram.Unsat prog := not (SMTCtx.checkSat (SMTProgram.ctx prog) [])`
  (`PrototypeSMTGen/ModelTransfer.lean`).
  The denotation of an `SMTProgram` also goes through the interpretation of an `SMTCtx` that is constructed by stepping through an `SMTProgram`.
- **Program well-formedness / validity** -
  `Program.WF p := Program.WFfrom p.decls CoreCtx.init` (`PrototypeSMTGen/Core.lean`), a
  declare-before-use prefix fold; `Program.Valid` (`PrototypeSMTGen/Core.lean`) via `ProcValid`
  (no reachable execution config `failed`), reusing Core's `Factory.InterpConsistent`.

---

## The end-to-end soundness theorems

**Top-level (whole encoder)** - `PrototypeSMTGen/Soundness.lean`:

```lean
theorem program_valid_of_toSMTPrograms_unsat {p : Program} (hwf : Program.WF p)
    (hbc : CoreCtx.SeedBuiltinConsistent) (hseedFF : CoreCtx.SeedFactoryFuncsWF) :
    match toSMTPrograms p with
    | .ok progs => (forall prog in progs, SMTProgram.Unsat prog) -> Program.Valid p
    | .error _  => False
```

The `.error` arm being `False` is a *totality* guarantee: a well-formed program never fails to
encode. The `.ok` arm is soundness: solver-confirmed UNSAT on every query implies program validity.
The theorem is *factory-generic*: it is parameterized over the initial Factory's builtin-consistency
(`hbc`) and well-formedness (`hseedFF`) rather than any particular factory, so it matches SMT-LIB /
the mainline convention; discharging those premises for the default `Core.Factory` happens at the
instantiation below.

**Concrete instantiation** - `StrataTest/Languages/Core/PrototypeSMTGen/EncoderTests.lean` - the same
statement for a hand-built program `progMutual` (recursive + mutually-recursive functions, an `ite`
branch, a global axiom), with the two seed premises discharged for the default factory:

```lean
theorem progMutual_valid_of_smtUnsat :
    match toSMTPrograms progMutual with
    | .ok progs => (forall prog in progs, SMTProgram.Unsat prog) -> Program.Valid progMutual
    | .error _  => False :=
  program_valid_of_toSMTPrograms_unsat progMutual_WF init_SeedBuiltinConsistent init_FactoryFuncsWF
```

Its premise `progMutual_WF : Program.WF progMutual` is fully proved (`native_decide` at the stepped
contexts + `progMutual_body_pre`); the seed premises are discharged by `init_SeedBuiltinConsistent` /
`init_FactoryFuncsWF` from `SeedFactory.lean`.

**Composition.** The generic `program_valid_of_toSMTPrograms_unsat` (`Soundness.lean`) composes
Stage 1 - the generic `program_valid_of_oblProgramsValid` (`Core.lean`) - with Stage 2
`oblProgram_valid_of_smtUnsat` (`ModelTransfer.lean`), taking the seed premises as hypotheses; totality
is lifted over the `mapM` fan-out from `encode_succeeds` (`Construct.lean`). (The primed
`program_valid_of_oblProgramsValid'` in `SeedFactory.lean`, which bakes in the default-factory
discharges, is what the `EncoderTests` specialization uses.) Stage 2 in turn rests on
`smtModel_of_lambdaModel` (`ModelTransfer.lean`) and the per-term soundness theorem `toSMTTerm_sound`
(`FunDef.lean`), which equates the cast source denotation with `Term.denoteTyped` of the encoded term.

---

## Notable design choices

- **Expression-level soundness.** Closed -> NullaryFvar -> NaryFvar -> FunDecl -> FunDef.
  Each self-contained, but developed based on the experience from previous iterations.
  Introduce the notion of consistency.

- **Program-level soundness.** The argument is factored into *context construction* (a syntactic
  correspondence in `Construct.lean`) and *model transfer* (from a Lambda model to an SMT model,
  a semantic correspondence in `ModelTransfer.lean`), meeting at one seam (`smtModel_of_lambdaModel`).

- **Variable definitions are base-typed.** While we support encoding of variables of arrow types, a
  deterministic variable declaration (i.e., a variable definition) in a Core Program must have a RHS
  that can be encoded to an SMT Term, so that RHS and hence the variable being defined cannot have arrow
  types.

- **Prefix-fold well-formedness.** `Program.WF` and `SMTProgramWF` are declare-before-use prefix
  folds, so an obligation's context is exactly the prefix of decls in scope - the shape that makes
  per-assertion reachability minimization and (future) incremental encoding line up.

- **Div/mod-by-zero model.** SMT-LIB leaves integer division/modulo by zero uninterpreted, so
  `OpInterpConsistent` carries explicit `divByZero`/`modByZero : Int -> Int` functions; the connector
  picks the model's own at-zero value (`opInterp "Int.Div" _ x 0`). `Int.SafeDiv`/`Int.SafeMod` are
  deliberately out of scope (same SMT op, but no forced agreement at zero on the Core side).

- **Reachable-only function typing.** `declWF`'s procedure clause requires only the fn-axioms of
  functions *reachable* from the proc body to be typeable in the base-type-only `HasSimpType`
  fragment - not the whole factory. The default
  factory's polymorphic `Map`/`Sequence` seed axioms quantify over type variables and cannot be
  `HasSimpType`-typed; scoping to reachable axioms is what makes `Program.WF` provable for real
  programs (and turned `progMutual_WF` sorry-free). That was a necessary workaround due to the
  presence of polymorphic functions.

- **`native_decide` for concrete facts.** Seed-factory well-formedness and per-program WF are decided
  by `native_decide` via the `Infer` decision procedure. A few decisions route through bare
  `String`/`Int`/`Bool` projections to avoid missing compiled-`DecidableEq` IR for `LExpr`.

---

## Deferred / out of scope

- Upstream pipeline (raw program -> preprocessed form via symbolic execution): not modeled.
- User-declared datatypes and the real-number type are out of scope for now.
- `CoreDepDenote.lean` is a design-target reformulation, not the load-bearing path used by
  other files.
