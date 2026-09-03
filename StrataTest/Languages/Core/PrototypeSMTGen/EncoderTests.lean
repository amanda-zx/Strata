/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

meta import all Strata.Languages.Core.PrototypeSMTGen.Soundness
meta import all Strata.Languages.Core.PrototypeSMTGen.SeedFactory
meta import all Strata.Languages.Core.PrototypeSMTGen.Infer

meta section

open Core Lambda Imperative Std Core.Construct Core.Preprocessed Core.ModelTransfer
  Core.SeedFactory Strata.SMT

/-!
# Smoke tests for the Core → SMT encoder pipeline

Small preprocessed Core programs built by hand, run through the encoder end to end, with structural
facts read off the emitted `SMTProgram` (declared UF names, `define-fun` names, assertion count) via
`SMTProgram.ctx`. Assertions target STABLE structure; a few `#eval`s render the actual emitted
commands. The input programs already satisfy the Layer-1
preprocessed-Core contract (explicit `init` per variable, topologically ordered `.func` decls).

The final section is a worked example (`progMutual`) that instantiates the headline
`program_valid_of_toSMTPrograms_unsat` at a concrete, fully well-formedness-proved program.
-/

namespace Strata.Test.PrototypeSMTGen

/-! ## Inspection helpers -/

/-- The single emitted `OblProgram`, or an error if the program did not produce exactly one
    obligation. -/
def oneObl (P : Program) : Except Format OblProgram :=
  match toOblPrograms P with
  | [Q] => .ok Q
  | qs  => .error f!"expected exactly one obligation, got {qs.length}"

/-- The declared-function (`declare-fun`) ids of `P`'s single emitted SMT program, in emission
    order. -/
def ufIds (P : Program) : Except Format (List String) := do
  let cmds ← encode (← oneObl P)
  return (SMTProgram.ctx cmds).ufs.map (·.id)

/-- The interpreted-function (`define-fun`) ids of `P`'s single emitted SMT program. -/
def fsIds (P : Program) : Except Format (List String) := do
  let cmds ← encode (← oneObl P)
  return (SMTProgram.ctx cmds).fs.map (·.id)

/-- The number of `assert`ed terms in `P`'s single emitted SMT program (assumptions + distincts +
    the trailing negated goal). -/
def numAsserts (P : Program) : Except Format Nat := do
  let cmds ← encode (← oneObl P)
  return (SMTProgram.ctx cmds).assertions.length

/-- Whether encoding `P`'s single obligation succeeds. -/
def encodes (P : Program) : Except Format Bool :=
  return (encode (← oneObl P)).isOk

/-! ## Expression builders -/

/-- A program variable `x : int`, referenced as a free variable. -/
def x : Expression.Expr := .fvar () ⟨"x", ()⟩ (some .int)
/-- A program variable `y : int`. -/
def y : Expression.Expr := .fvar () ⟨"y", ()⟩ (some .int)
/-- The `int` type as a (monomorphic) `Expression.Ty`, for `Statement.init`. -/
def intTy : Expression.Ty := .forAll [] .int

/-- `a < b` (`Int.Lt`). -/
def lt (a b : Expression.Expr) : Expression.Expr :=
  .app () (.app () (.op () "Int.Lt" (some (.arrow .int (.arrow .int .bool)))) a) b
/-- `a + b` (`Int.Add`). -/
def add (a b : Expression.Expr) : Expression.Expr :=
  .app () (.app () (.op () "Int.Add" (some (.arrow .int (.arrow .int .int)))) a) b
/-- `a == b`. -/
def eqE (a b : Expression.Expr) : Expression.Expr := .eq () a b

/-- Wrap a single structured procedure body into a whole `Program`. -/
def procProg (body : Statements) : Program :=
  { decls := [
      .proc {
        header := { name := "P", typeArgs := [], inputs := [], outputs := [] },
        spec   := { preconditions := [], postconditions := [] },
        body   := .structured body } .empty ] }

/-! ## Test 1 — trivial obligation

`assert true`. Emits just the negated goal + `check-sat`; no declarations, no assumptions. -/

def progTrivial : Program := procProg [ Statement.assert "triv" (.boolConst () true) .empty ]

/-- info: ok: true -/
#guard_msgs in #eval encodes progTrivial

#guard (toOblPrograms progTrivial).length == 1
#guard (ufIds progTrivial).toOption == some []
#guard (fsIds progTrivial).toOption == some []
#guard (numAsserts progTrivial).toOption == some 1   -- just `not true`

/-! ## Test 2 — havoc + assume + a built-in operator

`havoc x; assume 0 < x; assert 0 < x`. `x` becomes a `declare-fun`; the assume is a persistent
assertion, and `Int.Lt` stays a native SMT op (no function declared for it). -/

def progAssume : Program := procProg [
  Statement.init ⟨"x", ()⟩ intTy .nondet .empty,
  Statement.assume "pos"       (lt (.intConst () 0) x) .empty,
  Statement.assert "still_pos" (lt (.intConst () 0) x) .empty ]

#guard (ufIds progAssume).toOption == some ["x"]
#guard (fsIds progAssume).toOption == some []
#guard (numAsserts progAssume).toOption == some 2   -- assume + negated goal

/-! ## Test 3 — a deterministic binding becomes a `define-fun`

`havoc x; y := x + 1; assert x < y`. `y` is emitted as a nullary `define-fun` (its `.det` body),
`x` as a `declare-fun`. -/

def progDet : Program := procProg [
  Statement.init ⟨"x", ()⟩ intTy .nondet .empty,
  Statement.init ⟨"y", ()⟩ intTy (.det (add x (.intConst () 1))) .empty,
  Statement.assert "lt" (lt x y) .empty ]

#guard (ufIds progDet).toOption == some ["x", "y"]
#guard (fsIds progDet).toOption == some ["y"]        -- the `.det` var is a define-fun
#guard (numAsserts progDet).toOption == some 1

/-! ## Test 4 — a user-defined function is emitted (`define-fun`) and reached

`function inc(n) = n + 1`, then `havoc x; assert inc(x) == inc(x)`. Reachability pulls `inc` into
the emitted program (as a `define-fun` with its formal lifted to `$__bv0`), alongside the
`declare-fun` for `x`. -/

/-- `inc(n) = n + 1`; non-recursive, body references its formal as the free variable `n`. -/
def incFunc : Core.Function :=
  { name   := ⟨"inc", ()⟩,
    inputs := [(⟨"n", ()⟩, .int)],
    output := .int,
    body   := some (add (.fvar () ⟨"n", ()⟩ (some .int)) (.intConst () 1)) }

/-- `inc` applied to `a`. -/
def incApp (a : Expression.Expr) : Expression.Expr :=
  .app () (.op () "inc" (some (.arrow .int .int))) a

def progFunc : Program :=
  { decls := [
      .func incFunc .empty,
      .proc {
        header := { name := "P", typeArgs := [], inputs := [], outputs := [] },
        spec   := { preconditions := [], postconditions := [] },
        body   := .structured [
          Statement.init ⟨"x", ()⟩ intTy .nondet .empty,
          Statement.assert "refl" (eqE (incApp x) (incApp x)) .empty ] } .empty ] }

#guard (ufIds progFunc).toOption == some ["inc", "x"]
#guard (fsIds progFunc).toOption == some ["inc"]     -- non-recursive ⇒ define-fun
#guard (numAsserts progFunc).toOption == some 1

/-! ## Test 5 — minimality of reachability

An UNUSED function `dead` is declared but never referenced by the obligation, so it is NOT emitted;
only the referenced `inc` is. -/

def deadFunc : Core.Function :=
  { name   := ⟨"dead", ()⟩,
    inputs := [(⟨"n", ()⟩, .int)],
    output := .int,
    body   := some (.fvar () ⟨"n", ()⟩ (some .int)) }

def progReach : Program :=
  { decls := [
      .func incFunc .empty,
      .func deadFunc .empty,
      .proc {
        header := { name := "P", typeArgs := [], inputs := [], outputs := [] },
        spec   := { preconditions := [], postconditions := [] },
        body   := .structured [
          Statement.init ⟨"x", ()⟩ intTy .nondet .empty,
          Statement.assert "refl" (eqE (incApp x) (incApp x)) .empty ] } .empty ] }

#guard (fsIds progReach).toOption == some ["inc"]     -- `dead` pruned by reachability
#guard ((ufIds progReach).toOption.map (·.contains "dead")) == some false

/-! ## Test 6 — a global axiom becomes an extra assumption

`axiom pos_ax : 0 < x`, then `havoc x; assert 0 < x`. The axiom is emitted as an `assert`
(assumption), so there are two asserted terms: the axiom and the negated goal. -/

def progAxiom : Program :=
  { decls := [
      .ax { name := "pos_ax", e := lt (.intConst () 0) x } .empty,
      .proc {
        header := { name := "P", typeArgs := [], inputs := [], outputs := [] },
        spec   := { preconditions := [], postconditions := [] },
        body   := .structured [
          Statement.init ⟨"x", ()⟩ intTy .nondet .empty,
          Statement.assert "pos" (lt (.intConst () 0) x) .empty ] } .empty ] }

#guard (ufIds progAxiom).toOption == some ["x"]
#guard (numAsserts progAxiom).toOption == some 2      -- axiom + negated goal

/-! ## Test 7 — multiple asserts fan out into multiple obligations

Two `assert`s in one body ⇒ two emitted `OblProgram`s (one per obligation). -/

def progMulti : Program := procProg [
  Statement.init ⟨"x", ()⟩ intTy .nondet .empty,
  Statement.assert "a1" (lt (.intConst () 0) x) .empty,
  Statement.assert "a2" (eqE x x) .empty ]

#guard (toOblPrograms progMulti).length == 2

/-! ## Test 8 — the three encoder shapes agree on the shared block

For `progAssume`: `encode` (validity, negated goal) and `encodeUnsat` (goal as-is) each append one
persistent assert + one `check-sat`; `encodeIncremental` pushes the block once and issues two
`check-sat-assuming`s. -/

/-- Number of `check-sat` / `check-sat-assuming` queries in the encoded program. -/
def numChecks (enc : OblProgram → Except Format SMTProgram) (P : Program) : Except Format Nat := do
  let cmds ← enc (← oneObl P)
  return (cmds.filter SMTCommand.isCheck).length

#guard (numChecks encode            progAssume).toOption == some 1
#guard (numChecks encodeUnsat       progAssume).toOption == some 1
#guard (numChecks encodeIncremental progAssume).toOption == some 2

-- `encodeIncremental` keeps the goal literals TRANSIENT: the persistent assertion set is just the
-- shared block (the two assumptions here), with no trailing goal assert.
/-- info: ok: 1 -/
#guard_msgs in
#eval do
  let cmds ← encodeIncremental (← oneObl progAssume)
  return (SMTProgram.ctx cmds).assertions.length   -- only the `assume`, no goal

#eval (ufIds progFunc, fsIds progFunc, numAsserts progFunc)

/-! ## SMT-LIB renderer for the emitted `SMTProgram`

A compact renderer so the `#eval`s show the actual emitted script. It
covers only the term/op shapes this encoder produces, reusing the SMT layer's `Op.mkName` /
`TermPrimType.mkName` for operator and sort names. -/

/-- Render a `TermType` as an SMT-LIB sort. -/
partial def sortStr : TermType → String
  | .prim p     => p.mkName
  | .option t   => s!"(Option {sortStr t})"
  | .constr id args =>
      if args.isEmpty then id else s!"({id} {" ".intercalate (args.map sortStr)})"

/-- Render a `Term` as an SMT-LIB s-expression. -/
partial def termStr : Term → String
  | .prim (.bool b) => toString b
  | .prim (.int i)  => toString i
  | .prim p         => p.mkName
  | .var v          => v.id
  | .none _         => "none"
  | .some t         => s!"(some {termStr t})"
  | .app op args _  =>
      if args.isEmpty then op.mkName
      else s!"({op.mkName} {" ".intercalate (args.map termStr)})"
  | .quant k args _ body =>
      let q := match k with | .all => "forall" | .exist => "exists"
      let bs := " ".intercalate (args.map (fun v => s!"({v.id} {sortStr v.ty})"))
      s!"({q} ({bs}) {termStr body})"

/-- Render one emitted `SMTCommand` as an SMT-LIB line. -/
def cmdStr : SMTCommand → String
  | .declareFun u =>
      s!"(declare-fun {u.id} ({" ".intercalate (u.args.map sortStr)}) {sortStr u.out})"
  | .defineFun f =>
      let ps := " ".intercalate (f.args.map (fun v => s!"({v.id} {sortStr v.ty})"))
      s!"(define-fun {f.id} ({ps}) {sortStr f.out} {termStr f.body})"
  | .assert t              => s!"(assert {termStr t})"
  | .checkSat              => "(check-sat)"
  | .checkSatAssuming lits => s!"(check-sat-assuming ({" ".intercalate (lits.map termStr)}))"

/-- Render a whole `SMTProgram`, one command per line. -/
def progStr (P : SMTProgram) : String := "\n".intercalate (P.map cmdStr)

/-- A "kitchen-sink" preprocessed program that exercises every emission path:
      • `inc` — a NON-recursive function ⇒ `define-fun`;
      • `absF` — a RECURSIVE function ⇒ bodyless `declare-fun` + its axiom as an `assert`;
      • a global `axiom x_nonneg`;
      • `havoc x` ⇒ `declare-fun`, and `y := inc x` (`.det`) ⇒ nullary `define-fun`;
      • two `assert`s ⇒ TWO emitted obligations. Note the per-obligation minimality:
        `absF` is unreachable from the first obligation, so it is absent there. -/
def incFunc' : Core.Function :=
  { name := ⟨"inc", ()⟩, inputs := [(⟨"n", ()⟩, .int)], output := .int,
    body := some (add (.fvar () ⟨"n", ()⟩ (some .int)) (.intConst () 1)) }

def absFunc : Core.Function :=
  { name := ⟨"absF", ()⟩, isRecursive := true,
    inputs := [(⟨"n", ()⟩, .int)], output := .int,
    axioms := [ lt (.intConst () (-1)) (.app () (.op () "absF" (some (.arrow .int .int)))
                                                (.fvar () ⟨"n", ()⟩ (some .int))) ] }

def incApp' (a : Expression.Expr) : Expression.Expr :=
  .app () (.op () "inc" (some (.arrow .int .int))) a
def absApp (a : Expression.Expr) : Expression.Expr :=
  .app () (.op () "absF" (some (.arrow .int .int))) a

def progFull : Program :=
  { decls := [
      .func incFunc' .empty,
      .func absFunc .empty,
      .ax { name := "x_nonneg", e := lt (.intConst () (-1)) x } .empty,
      .proc {
        header := { name := "P", typeArgs := [], inputs := [], outputs := [] },
        spec   := { preconditions := [], postconditions := [] },
        body   := .structured [
          Statement.init ⟨"x", ()⟩ intTy .nondet .empty,
          Statement.init ⟨"y", ()⟩ intTy (.det (incApp' x)) .empty,
          Statement.assert "a1_x_lt_y"  (lt x y) .empty,
          Statement.assert "a2_absF_pos" (lt (.intConst () (-1)) (absApp x)) .empty ] } .empty ] }

-- Print every emitted SMT program for `progFull` end to end.
#eval show IO Unit from do
  let obls := toOblPrograms progFull
  IO.println s!"# {obls.length} obligation(s) emitted"
  for (Q, i) in obls.zipIdx do
    IO.println s!"\n;; ── obligation {i} ──"
    match encode Q with
    | .ok cmds => IO.println (progStr cmds)
    | .error e => IO.println s!"error: {e}"

/-! ## SMT-LIB renderer for the intermediate `OblProgram` (Stage 1 output)

Parallels `progStr` for `SMTProgram`. `OblProgram`/`OblCommand` carry Lambda `Expr`s (not yet SMT
`Term`s), so this reuses `reprStr` on the expressions — compact enough to eyeball the per-obligation
command list before it is encoded to SMT. -/

/-- Render one `OblCommand` (the Lambda-side dual of an `SMTCommand`) as a line. -/
def oblCmdStr : Core.Construct.OblCommand → String
  | .fnDecl name sig => s!"(declare-fn {name} : {sig})"
  | .fnDef d         => s!"(define-fn {d.name} ({" ".intercalate (d.argTys.map toString)}) {d.retTy} := {repr d.body})"
  | .fvarDecl name τ => s!"(declare-var {name} : {τ})"
  | .varDef v        => s!"(define-var {v.name} : {v.ty} := {repr v.body})"
  | .assume e        => s!"(assume {repr e})"
  | .distinct es     => s!"(distinct {" ".intercalate (es.map (fun e => toString (repr e)))})"

/-- Render a whole `OblProgram`: its command list, then the (un-negated) goal. -/
def oblProgStr (Q : Core.Construct.OblProgram) : String :=
  "\n".intercalate (Q.cmds.map oblCmdStr) ++ s!"\n(goal {repr Q.obligation})"

/-! ## Worked example — mutually-recursive functions, an `if` branch, and a defined function

Models this source program (pseudocode):

    .func f (Int) : Int with axiom {forall x, f(x) = g(x+2)}
    .ax (10 = 10)
    .func g (Int) : Int with axiom {forall x, g(x) = f(x+1)}
    .func h (Int) : Int { x }             -- non-recursive, has a body
    .proc() {
      .ite {                         -- nondeterministic branch
        .assume (f(0) = 1)
        .assert (g(0) = 2)
      } else {
        .assume (h(0) = 1)
        .assert (g(0) = 0)
      }
      .assert (h(0) = 0)
    }

How each feature lands in the pipeline:
  • `f` and `g` are MUTUALLY RECURSIVE. Neither can carry a `body` (a recursive function with a body
    is rejected by the preprocessed-Core `declWF`); each gives its meaning through a
    universally-quantified `axiom` instead. Emission is two-phase — ALL `declare-fun`s first, then
    ALL axiom `assert`s — so `f`'s axiom may reference `g` (and vice versa) regardless of order.
    Reachability follows axiom references, so seeding either pulls in BOTH.
  • The `.ite` uses a `.nondet` guard: each branch is explored self-contained from the pre-branch
    prefix, and the branch's leading `.assume` supplies its path condition. A trailing `.assert`
    after the branch is a third, independent obligation.
  • `h` IS declared via `.func` (after `g`), non-recursive and WITH a body (`h(x) = x`), so it
    becomes a `define-fun` — its formal lifted fvar→bvar to `$__bv0`. It is pulled in only for the
    obligations that reference it (the else-branch and the tail), so it is ABSENT from obligation 0
    by per-obligation reachability minimality.

THREE `assert`s ⇒ THREE emitted obligations:
  0. `g(0) = 2`  under path `f(0) = 1`   (then-branch)
  1. `g(0) = 0`  under path `h(0) = 1`   (else-branch)
  2. `h(0) = 0`  under the empty path    (after the branch) -/

/-- `f` applied to `a` (`f : Int → Int`, an op head resolved through the factory). -/
def fApp (a : Expression.Expr) : Expression.Expr :=
  .app () (.op () "f" (some (.arrow .int .int))) a
/-- `g` applied to `a`. -/
def gApp (a : Expression.Expr) : Expression.Expr :=
  .app () (.op () "g" (some (.arrow .int .int))) a
/-- `h` applied to `a`. `h` IS declared (below), with a body, so it becomes a `define-fun`. -/
def hApp (a : Expression.Expr) : Expression.Expr :=
  .app () (.op () "h" (some (.arrow .int .int))) a

/-- `forall x : int, f(x) == g(x + 2)`, closed over the bound variable `x` (de Bruijn `%0`). Uses
    the natural `LExpr.all` (whose `noTrigger = .bvar 0`), admitted by `HasSimpType.quant`'s relaxed
    arbitrary-trigger rule. -/
def fAxiom : Expression.Expr :=
  .all () "x" (some .int)
    (eqE (fApp (.bvar () 0)) (gApp (add (.bvar () 0) (.intConst () 2))))

/-- `forall x : int, g(x) == f(x + 1)`, closed over the bound variable `x` (natural `LExpr.all`
    trigger, see `fAxiom`). -/
def gAxiom : Expression.Expr :=
  .all () "x" (some .int)
    (eqE (gApp (.bvar () 0)) (fApp (add (.bvar () 0) (.intConst () 1))))

/-- `f : Int → Int`, recursive, meaning given by `fAxiom` (no body). -/
def fFunc : Core.Function :=
  { name := ⟨"f", ()⟩, isRecursive := true,
    inputs := [(⟨"x", ()⟩, .int)], output := .int,
    axioms := [ fAxiom ] }

/-- `g : Int → Int`, recursive, meaning given by `gAxiom` (no body). -/
def gFunc : Core.Function :=
  { name := ⟨"g", ()⟩, isRecursive := true,
    inputs := [(⟨"x", ()⟩, .int)], output := .int,
    axioms := [ gAxiom ] }

/-- `h(x) = x` — a NON-recursive function WITH a body, so it becomes a `define-fun` (its formal `x`
    lifted fvar→bvar as `$__bv0`). -/
def hFunc : Core.Function :=
  { name := ⟨"h", ()⟩,
    inputs := [(⟨"x", ()⟩, .int)], output := .int,
    body := some (.fvar () ⟨"x", ()⟩ (some .int)) }

def progMutual : Program :=
  { decls := [
      .func fFunc .empty,
      .ax { name := "eq10", e := eqE (.intConst () 10) (.intConst () 10) } .empty,
      .func gFunc .empty,
      .func hFunc .empty,
      .proc {
        header := { name := "P", typeArgs := [], inputs := [], outputs := [] },
        spec   := { preconditions := [], postconditions := [] },
        body   := .structured [
          Stmt.ite .nondet
            [ Statement.assume "then_g" (eqE (fApp (.intConst () 0)) (.intConst () 1)) .empty,
              Statement.assert "a_then"  (eqE (gApp (.intConst () 0)) (.intConst () 2)) .empty ]
            [ Statement.assume "else_h" (eqE (hApp (.intConst () 0)) (.intConst () 1)) .empty,
              Statement.assert "a_else"  (eqE (gApp (.intConst () 0)) (.intConst () 0)) .empty ]
            .empty,
          Statement.assert "a_tail" (eqE (hApp (.intConst () 0)) (.intConst () 0)) .empty ] } .empty ] }

-- Three asserts (two in the branches, one after) ⇒ three obligations.
#guard (toOblPrograms progMutual).length == 3

-- Print the INTERMEDIATE `OblProgram`s (Stage 1), then their SMT programs (Stage 2).
#eval show IO Unit from do
  let obls := toOblPrograms progMutual
  IO.println s!"# {obls.length} obligation(s) emitted\n"
  IO.println "════════════════════ OblPrograms (Stage 1) ════════════════════"
  for (Q, i) in obls.zipIdx do
    IO.println s!"\n;; ── OblProgram {i} ──"
    IO.println (oblProgStr Q)

  IO.println "\n════════════════════ SMTPrograms (Stage 2) ════════════════════"
  match toSMTPrograms progMutual with
  | .ok progs =>
      for (cmds, i) in progs.zipIdx do
        IO.println s!"\n;; ── SMTProgram {i} ──"
        IO.println (progStr cmds)
  | .error e => IO.println s!"error: {e}"

set_option maxHeartbeats 4000000 in
/-- The proc-body `Preprocessed` derivation, built by constructors (typing/freshness leaves via
    `native_decide` at the 4-step stepped `Ψ`). -/
theorem progMutual_body_pre :
    let cΨ := ((((CoreCtx.init.step (Decl.func fFunc .empty)).step
        (Decl.ax { name := "eq10", e := eqE (.intConst () 10) (.intConst () 10) } .empty)).step
      (Decl.func gFunc .empty)).step (Decl.func hFunc .empty)).Ψ
    Statements.Preprocessed cΨ [] [
      Stmt.ite .nondet
        [ Statement.assume "then_g" (eqE (fApp (.intConst () 0)) (.intConst () 1)) .empty,
          Statement.assert "a_then"  (eqE (gApp (.intConst () 0)) (.intConst () 2)) .empty ]
        [ Statement.assume "else_h" (eqE (hApp (.intConst () 0)) (.intConst () 1)) .empty,
          Statement.assert "a_else"  (eqE (gApp (.intConst () 0)) (.intConst () 0)) .empty ]
        .empty,
      Statement.assert "a_tail" (eqE (hApp (.intConst () 0)) (.intConst () 0)) .empty ] := by
  intro cΨ
  apply Statements.Preprocessed.ite
  · apply Statements.Preprocessed.assume _ _ _ _ _ (by native_decide)
    apply Statements.Preprocessed.assert _ _ _ _ _ (by native_decide)
    apply Statements.Preprocessed.nil
  · apply Statements.Preprocessed.assume _ _ _ _ _ (by native_decide)
    apply Statements.Preprocessed.assert _ _ _ _ _ (by native_decide)
    apply Statements.Preprocessed.nil
  · apply Statements.Preprocessed.assert _ _ _ _ _ (by native_decide)
    apply Statements.Preprocessed.nil

set_option maxHeartbeats 4000000 in
/-- **`progMutual` is well-formed**, thanks to the reachable-only `declWF` proc clause.
    The fn-axiom typing obligation is scoped to functions REACHABLE from the proc body
    (`reachableFuncs c.F (procSeeds ss) = {f, g, h}`), whose axioms DO type; the polymorphic
    Map/Sequence seed axioms are unreachable and never required. Every leaf: `native_decide`
    (typing/reachability at the stepped `Ψ`) or the reserved-name head lemma; body via
    `progMutual_body_pre`. -/
theorem progMutual_WF : Program.WF progMutual := by
  unfold Program.WF progMutual
  simp only [Program.WFfrom, CoreCtx.declWF]
  refine ⟨?df, ?dax, ?dg, ?dh, ⟨_, rfl, progMutual_body_pre, ?dfnax⟩, trivial⟩
  -- `.func fFunc` — recursive, bodyless: reserved-name via the head lemma, rest by native_decide.
  case df =>
    refine ⟨by native_decide, Core.SeedFactory.ne_bv_of_head (by native_decide), ?_⟩
    native_decide
  -- `.ax eq10` — bool-typed at init.Ψ.
  case dax => native_decide
  -- `.func gFunc` — like fFunc.
  case dg =>
    refine ⟨by native_decide, Core.SeedFactory.ne_bv_of_head (by native_decide), ?_⟩
    native_decide
  -- `.func hFunc` — non-recursive WITH a body; body typing at the stepped Ψ by native_decide.
  case dh =>
    refine ⟨by native_decide, Core.SeedFactory.ne_bv_of_head (by native_decide), ?_⟩
    native_decide
  -- REACHABLE fn-axiom typing: `reachableFuncs` from the body's `{f,g,h}` refs; their axioms type.
  case dfnax => native_decide

/-- **End-to-end soundness of `progMutual`'s SMT encoding.** If every emitted SMT program is
    unsatisfiable, `progMutual` is valid — the headline `program_valid_of_toSMTPrograms_unsat`
    instantiated at `progMutual_WF`, with its seed premises discharged for the default `Core.Factory`
    via `SeedFactory`. -/
theorem progMutual_valid_of_smtUnsat :
    match toSMTPrograms progMutual with
    | .ok progs => (∀ prog ∈ progs, SMTProgram.Unsat prog) → Program.Valid progMutual
    | .error _  => False :=
  program_valid_of_toSMTPrograms_unsat progMutual_WF
    init_SeedBuiltinConsistent init_FactoryFuncsWF

end Strata.Test.PrototypeSMTGen
