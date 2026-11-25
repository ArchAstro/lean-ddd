import Lean
import DDD.Aggregate
import DDD.CommandPath

/-!
# Visualising a domain

Any domain built with `DDD` can be drawn and played back in a generated site. A domain
says only *which* declarations matter (`Viz.Spec`): its aggregates, the processes that
join them, the theorems worth showing. Everything else is read from the compiled
environment:

1. every type reachable from an aggregate's state, commands and events, with its fields
   or constructors, their Lean types and their docstrings;
2. how types refer to each other (`field`, `arg`, `extends` edges, with `one`, `optional`
   or `many`);
3. which aggregates each process and theorem is about, from the constants it mentions;
4. the signature and docstring of every process and theorem.

Scenarios are played, not drawn: a `Beat` runs a command (or a process) against a world
and records what happened; `play` runs a list of beats and snapshots every aggregate
after each one. `emit` writes the domain's page into a static site (see *The site*).

Nothing here knows about any particular domain.
-/

namespace DDD.Viz
open Lean Meta Elab Command

/-! ## What a domain says about itself -/

structure AggSpec where
  /-- Short id used by the viewer and by scenarios (`"account"`). -/
  id : String
  /-- The state type. -/
  state : Name
  cmd : Name
  evt : Name
  err : Option Name := none
  /-- Theorems that state what is always true of this aggregate (its `Sound` proofs). -/
  invariants : List Name := []

structure ProcSpec where
  id : String
  decl : Name
  /-- Aggregates it touches. Empty: worked out from the constants it mentions. -/
  touches : List String := []

/-- A bounded context: a part of the domain with its own language, drawn as a frame
around its aggregates. -/
structure ContextSpec where
  id : String
  title : String
  doc : String := ""
  /-- Ids of the aggregates inside it. -/
  aggregates : List String

structure Spec where
  id : String
  title : String
  doc : String := ""
  /-- Names under this prefix are the domain's own; types outside it are not crawled. -/
  ns : Name
  aggregates : List AggSpec
  processes : List ProcSpec := []
  theorems : List Name := []
  /-- Bounded contexts. An aggregate in none is drawn on its own. -/
  contexts : List ContextSpec := []
  /-- Make a missing doc comment an error, not a warning. Doc comments are the domain's
  glossary: the viewer shows them for every type, field, command, event and reason. -/
  requireDocs : Bool := false
  /-- More types to include, beyond those reachable from the aggregates. -/
  extraTypes : List Name := []
  /-- Override a type's kind (`entity`, `value`, `identifier`, ...). -/
  kinds : List (Name × String) := []

/-! ## Scenarios -/

/-- A policy finding, in words. -/
def Finding.say (f : Finding) : String :=
  match f.kind with
  | .violation => s!"{f.rule}: broken, and recorded as a warning"
  | .overridden a r => s!"{f.rule}: overridden by the {match a with | .administrator => "administrator" | .counsel => "counsel"}{if r.isEmpty then "" else s!" ({r})"}"
  | .missingFact x => s!"{f.rule}: could not be checked, {x} is unknown"

/-- The constructor a value was built with, from its `Repr`: `Ns.Evt.deposited 120` gives
`deposited`. -/
def ctorName (s : String) : String :=
  let cs := (s.toList.dropWhile (fun c => c.isWhitespace || c == '(')).takeWhile
    (fun c => !c.isWhitespace && c != '(' && c != ')')
  (String.ofList cs |>.splitOn ".").getLast?.getD ""

/-- What a step did, in the terms a story's `expect:` names. -/
inductive Result where
  /-- Accepted: the constructors of the events recorded, in order, and the rules that warned. -/
  | accepted (events : List String) (warned : List String)
  /-- Built on an out-of-date version of the aggregate. -/
  | stale
  /-- Policy stopped it: rules that block until overridden, facts nobody has set. -/
  | blocked (rules : List String) (facts : List String)
  /-- The aggregate refused it: the constructor of its reason, or `""` if it gives none. -/
  | refused (reason : String)
  deriving Repr, BEq, Inhabited

private def names (xs : List String) : String := ", ".intercalate xs

def Result.say : Result → String
  | .accepted [] [] => "accepted, recording nothing"
  | .accepted es ws => s!"accepted{if es.isEmpty then ", recording nothing" else s!", recording {names es}"}{if ws.isEmpty then "" else s!", with warnings from {names ws}"}"
  | .stale => "rejected as stale"
  | .blocked rs [] => s!"blocked by {names rs}"
  | .blocked [] fs => s!"held until {names fs} is set"
  | .blocked rs fs => s!"blocked by {names rs} and held until {names fs} is set"
  | .refused "" => "refused"
  | .refused r => s!"refused: {r}"

structure Outcome where
  ok : Bool
  error : String := ""
  events : List String := []
  /-- What policy noted about an accepted command: rules it broke that only warn, overrides,
  facts it could not check. -/
  findings : List String := []
  /-- The rules behind `findings`. -/
  warned : List String := []
  /-- What happened, for checking against what the story says. -/
  result : Result := if ok then .accepted (events.map ctorName) warned else .refused ""

/-- What a story says a step does. A step must say it, and the build fails when the step
does something else. -/
inductive Expect where
  /-- Accepted, recording exactly these events (constructor names, in order) and warned by
  exactly these rules. -/
  | accepted (events : List String) (warned : List String)
  /-- Refused by the aggregate, for this reason (constructor name). `none` only where the
  step gives no reason, such as a process that wrote nothing. -/
  | refused (reason : Option String)
  /-- Stopped by these policy rules. -/
  | blocked (rules : List String)
  /-- Held by policy until these facts are set. -/
  | needs (facts : List String)
  | stale
  deriving Repr, BEq, Inhabited

def Expect.matches : Expect → Result → Bool
  | .accepted es ws, .accepted es' ws' => es == es' && ws == ws'
  | .refused none, .refused r => r == ""
  | .refused (some r), .refused r' => r == r'
  | .blocked rs, .blocked rs' [] => rs == rs'
  | .needs fs, .blocked [] fs' => fs == fs'
  | .stale, .stale => true
  | _, _ => false

def Expect.say : Expect → String
  | .accepted es ws => Result.say (.accepted es ws)
  | .refused none => "refused"
  | .refused (some r) => s!"refused: {r}"
  | .blocked rs => s!"blocked by {names rs}"
  | .needs fs => s!"held until {names fs} is set"
  | .stale => "rejected as stale"

/-- How to write what actually happened as an `expect:` line, for the error message. -/
def Result.expectLine : Result → String
  | .accepted es ws =>
    let q (xs : List String) := ", ".intercalate (xs.map (s!"\"{·}\""))
    s!"expect: accepted{if es.isEmpty then "" else " " ++ q es}{if ws.isEmpty then "" else " warns " ++ q ws}"
  | .stale => "expect: stale"
  | .blocked rs [] => s!"expect: blocked {", ".intercalate (rs.map (s!"\"{·}\""))}"
  | .blocked _ fs => s!"expect: needs {", ".intercalate (fs.map (s!"\"{·}\""))}"
  | .refused "" => "expect: refused"
  | .refused r => s!"expect: refused \"{r}\""

/-- What a person reads at one step of a story: what is happening, in words, and notes
pinned to particular objects. -/
structure Telling where
  /-- What is happening and why it matters, for someone new to the domain. -/
  say : String := ""
  /-- Notes pinned to objects: an aggregate id (`"order"`), or an object inside one, as
  `aggregate/field#id` (`"order/items#3"`) or `aggregate/field[i]` when it has no id. -/
  notes : List (String × String) := []
  /-- Objects to bring onto the page at this step though the step does not change them:
  the people involved, say. Same keys as `notes`. -/
  reveal : List String := []
  /-- What the step does, from `expect:`. A story step must have exactly one. -/
  expect : List Expect := []

/-- One step of a scenario: who does what to which aggregates, and how to run it. -/
structure Beat (W : Type) where
  /-- What is told at this step. The `story` syntax fills it in. -/
  telling : Telling := {}
  note : String
  actor : String := ""
  /-- The process it goes through, if any (a `ProcSpec` id). -/
  via : Option String := none
  targets : List String
  command : String
  run : W → W × Outcome
  /-- The world after each event of the step but the last, when it records several, so the
  viewer can show which event changed what. -/
  stages : W → List W := fun _ => []

structure Scenario where
  id : String
  title : String
  doc : String := ""
  frames : Json
  /-- What is wrong with the scenario: a step that does something other than what the story
  says, a note about an object that is not there. `story` fails the build on any. -/
  problems : List String := []

private def tellingJson (t : Telling) : List (String × Json) :=
  [("say", toJson t.say),
   ("notes", Json.arr (t.notes.map fun (at_, text) => Json.mkObj [("at", toJson at_), ("text", toJson text)]).toArray),
   ("reveal", toJson t.reveal), ("expect", toJson (t.expect.map (·.say)))]

/-- The events appended to a log, as text. -/
def newEvents {E : Type} [Repr E] (before after : List E) : List String :=
  (after.drop before.length).map (fun e => reprStr e)

/-- A rejection, as what a story's `expect:` names. A process that runs commands itself can
use it to say why it was refused. -/
def _root_.DDD.Rejection.result {X : Type} [Repr X] : Rejection X → Result
  | .stale _ _ => .stale
  | .policy v => .blocked
      (v.dispositions.filterMap fun | .blocked r _ => some r | _ => none)
      (v.dispositions.filterMap fun | .needsFact _ f => some f | _ => none)
  | .impossible x => .refused (ctorName (reprStr x))

/-- A beat that sends one command to one aggregate through the command path. Pass the
command, event and rejection types by name (`(C := Cmd) (E := Evt) (X := Why)`) so their
`Repr` instances are found. -/
def submitBeat {W Ctx S C E X : Type} [Repr C] [Repr E] [Repr X]
    (agg : Aggregate S C E X) (target : String) (note : String) (actor : String)
    (rules : W → List (Rule Ctx S C)) (ctx : W → Ctx)
    (get : W → List E) (set : W → List E → W) (c : C) : Beat W where
  note := note
  actor := actor
  targets := [target]
  command := reprStr c
  run w :=
    let log := get w
    match submit agg (rules w) .enforcing [] (ctx w) log log.length c with
    | .ok (log', fs) => (set w log',
        { ok := true, events := newEvents log log', findings := fs.map Finding.say,
          warned := (fs.map (·.rule)).eraseDups })
    | .error why => (w, { ok := false, error := reprStr why, result := why.result })
  stages w :=
    let log := get w
    match submit agg (rules w) .enforcing [] (ctx w) log log.length c with
    | .ok (log', _) =>
      let new := log'.drop log.length
      (List.range (new.length - 1)).map fun i => set w (log ++ new.take (i + 1))
    | .error _ => []

/-- How the viewer writes an id in an object's key: a string or number as is, a one-field
identifier (`{"raw": "ana"}`) as its value. -/
def idText : Json → String
  | .str s => s
  | .num n => toString n
  | .obj kvs => match kvs.toList with
    | [(k, .str s)] => if k == "raw" || k == "code" then s else (Json.obj kvs).compress
    | [(k, .num n)] => if k == "raw" || k == "code" then toString n else (Json.obj kvs).compress
    | _ => (Json.obj kvs).compress
  | j => j.compress

/-- Whether a snapshot holds the object a note or `show:` names: an aggregate id, then
`/field`, `/field#id` or `/field[i]` steps into it, as the viewer keys objects. -/
def objectAt (state : Json) (key : String) : Bool :=
  match key.splitOn "/" with
  | [] => false
  | agg :: path =>
    match state.getObjVal? agg with
    | .error _ => false
    | .ok a =>
      if a.getObjValD "exists" == .bool false then false else
      let step (cur : Option Json) (seg : String) : Option Json := do
        let c ← cur
        match seg.splitOn "#" with
        | [f, id] =>
          let .arr xs := c.getObjValD f | none
          xs.find? (fun x => idText (x.getObjValD "id") == id)
        | _ =>
          match seg.splitOn "[" with
          | [f, ix] =>
            let .arr xs := c.getObjValD f | none
            let n ← (ix.dropEnd 1).toString.toNat?
            xs[n]?
          | _ => match c.getObjValD seg with
            | .null => none
            | v => some v
      (path.foldl step (some (a.getObjValD "raw"))).isSome

/-- Run beats in order. Frame 0 is the starting state; each later frame is one beat, with
every aggregate's snapshot after it.

A snapshot is an object per aggregate id:
- `raw`: the state as `ToJson`; the viewer draws it as objects, using the model's types;
- `exists` (optional, default true): false until the aggregate has been created, so the
  viewer does not draw its empty initial state as if it were a real object;
- `view` (optional): readable values for the side panel.

An entry named `@world` is not an aggregate: it is an object of facts about the world the
scenario runs in, such as today's date, and the viewer shows it on every step. -/
def playChecked {W : Type} (snap : W → List (String × Json)) (w₀ : W) (beats : List (Beat W))
    (opening : Telling := {}) (checked : Bool := false) : Json × List String :=
  let frame (w : W) (b : Option (Beat W)) (o : Outcome) : Json :=
    let stages := ((b.map (·.stages w)).getD []).map fun w => Json.mkObj (snap w)
    Json.mkObj <| tellingJson ((b.map (·.telling)).getD opening) ++ [
      ("note", toJson ((b.map (·.note)).getD "The starting state")),
      ("actor", toJson ((b.map (·.actor)).getD "")),
      ("via", match b.bind (·.via) with | some v => toJson v | none => Json.null),
      ("targets", toJson ((b.map (·.targets)).getD [])),
      ("command", toJson ((b.map (·.command)).getD "")),
      ("ok", toJson o.ok), ("error", toJson o.error), ("events", toJson o.events),
      ("findings", toJson o.findings), ("result", toJson o.result.say),
      ("start", toJson b.isNone),
      ("state", Json.mkObj (snap w))] ++ (if stages.isEmpty then [] else [("stages", Json.arr stages.toArray)])
  let keyProblems (where_ : String) (t : Telling) (w : W) : List String :=
    let st := Json.mkObj (snap w)
    (t.notes.map (·.1) ++ t.reveal).filterMap fun k =>
      if objectAt st k then none
      else some s!"{where_}: there is no object \"{k}\" on the page to note or show"
  let (_, frames, problems, _) := beats.foldl (fun (w, acc, ps, i) b =>
    let (w', o) := b.run w
    let here := s!"step {i} (\"{b.note}\")"
    let expectPs := if !checked then [] else match b.telling.expect with
      | [] => [s!"{here}: say what it does with `expect:`; it was {o.result.say}. Write: {o.result.expectLine}"]
      | [e] => if e.matches o.result then []
        else [s!"{here}: the story says it is {e.say}, but it was {o.result.say}. If the story is wrong, write: {o.result.expectLine}"]
      | _ => [s!"{here}: has more than one `expect:`"]
    let sayPs := if checked && b.telling.say.isEmpty then [s!"{here}: has no `says:`; tell a reader what is happening"] else []
    (w', acc ++ [frame w' (some b) o], ps ++ expectPs ++ sayPs ++ keyProblems here b.telling w', i + 1))
    (w₀, [frame w₀ none { ok := true }], keyProblems "the opening" opening w₀ ++
      (if opening.expect.isEmpty then [] else ["the opening: `expect:` belongs to a step, not the opening"]), 1)
  (Json.arr frames.toArray, problems)

def play {W : Type} (snap : W → List (String × Json)) (w₀ : W) (beats : List (Beat W))
    (opening : Telling := {}) : Json :=
  (playChecked snap w₀ beats opening).1

/-! ## Stories: scenarios written to be read

A `story` is a scenario with words. It starts from a blank page; each step runs one beat and
says, for a person new to the domain, what is happening. The viewer brings objects onto the
page as the story reaches them.

```lean
story limits "limits" "Deposits, a limit, an overdraft"
  about: "The daily limit is $100; the balance never goes below zero."
  from ([] : World) using snap
  says: "A blank page: no account exists until the first deposit opens one."
  | beat "Open the account with $120" (.deposit 120)
    expect: accepted "deposited"
    says: "The customer deposits $120. That first deposit brings the account into being."
    note: "account" "The balance is everything deposited minus everything withdrawn."
  | beat "Take out $200" (.withdraw 200)
    expect: blocked "withdrawal-limit"
    says: "$200 is over the daily limit, so policy stops it."
```

(`viz/domains/Account.lean` is the whole example.)

- `expect:` what the step does. Every step has exactly one, and the build fails when the
  domain does something else:
  - `accepted "event", …` recorded exactly these events (constructor names, in order; none:
    it recorded nothing), optionally `warns "rule", …` for the policy rules that warned;
  - `refused "reason"` the aggregate refused it, with this reason (constructor name);
    `refused` alone only for a step that gives no reason;
  - `blocked "rule", …` policy stopped it; `needs "fact", …` policy is waiting on a fact;
  - `stale` it was built on an out-of-date version.
- `says:` what is happening, in plain words. Every step needs one; several join into paragraphs.
- `note: "key" "text"` a note pinned to one object. A key is an aggregate id, or an object
  inside one: `aggregate/field#id`, or `aggregate/field[i]` for one with no id.
- `show: "key", …` brings objects onto the page that the step does not change.
- Lines before the first `|` describe the opening page.

A note or `show:` must name an object that is on the page after its step, or the build fails.
The error says what the step really did, and the `expect:` line that would say so: a story
can be wrong, but it cannot be wrong quietly. `Examples/Stories.lean` shows each mistake and
the message it gives.

It defines `limits : Scenario`, for `emit`. -/

/-- One line of a story step. -/
inductive StoryLine where
  | says (text : String)
  | note (at_ text : String)
  | show (keys : List String)
  | expect (e : Expect)

/-- A step's lines, gathered into what is told. -/
def Telling.of (ls : List StoryLine) : Telling := ls.foldl (fun t l => match l with
  | .says x => { t with say := if t.say.isEmpty then x else t.say ++ "\n\n" ++ x }
  | .note a x => { t with notes := t.notes ++ [(a, x)] }
  | .show ks => { t with reveal := t.reveal ++ ks }
  | .expect e => { t with expect := t.expect ++ [e] }) {}

/-- A scenario from a story: its opening lines and its steps, each a beat with what it tells. -/
def tell {W : Type} (id title doc : String) (snap : W → List (String × Json)) (w₀ : W)
    (opening : List StoryLine) (steps : List (Beat W × List StoryLine)) : Scenario :=
  let (frames, problems) := playChecked snap w₀
    (steps.map fun (b, ls) => { b with telling := Telling.of ls }) (Telling.of opening) (checked := true)
  { id, title, doc, frames, problems }

/-- Fail with every problem in a scenario. `story` runs this on what it defines, and `emit`
on every scenario it writes, so a story that says one thing while the domain does another
does not build. -/
def Scenario.check (s : Scenario) : CommandElabM Unit := do
  unless s.problems.isEmpty do
    throwError m!"story \"{s.id}\" does not match the domain ({s.problems.length} problems):\n" ++
      "\n".intercalate (s.problems.map ("  • " ++ ·))

declare_syntax_cat storyLine
syntax "says: " str : storyLine
syntax "note: " str str : storyLine
syntax "show: " str,+ : storyLine

/-- What a step does. `accepted "e", …` lists the events it records (constructor names, in
order; none: it records nothing), `warns "rule", …` the policy rules that warn. -/
declare_syntax_cat storyExpect (behavior := both)
syntax &"accepted" (str,+)? (&"warns" str,+)? : storyExpect
syntax &"refused" (str)? : storyExpect
syntax &"blocked" str,+ : storyExpect
syntax &"needs" str,+ : storyExpect
syntax &"stale" : storyExpect
syntax "expect: " storyExpect : storyLine

declare_syntax_cat storyStep
syntax "| " term (ppLine storyLine)* : storyStep

syntax (docComment)? "story " ident str str ("about: " str)? " from " term " using " term
  (ppLine storyLine)* (ppLine storyStep)* : command

syntax "story_line% " storyLine : term
macro_rules
  | `(story_line% says: $t:str) => `(StoryLine.says $t)
  | `(story_line% note: $a:str $t:str) => `(StoryLine.note $a $t)
  | `(story_line% show: $ks:str,*) => `(StoryLine.show [$ks,*])
  | `(story_line% expect: accepted $[$es:str,*]? $[warns $ws:str,*]?) =>
    let es := es.map (·.getElems) |>.getD #[]
    let ws := ws.map (·.getElems) |>.getD #[]
    `(StoryLine.expect (Expect.accepted [$es,*] [$ws,*]))
  | `(story_line% expect: refused $r:str) => `(StoryLine.expect (Expect.refused (some $r)))
  | `(story_line% expect: refused) => `(StoryLine.expect (Expect.refused none))
  | `(story_line% expect: blocked $rs:str,*) => `(StoryLine.expect (Expect.blocked [$rs,*]))
  | `(story_line% expect: needs $fs:str,*) => `(StoryLine.expect (Expect.needs [$fs,*]))
  | `(story_line% expect: stale) => `(StoryLine.expect Expect.stale)

syntax "story_step% " storyStep : term
macro_rules
  | `(story_step% | $b:term $ls:storyLine*) => `(($b, [$[story_line% $ls],*]))

macro_rules
  | `($[$doc:docComment]? story $n:ident $id:str $title:str $[about: $ab:str]? from $w:term using $snap:term
      $ls:storyLine* $steps:storyStep*) => do
    let about : TSyntax `str := ab.getD (Syntax.mkStrLit "")
    `($[$doc:docComment]? def $n : Scenario :=
        tell $id $title $about $snap $w [$[story_line% $ls],*] [$[story_step% $steps],*]
      #eval Scenario.check $n)

/-! ## Reading the environment -/

private def strip (spec : Spec) (s : String) : String :=
  let p := spec.ns.toString ++ "."
  (s.replace p "").replace "DDD." ""

private def ppE (spec : Spec) (e : Expr) : MetaM String := do
  return strip spec (toString (← ppExpr e))

private def isDomainType (env : Environment) (spec : Spec) (n : Name) : Bool :=
  spec.ns.isPrefixOf n && (isStructure env n || (env.find? n matches some (.inductInfo _)))

/-- `one`, `optional` or `many`, from the outermost type constructor. -/
private def cardOf (e : Expr) : String :=
  match e.getAppFn.constName? with
  | some ``List | some ``Array => "many"
  | some ``Option => "optional"
  | _ => "one"

private def typeRefs (env : Environment) (spec : Spec) (e : Expr) : Array Name :=
  (e.getUsedConstants.filter (isDomainType env spec)).toList.eraseDups.toArray

private def docOf (n : Name) : MetaM String := do
  return ((← findDocString? (← getEnv) n).getD "").trimAscii.toString

/-- A field or constructor argument. -/
private def slot (spec : Spec) (name : String) (ty : Expr) (doc : String) (kind : String) :
    MetaM (Json × Array Json) := do
  let env ← getEnv
  let refs := typeRefs env spec ty
  let j := Json.mkObj [("name", toJson name), ("type", toJson (← ppE spec ty)),
    ("doc", toJson doc), ("refs", toJson (refs.map (·.toString))), ("card", toJson (cardOf ty))]
  return (j, refs.map fun r => Json.mkObj [("to", toJson r.toString), ("label", toJson name),
    ("card", toJson (cardOf ty)), ("kind", toJson kind)])

private def describeStructure (spec : Spec) (n : Name) : MetaM (Json × Array Json × Array Name) := do
  let env ← getEnv
  let mut fields := #[]
  let mut edges := #[]
  let mut refs := #[]
  for f in getStructureFields env n do
    let proj := n ++ f
    let some ci := env.find? proj | continue
    let body ← forallTelescope ci.type fun _ b => pure b
    let isParent := (isSubobjectField? env n f).isSome
    let (j, es) ← slot spec f.toString body (← docOf proj) (if isParent then "extends" else "field")
    fields := fields.push j
    edges := edges ++ es
    refs := refs ++ typeRefs env spec body
  return (Json.mkObj [("fields", Json.arr fields)], edges, refs)

private def describeInductive (spec : Spec) (n : Name) : MetaM (Json × Array Json × Array Name) := do
  let env ← getEnv
  let .inductInfo v ← getConstInfo n | return (Json.mkObj [], #[], #[])
  let mut ctors := #[]
  let mut edges := #[]
  let mut refs := #[]
  for c in v.ctors do
    let ci ← getConstInfo c
    let (args, es, rs) ← forallTelescope ci.type fun xs _ => do
      let mut args := #[]
      let mut es := #[]
      let mut rs := #[]
      for x in xs[v.numParams:] do
        let d ← x.fvarId!.getDecl
        let (j, e) ← slot spec d.userName.eraseMacroScopes.toString d.type "" "arg"
        args := args.push j
        es := es ++ e
        rs := rs ++ typeRefs env spec d.type
      return (args, es, rs)
    ctors := ctors.push (Json.mkObj [("name", toJson c.componentsRev.head!.toString),
      ("doc", toJson (← docOf c)), ("args", Json.arr args)])
    edges := edges ++ es
    refs := refs ++ rs
  return (Json.mkObj [("ctors", Json.arr ctors)], edges, refs)

private def describe (spec : Spec) (n : Name) : MetaM (Json × Array Json × Array Name) := do
  if isStructure (← getEnv) n then describeStructure spec n else describeInductive spec n

/-- Every domain type reachable from these roots, each with what it refers to. -/
private def crawl (spec : Spec) (roots : List Name) :
    MetaM (Array (Name × Json × Array Json × Array Name)) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := roots.filter (isDomainType env spec)
  let mut out := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let (j, es, rs) ← describe spec n
    out := out.push (n, j, es, rs)
    todo := todo ++ rs.toList.filter (!seen.contains ·)
  return out

private def reachable (graph : Array (Name × Json × Array Json × Array Name)) (root : Name) :
    NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match graph.find? (·.1 == n) with
    | some (_, _, _, rs) => todo := todo ++ rs.toList
    | none => pure ()
  return seen

private def kindOf (env : Environment) (spec : Spec) (n : Name) : String :=
  match spec.kinds.lookup n with
  | some k => k
  | none =>
    if spec.aggregates.any (·.state == n) then "aggregate"
    else if spec.aggregates.any (·.cmd == n) then "command"
    else if spec.aggregates.any (·.evt == n) then "event"
    else if spec.aggregates.any (·.err == some n) then "rejection"
    else if isStructure env n then
      let fs := getStructureFields env n
      if fs.size == 1 then "identifier"
      else if fs.contains `id then "entity"
      else "value"
    else match env.find? n with
      | some (.inductInfo v) =>
        if v.ctors.all (fun c => match env.find? c with
          | some ci => !ci.type.isForall
          | none => true) then "enum" else "choice"
      | _ => "type"

/-- The aggregates whose types a declaration mentions. -/
private def aboutAggregates (spec : Spec) (n : Name) : MetaM (List String) := do
  let ci ← getConstInfo n
  let cs := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
  return spec.aggregates.filter (fun a => cs.any fun c =>
    a.state == c || a.cmd.isPrefixOf c || a.evt.isPrefixOf c) |>.map (·.id)

private def signature (spec : Spec) (n : Name) : MetaM String := do
  return strip spec (toString (← PrettyPrinter.ppSignature n).fmt)

/-- Everything the viewer needs about the domain's structure. -/
def model (spec : Spec) : MetaM Json := do
  let env ← getEnv
  let roots := spec.aggregates.flatMap (fun a => [a.state, a.cmd, a.evt] ++ a.err.toList) ++ spec.extraTypes
  let graph ← crawl spec roots
  -- Which aggregate's state reaches each type; several: shared.
  let owners := spec.aggregates.map fun a =>
    let r := [a.state, a.cmd, a.evt].flatMap (fun n => (reachable graph n).toList)
    (a.id, r)
  let types ← graph.mapM fun (n, j, es, _) => do
    let ownedBy := owners.filter (·.2.contains n) |>.map (·.1)
    let fields := j.getObjValD "fields"
    let ctors := j.getObjValD "ctors"
    return Json.mkObj [("id", toJson n.toString), ("name", toJson (strip spec n.toString)),
      ("kind", toJson (kindOf env spec n)), ("doc", toJson (← docOf n)),
      ("owners", toJson ownedBy), ("fields", fields), ("ctors", ctors),
      ("edges", Json.arr es)]
  let aggs ← spec.aggregates.mapM fun a => do
    let invs ← a.invariants.filterMapM fun t => do
      if env.contains t then
        return some (Json.mkObj [("name", toJson (strip spec t.toString)),
          ("doc", toJson (← docOf t)), ("signature", toJson (← signature spec t))])
      else return none
    return Json.mkObj [("id", toJson a.id), ("name", toJson (strip spec a.state.toString)),
      ("state", toJson a.state.toString), ("cmd", toJson a.cmd.toString),
      ("evt", toJson a.evt.toString), ("err", toJson (a.err.map (·.toString))),
      ("doc", toJson (← docOf a.state)), ("invariants", Json.arr invs.toArray)]
  let procs ← spec.processes.filterMapM fun p => do
    if !env.contains p.decl then return none
    let touches ← if p.touches.isEmpty then aboutAggregates spec p.decl else pure p.touches
    return some (Json.mkObj [("id", toJson p.id), ("name", toJson (strip spec p.decl.toString)),
      ("doc", toJson (← docOf p.decl)), ("signature", toJson (← signature spec p.decl)),
      ("touches", toJson touches)])
  let thms ← spec.theorems.filterMapM fun t => do
    if !env.contains t then return none
    let ci ← getConstInfo t
    let cs := ci.type.getUsedConstants
    let procsAbout := spec.processes.filter (fun p => cs.contains p.decl) |>.map (·.id)
    return some (Json.mkObj [("name", toJson (strip spec t.toString)), ("doc", toJson (← docOf t)),
      ("signature", toJson (← signature spec t)), ("about", toJson (← aboutAggregates spec t)),
      ("processes", toJson procsAbout)])
  return Json.mkObj [("id", toJson spec.id), ("title", toJson spec.title), ("doc", toJson spec.doc),
    ("ns", toJson spec.ns.toString),
    ("contexts", Json.arr (spec.contexts.map fun c => Json.mkObj [("id", toJson c.id),
      ("title", toJson c.title), ("doc", toJson c.doc), ("aggregates", toJson c.aggregates)]).toArray),
    ("aggregates", Json.arr aggs.toArray), ("processes", Json.arr procs.toArray),
    ("theorems", Json.arr thms.toArray), ("types", Json.arr types)]

/-! ## The site

The viewer ships inside this library (`DDD/Viz/*`, embedded at compile time), so a project
that depends on `ddd` gets it with no files to copy. `emit` writes one self-contained page
per domain and refreshes a catalog of every domain in the same directory:

```
site/
  index.html          catalog of every domain emitted here
  <id>.html           one domain: model, types, scenarios (data inlined; opens from disk)
  data/<id>.json      the domain's data, for other tools
  data/<id>.meta.json what the catalog lists
```
-/

private def shell : String := include_str "Viz/shell.html"
private def css : String := include_str "Viz/viewer.css"
private def app : String := include_str "Viz/viewer.js"

/-- JSON safe to put inside a `<script>` element. -/
private def scriptSafe (j : Json) : String :=
  j.compress.replace "</" "<\\/"

/-- A viewer file, read fresh from the `ddd` package's sources when they can be found (Lake
does not rebuild this module when only the viewer changes), else the copy embedded when
this module was compiled. -/
private def asset (name embedded : String) : IO String := do
  -- Where the package's sources are: here, or four levels up from its `.lake/build/lib/lean`
  -- on the search path (how a package that depends on `ddd` finds them).
  let roots := ("." : System.FilePath) :: (← searchPathRef.get).map (· / ".." / ".." / ".." / "..")
  for r in roots do
    let f := r / "DDD" / "Viz" / name
    if ← f.pathExists then
      if (← IO.FS.readFile (r / "DDD" / "Viz.lean")).startsWith "import Lean" then
        return ← IO.FS.readFile f
  return embedded

/-- The page around some data: the shell, the stylesheet, the viewer. -/
def page (title data : String) : IO String := do
  let shell ← asset "shell.html" shell
  let css ← asset "viewer.css" css
  let app ← asset "viewer.js" app
  return (((shell.replace "{{TITLE}}" title).replace "{{CSS}}" css).replace "{{APP}}" app).replace "{{DATA}}" data

/-- Rebuild `index.html` from every `data/*.meta.json` in `dir`. -/
def writeCatalog (dir : System.FilePath) : IO Unit := do
  let files ← (dir / "data").readDir
  let metas ← files.toList.filterMapM fun f => do
    if !f.fileName.endsWith ".meta.json" then return none
    match Json.parse (← IO.FS.readFile f.path) with
    | .ok j => return some j
    | .error _ => return none
  let key (j : Json) : String := (j.getObjValAs? String "title").toOption.getD ""
  let metas := metas.toArray.qsort (fun a b => key a < key b)
  let site := Json.mkObj [("mode", "catalog"), ("domains", Json.arr metas)]
  IO.FS.writeFile (dir / "index.html") (← page "Domain models" s!"window.DDD_SITE = {scriptSafe site};")

/-- The domain's model and scenarios, as the viewer reads them. -/
def data (spec : Spec) (scenarios : List Scenario) : MetaM Json := do
  let m ← model spec
  let scs := scenarios.map fun s => Json.mkObj [("id", toJson s.id), ("title", toJson s.title),
    ("doc", toJson s.doc), ("frames", s.frames)]
  return m.mergeObj (Json.mkObj [("scenarios", Json.arr scs.toArray)])

/-- The terms of the model that have no doc comment yet: `Type`, `Type.field`, `Type.case`.
The field that holds a parent structure is skipped: its fields are checked where they are declared. -/
def glossaryGaps (model : Json) : List String := Id.run do
  let arr (j : Json) (k : String) : Array Json := match j.getObjValD k with | .arr a => a | _ => #[]
  let str (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
  let mut out := #[]
  for t in arr model "types" do
    let n := str t "name"
    if str t "doc" == "" then out := out.push n
    let parents := (arr t "edges").filterMap fun e => if str e "kind" == "extends" then some (str e "label") else none
    for f in arr t "fields" do
      if !parents.contains (str f "name") && str f "doc" == "" then out := out.push s!"{n}.{str f "name"}"
    for c in arr t "ctors" do
      if str c "doc" == "" then out := out.push s!"{n}.{str c "name"}"
  return out.toList

/-- Write the domain's page into `dir` (default `site/`) and refresh the catalog there.
Call it from a script with `#eval emit spec scenarios`; `lake exe ddd-viz` runs every such
script. Warns about terms with no doc comment (see `glossaryGaps`). -/
def emit (spec : Spec) (scenarios : List Scenario) (dir : System.FilePath := "site") :
    CommandElabM Unit := do
  for s in scenarios do s.check
  let d ← liftTermElabM (data spec scenarios)
  IO.FS.createDirAll (dir / "data")
  IO.FS.writeFile (dir / "data" / s!"{spec.id}.json") d.compress
  let count (k : String) : Nat := match d.getObjValD k with | .arr a => a.size | _ => 0
  let summary := Json.mkObj [("id", toJson spec.id), ("title", toJson spec.title), ("doc", toJson spec.doc),
    ("href", toJson s!"{spec.id}.html"), ("aggregates", toJson (count "aggregates")),
    ("types", toJson (count "types")), ("theorems", toJson (count "theorems")),
    ("scenarios", toJson (count "scenarios"))]
  IO.FS.writeFile (dir / "data" / s!"{spec.id}.meta.json") summary.compress
  let site := Json.mkObj [("mode", "domain"), ("domain", toJson spec.id), ("home", "index.html")]
  IO.FS.writeFile (dir / s!"{spec.id}.html") (← page spec.title
    s!"window.DDD_SITE = {scriptSafe site};\nwindow.DDD_VIZ = \{{scriptSafe (toJson spec.id)}: {scriptSafe d}};")
  writeCatalog dir
  let gaps := glossaryGaps d
  unless gaps.isEmpty do
    let msg := m!"{gaps.length} terms have no doc comment, so the viewer can't define them:\n  {", ".intercalate (gaps.take 60)}{if gaps.length > 60 then ", …" else ""}"
    if spec.requireDocs then logError msg else logWarning msg
  logInfo m!"wrote {dir / s!"{spec.id}.html"}: {spec.aggregates.length} aggregates, {count "types"} types, {scenarios.length} scenarios"

end DDD.Viz
