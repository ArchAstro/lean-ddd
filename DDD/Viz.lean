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
  /-- Short id used by the viewer and by scenarios (`"report"`). -/
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

structure Outcome where
  ok : Bool
  error : String := ""
  events : List String := []
  /-- What policy noted about an accepted command: rules it broke that only warn, overrides,
  facts it could not check. -/
  findings : List String := []

/-- One step of a scenario: who does what to which aggregates, and how to run it. -/
structure Beat (W : Type) where
  note : String
  actor : String := ""
  /-- The process it goes through, if any (a `ProcSpec` id). -/
  via : Option String := none
  targets : List String
  command : String
  run : W → W × Outcome

structure Scenario where
  id : String
  title : String
  doc : String := ""
  frames : Json

/-- The events appended to a log, as text. -/
def newEvents {E : Type} [Repr E] (before after : List E) : List String :=
  (after.drop before.length).map (fun e => reprStr e)

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
    | .ok (log', fs) => (set w log', { ok := true, events := newEvents log log', findings := fs.map Finding.say })
    | .error why => (w, { ok := false, error := reprStr why })

/-- Run beats in order. Frame 0 is the starting state; each later frame is one beat, with
every aggregate's snapshot after it.

A snapshot is an object per aggregate id:
- `raw`: the state as `ToJson`; the viewer draws it as objects, using the model's types;
- `exists` (optional, default true): false until the aggregate has been created, so the
  viewer does not draw its empty initial state as if it were a real object;
- `view` (optional): readable values for the side panel.

An entry named `@world` is not an aggregate: it is an object of facts about the world the
scenario runs in, such as today's date, and the viewer shows it on every step. -/
def play {W : Type} (snap : W → List (String × Json)) (w₀ : W) (beats : List (Beat W)) : Json :=
  let frame (w : W) (b : Option (Beat W)) (o : Outcome) : Json :=
    Json.mkObj [
      ("note", toJson ((b.map (·.note)).getD "The starting state")),
      ("actor", toJson ((b.map (·.actor)).getD "")),
      ("via", match b.bind (·.via) with | some v => toJson v | none => Json.null),
      ("targets", toJson ((b.map (·.targets)).getD [])),
      ("command", toJson ((b.map (·.command)).getD "")),
      ("ok", toJson o.ok), ("error", toJson o.error), ("events", toJson o.events),
      ("findings", toJson o.findings),
      ("start", toJson b.isNone),
      ("state", Json.mkObj (snap w))]
  let (_, frames) := beats.foldl (fun (w, acc) b =>
    let (w', o) := b.run w
    (w', acc ++ [frame w' (some b) o])) (w₀, [frame w₀ none { ok := true }])
  Json.arr frames.toArray

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
