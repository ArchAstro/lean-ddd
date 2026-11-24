/-!
# `lake exe ddd-viz`

Builds the demo site for every domain script.

```
lake exe ddd-viz                      # every viz/domains/*.lean
lake exe ddd-viz path/to/Domain.lean  # just these
```

A domain script is any Lean file that ends with `#eval DDD.Viz.emit spec scenarios`; see
`viz/domains/Account.lean` for the smallest one. The driver builds the package first (so
the script's imports are compiled), then elaborates each script with `lake env lean`,
which runs its `emit`. The site lands in `site/`: open `site/index.html`.
-/

def scriptsIn (dir : System.FilePath) : IO (Array System.FilePath) := do
  if !(← dir.pathExists) then return #[]
  let fs ← dir.readDir
  return (fs.filter (·.fileName.endsWith ".lean")).map (·.path) |>.qsort (·.toString < ·.toString)

def run (cmd : String) (args : Array String) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args, stdin := .null, stdout := .inherit, stderr := .inherit }
  child.wait

def main (args : List String) : IO UInt32 := do
  if args.any (· ∈ ["-h", "--help"]) then
    IO.println "usage: lake exe ddd-viz [script.lean ...]   (default: viz/domains/*.lean; output: site/)"
    return 0
  let scripts ← if args.isEmpty then scriptsIn "viz/domains" else pure (args.toArray.map System.FilePath.mk)
  if scripts.isEmpty then
    IO.eprintln "ddd-viz: no domain scripts. Put one in viz/domains/ or name it on the command line."
    return 1
  IO.println "ddd-viz: building the package"
  if (← run "lake" #["build"]) != 0 then return 1
  -- A package that depends on `ddd` doesn't import the viewer itself, so build it explicitly.
  if (← run "lake" #["build", "DDD.Viz"]) != 0 then return 1
  let mut failed := #[]
  for s in scripts do
    IO.println s!"ddd-viz: {s}"
    if (← run "lake" #["env", "lean", s.toString]) != 0 then failed := failed.push s
  if failed.isEmpty then
    IO.println s!"ddd-viz: {scripts.size} domain(s) written. Open site/index.html"
    return 0
  IO.eprintln s!"ddd-viz: failed: {failed.toList}"
  return 1
