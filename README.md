# lean-ddd

Domain-driven design in Lean 4, with the guarantees proved.

`DDD` gives you aggregates, a policy engine, a command path, jobs and the rest of the
plumbing a business domain sits on. You write your aggregate and prove one theorem, that
your invariant is sound. Every theorem about the command path, jobs, batches and audits
then applies to your domain for free.

- Lean `v4.35.0` (see `lean-toolchain`).
- No dependencies beyond Lean core.
- No `sorry`, no axioms beyond Lean's standard three.

## What is in it

| Module | What it is |
|---|---|
| `DDD.Aggregate` | Aggregates (`decide`, `evolve`), replay, snapshots, sound invariants, atomic batches; `AggregateRoot`, a state type that is an aggregate |
| `DDD.Journal` | Bitemporal journal: legal date and recorded date; as-of views |
| `DDD.Policy` | Rules with three outcomes, override classes, assurance, modes, findings; raising a class; publishing a rule |
| `DDD.Pack` | Dated parameters; rule packs chosen by jurisdiction and adopted version |
| `DDD.Effects` | Post-commit effects and the compliance record |
| `DDD.CommandPath` | `submit`: version check, policy, aggregate, append |
| `DDD.Gate` | Recording mode as a capability: import windows and corrections |
| `DDD.Settings` | Scoped settings with bounds; narrower scopes may tighten, never loosen |
| `DDD.Reaction` | Reactions to events, and their modes (automatic, confirm, off) |
| `DDD.Job` | A small job language and its runner; views are jobs that never write |
| `DDD.Requirements` | Approvals and documents a draft needs before it commits |
| `DDD.Audit` | Run every rule over a whole history; preview a pack upgrade |
| `DDD.Syntax` | `rule!` and `steps![...]` macros |
| `DDD.Codec` | A stored form with a proved round trip, and `derive_codec` |

`import DDD` brings in everything except `DDD.Codec`, which you import on its own.

## How a command is handled

```text
draft ──► gate ──► rules ──► aggregate ──► append ──► post-commit rules ──► compliance record
          │        │         │                         │
          │        │         └ possible?               └ deadlines, classifications, stale marks
          │        └ pass / fail / unknown, per rule
          └ recording mode allowed? (import window or correction)
```

1. `submit` rejects a command built on an out-of-date version, so policy and the
   aggregate see the same state.
2. Each rule returns pass, fail or unknown. Its override class, assurance and the mode
   decide whether that blocks, leaves a finding, or asks for a missing fact.
3. The aggregate decides whether the command is possible. Policy can never weaken it:
   `submit_inv` holds whatever the rules, mode or overrides.

## Example

A bank account whose balance never goes negative (the full file, with checks, is
[`Examples/Account.lean`](Examples/Account.lean)):

```lean
import DDD
open DDD

structure Account where
  balance : Int

namespace Account

inductive Cmd where
  | deposit (n : Nat)
  | withdraw (n : Nat)

inductive Evt where
  | deposited (n : Nat)
  | withdrew (n : Nat)

inductive Why where
  | insufficientFunds

def decide (a : Account) : Cmd → Except Why (List Evt)
  | .deposit n => .ok [.deposited n]
  | .withdraw n =>
    if (n : Int) ≤ a.balance then .ok [.withdrew n] else .error .insufficientFunds

def evolve (a : Account) : Evt → Account
  | .deposited n => { a with balance := a.balance + n }
  | .withdrew n => { a with balance := a.balance - n }

/-- `Account` is an aggregate: the state type names its commands, events and rejections. -/
instance : AggregateRoot Account where
  Cmd := Cmd
  Evt := Evt
  Err := Why
  init := { balance := 0 }
  decide := decide
  evolve := evolve

/-- The aggregate, for `replay`, `submit` and the theorems about them. -/
abbrev account := Aggregate.of Account

/-- The one proof obligation: the invariant holds initially and every accepted command keeps it. -/
theorem nonneg_sound : account.Sound (fun a => 0 ≤ a.balance) where
  init := by decide
  step := by
    intro s c es hs hd
    cases c with
    | deposit n =>
      simp [AggregateRoot.decide, decide] at hd; subst hd
      simp [Aggregate.fold, AggregateRoot.evolve, evolve]; omega
    | withdraw n =>
      simp only [AggregateRoot.decide, decide] at hd
      split at hd
      · cases hd; simp [Aggregate.fold, AggregateRoot.evolve, evolve]; omega
      · cases hd

structure Ctx where
  dailyLimit : Nat

/-- Large withdrawals need an administrator's override. -/
def limit : Rule Ctx Account Cmd :=
  rule! "withdrawal-limit" product cite "account terms"
    require (fun (ctx : Ctx) (_ : Account) (c : Cmd) =>
      match c with
      | .withdraw n => Decidable.decide (n ≤ ctx.dailyLimit)
      | .deposit _ => true)
    else deny_unless_administrator reviewed_by ["alice", "bob"]

/-- Whatever passes `submit`, the balance stays non-negative. -/
example {rules : List (Rule Ctx Account Cmd)} {mode ovr c fs} {l l' : List Evt} {v : Nat}
    (hc : account.Committed l) (h : submit account rules mode ovr ⟨100⟩ l v c = .ok (l', fs)) :
    0 ≤ (account.replay l').balance :=
  submit_inv nonneg_sound hc h

end Account
```

## Use it

Add it to your `lakefile.toml`, pinned to a release tag:

```toml
[[require]]
name = "ddd"
git = "https://github.com/ArchAstro/lean-ddd"
rev = "v0.2.0"
```

Or, in a `lakefile.lean`:

```lean
require ddd from git "https://github.com/ArchAstro/lean-ddd" @ "v0.2.0"
```

Then run `lake update ddd` and `import DDD`. Use the same Lean version as this
repository's `lean-toolchain`.

## Drawing a domain: `lake exe ddd-viz`

Any domain built on `DDD` gets a static demo site, generated from the compiled model.

```
lake exe ddd-viz                 # every viz/domains/*.lean  →  site/
lake exe ddd-viz path/to/X.lean  # just these
open site/index.html
```

Each page has two views:

1. **Model**: a class diagram of every type the domain declares.
   - Each type has a stereotype: «aggregate root», «entity», «value object», «identifier», «enumeration», «choice», «commands», «events», «rejections» or «process».
   - Boxes sit inside frames, one for each bounded context and one inside it for each aggregate.
   - Connections can be switched on and off by type: composition, extends, reference by id, command → root → event, rejections and processes.
   - Zoomed out, boxes shrink to their names, and the connections between two aggregates become one line labelled with their count.
   - Boxes and frames can be dragged, and their positions are saved per browser.
2. **Scenarios**: stories told on an object diagram, built from the state each aggregate has after each step (`raw`).
   - The page starts blank. An object comes onto it at the first step that creates, changes or targets it, or that a note or `show:` names. The layout grows with the story: each step is laid out with only what is on the page by then, so objects stay together; when room is needed, they glide to their new places and only what the step brings in fades in. The context the story is mostly about sits on top, and the others in a row beneath it, so what arrives at its bottom edge is next to them.
   - Each step has a caption saying what is happening, in plain words, and notes pinned beside the objects they are about. A note whose object is off screen, or has no free spot beside it, docks under the caption; click it to go there. A note naming an object that does not exist is shown as a warning.
   - Each object shows its field values, leaving out fields that stay empty throughout. Lines show what each object contains and the entities it refers to by id.
   - An object's identity comes from its `id`, or else its role in its parent (`payments[1] : Payment`).
   - The command arrives next to the aggregate it targets and is accepted ✓ or refused ✕, with the reason in words. New objects are outlined in green, changed rows are marked in amber, and events appear under the command.

A domain script names declarations; everything else is read from Lean (`viz/domains/Account.lean` is a complete one):

```lean
import DDD.Viz
import MyDomain
open DDD.Viz

def spec : Spec where
  id := "orders"; title := "Orders"; ns := `MyDomain
  aggregates := [{ id := "order", state := `MyDomain.Order, cmd := `MyDomain.Order.Cmd,
                   evt := `MyDomain.Order.Evt, invariants := [`MyDomain.Order.sound] }]
  processes  := [{ id := "checkout", decl := `MyDomain.checkout }]  -- touches: inferred
  theorems   := [`MyDomain.paid_once]

def place (note : String) (c : Cmd) : Beat World :=
  submitBeat order "order" note "alice" … c

story happy "happy" "An order, paid"
  about: "Alice orders a book and pays for it."
  from world₀ using snap
  says: "Nothing exists yet."
  | place "Alice places an order" (.place "o-1" "book")
    says: "Alice orders a book. Placing it is what creates the order."
    note: "order" "Status: placed. Nothing is owed until it's confirmed."
  | place "Alice pays" (.pay "o-1")
    says: "She pays, and the order is done."
    note: "order/payments[0]" "The payment, kept with the order."

#eval emit spec [happy]   -- writes site/orders.html and refreshes site/index.html
```

- `story` defines a `Scenario`. Each `|` step is a beat, followed by what to tell at that step:
  - `says: "…"` what is happening and why it matters, for someone new to the domain. Markdown.
  - `note: "key" "…"` a note pinned to one object. A key is an aggregate id (`"order"`), or an object inside one: `aggregate/field#id`, or `aggregate/field[i]` when it has no id. It can go deeper (`order/items#3/discount`).
  - `show: "key", …` brings objects onto the page that the step does not change.
  - Lines before the first `|` tell the opening, blank page.

- `submitBeat` sends one command through `submit`, with the domain's rules and context.
- A hand-built `Beat` can run a process (set `via`) or advance a clock.
- `snap` returns `{exists, view, raw}` for each aggregate:
  - `raw` is the state as `ToJson`, drawn as objects using the model's types.
  - `exists` (optional) is false until the aggregate has been created, so its empty initial state is not drawn.
  - `view` (optional) holds readable values for the side panel.
- `Spec.contexts` groups aggregates into bounded contexts, which are drawn as frames.
- The viewer (`DDD/Viz/{shell.html,viewer.css,viewer.js}`, React with no build step) is read from this package at emit time, so a project that depends on `ddd` gets it as is.

## Build

```sh
lake build    # checks every proof and every #guard
lake test     # builds the examples
```

## Licence

MIT. See [LICENSE](LICENSE).
