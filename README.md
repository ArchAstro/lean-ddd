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

## Build

```sh
lake build    # checks every proof and every #guard
lake test     # builds the examples
```

## Licence

MIT. See [LICENSE](LICENSE).
