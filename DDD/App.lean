import DDD.CommandPath

/-!
# Application services, ports and the outside world

The domain is pure: aggregates decide from what they are given, and never call out.
Everything that touches the outside world sits around it:

```
 use case ─▶ load (repository) ─▶ ask (port ─▶ anti-corruption layer ─▶ external API)
          ─▶ decide (aggregate) ─▶ save ─▶ publish
```

1. An **application service** groups related use cases, such as `ReportService.submit`,
   `.approve` and `.pay`. A use case is one transaction. It holds no business rules: it
   loads, asks, hands what it learned to the domain as a command, and saves what the domain
   decided.
2. A **port** is an interface the application owns, in the domain's words. In Lean it is a
   structure of operations over a monad, so one port can have many functions, each with its
   own request and response types (DTOs):
   ```lean
   structure Payouts (m : Type → Type) where
     create : PayoutRequest → m (Except PayoutError PayoutDto)
     cancel : PayoutId → m (Except PayoutError Unit)
   ```
   A port may front a whole external system (one port for all of Stripe) or one of its
   APIs (a port per Stripe API); `Viz.PortSpec` records which.
3. An **anti-corruption layer** turns the system's DTOs into the domain's value objects,
   or says why it can't. No DTO gets past it.
4. A use case takes its ports as arguments. Production passes adapters; tests and stories
   pass scripted answers (`Script`), so a story with outside calls is still deterministic,
   and a theorem can say what holds *whatever* the outside answers.

What a use case can fail with is not what the domain refuses: an outage or an answer that
does not fit is `AppError.failed`; the domain saying no is `AppError.refused`.
-/

namespace DDD

/-- Why a use case did not go through. -/
inductive AppError (X : Type) where
  /-- The domain refused: stale, blocked by policy, or impossible. -/
  | refused (r : Rejection X)
  /-- The outside failed, or answered something the anti-corruption layer would not accept.
  Nothing was decided and nothing was saved. -/
  | failed (reason : String)
  deriving Repr

/-- One call through a port, as a script answered it. -/
structure Call where
  port : String
  op : String
  /-- The arguments, as text. -/
  args : String := ""
  /-- The answer, as text. -/
  result : String := ""
  /-- Whether the call succeeded. -/
  ok : Bool := true
  deriving Repr, Inhabited, BEq

/-- Scripted ports: each call is answered by the script and recorded, so a story can show
what was asked and what came back. -/
abbrev Script := StateM (List Call)

/-- Answer a port call with `r`, and record it. -/
def Script.reply {ε α : Type} [Repr ε] [Repr α] (port op args : String) (r : Except ε α) :
    Script (Except ε α) := do
  let (ok, text) := match r with
    | .ok a => (true, reprStr a)
    | .error e => (false, reprStr e)
  modify (· ++ [{ port, op, args, result := text, ok }])
  pure r

/-- Run a scripted use case: its result and the calls it made. -/
def Script.run' {α : Type} (s : Script α) : α × List Call := StateT.run s [] |>.run

end DDD
