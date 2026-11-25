import DDD.Viz
import Examples.Account
import Examples.AccountService

/-!
# Stories that do not build

A story says what each step does (`expect:`), and the build fails when the domain does
something else. These are the mistakes it catches, each with the message it gives.
-/

namespace Examples.Stories
open Lean DDD DDD.Viz Examples.Account Examples.AccountService

deriving instance ToJson for Account

abbrev World := List Evt

def snap (w : World) : List (String × Json) :=
  [("account", Json.mkObj [("exists", toJson !w.isEmpty), ("raw", toJson (account.replay w))])]

def beat (note : String) (c : Cmd) : Beat World :=
  submitBeat (C := Cmd) (E := Evt) (X := Why) account "account" note "customer"
    (fun _ => [limit]) (fun _ => ctx) id (fun _ l => l) c

-- A story that says what happens builds.
story good "good" "Deposit, then a withdrawal over the limit"
  from ([] : World) using snap
  | beat "Deposit $120" (.deposit 120)
    says: "The first deposit opens the account."
    expect: accepted "deposited"
    note: "account" "$120."
  | beat "Take out $200" (.withdraw 200)
    says: "Over the daily limit, so policy stops it."
    expect: blocked "withdrawal-limit"

/--
error: story "claims" does not match the domain (1 problems):
  • step 2 ("Take out $200"): the story says it is accepted, recording withdrew, but it was blocked by withdrawal-limit. If the story is wrong, write: expect: blocked "withdrawal-limit"
-/
#guard_msgs in
story claims "claims" "Says a blocked withdrawal goes through"
  from ([] : World) using snap
  | beat "Deposit $500" (.deposit 500)
    says: "Open with $500."
    expect: accepted "deposited"
  | beat "Take out $200" (.withdraw 200)
    says: "The customer takes out $200."
    expect: accepted "withdrew"

/--
error: story "reason" does not match the domain (1 problems):
  • step 2 ("Take out $90"): the story says it is blocked by withdrawal-limit, but it was refused: insufficientFunds. If the story is wrong, write: expect: refused "insufficientFunds"
-/
#guard_msgs in
story reason "reason" "Gives the wrong reason for a refusal"
  from ([] : World) using snap
  | beat "Deposit $50" (.deposit 50)
    says: "Open with $50."
    expect: accepted "deposited"
  | beat "Take out $90" (.withdraw 90)
    says: "Policy stops it."
    expect: blocked "withdrawal-limit"

/--
error: story "unsaid" does not match the domain (2 problems):
  • step 1 ("Deposit $50"): say what it does with `expect:`; it was accepted, recording deposited. Write: expect: accepted "deposited"
  • step 1 ("Deposit $50"): has no `says:`; tell a reader what is happening
-/
#guard_msgs in
story unsaid "unsaid" "A step with no words and no expectation"
  from ([] : World) using snap
  | beat "Deposit $50" (.deposit 50)

/--
error: story "ghost" does not match the domain (2 problems):
  • the opening: there is no object "account" on the page to note or show
  • step 1 ("Deposit $50"): there is no object "account/owner" on the page to note or show
-/
#guard_msgs in
story ghost "ghost" "Notes about objects that are not there"
  from ([] : World) using snap
  show: "account"
  | beat "Deposit $50" (.deposit 50)
    says: "Open with $50."
    expect: accepted "deposited"
    note: "account/owner" "Nobody owns it."

/-! ## Use cases and the outside: a story can't hide a call, or claim one -/

/-- The acquirer's Charges API, approving every hold and capturing all of it. -/
def approving : Charges Script where
  authorize _ n := Script.reply "charges" "authorize" s!"{n}"
    (.ok { auth_id := "a", amount_minor := n, currency := "USD", status := "approved" } : Except AcquirerError _)
  capture id := Script.reply "charges" "capture" id
    (.ok { capture_id := "c", auth_id := id, amount_minor := 50, currency := "USD" } : Except AcquirerError _)

def byCard (note : String) : Beat World :=
  serviceBeat "account-service" "depositByCard" note "customer" ["account"] "depositByCard 50" fun w => do
    let r ← depositByCard approving w ⟨"tok"⟩ 50
    pure <| match r with
      | .ok w' => (w', { ok := true, events := newEvents w w' })
      | .error e => (w, Viz.Outcome.ofAppError e)

/--
error: story "hidden" does not match the domain (1 problems):
  • step 1 ("Deposit $50 by card"): it calls charges.authorize, charges.capture; say so with `asks:`. Write: asks: "charges.authorize", "charges.capture"
-/
#guard_msgs in
story hidden "hidden" "Does not say the step calls the acquirer"
  from ([] : World) using snap
  | byCard "Deposit $50 by card"
    says: "The customer deposits $50."
    expect: accepted "deposited"

/--
error: story "claimed" does not match the domain (1 problems):
  • step 1 ("Deposit $50 by card"): the story says it asks refunds.refund, but it asked charges.authorize, charges.capture. Write: asks: "charges.authorize", "charges.capture"
-/
#guard_msgs in
story claimed "claimed" "Says the step asks for a refund"
  from ([] : World) using snap
  | byCard "Deposit $50 by card"
    asks: "refunds.refund"
    says: "The customer deposits $50."
    expect: accepted "deposited"

/--
error: story "outage" does not match the domain (1 problems):
  • step 1 ("Deposit $50 by card"): the story says it fails with acquirer-unavailable, but it was accepted, recording deposited. If the story is wrong, write: expect: accepted "deposited"
-/
#guard_msgs in
story outage "outage" "Says a deposit that went through failed"
  from ([] : World) using snap
  | byCard "Deposit $50 by card"
    asks: "charges.authorize", "charges.capture"
    says: "The acquirer is down."
    expect: failed "acquirer-unavailable"


end Examples.Stories
