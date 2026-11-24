import DDD.Viz
import Examples.Account

/-!
# The account example, for the viewer

Run `lake exe ddd-viz` (or `lake env lean viz/domains/Account.lean`), then open
`site/index.html`.
-/

open Lean DDD DDD.Viz Examples Examples.Account

deriving instance ToJson for Account

def spec : Spec where
  id := "account"
  title := "Bank account"
  doc := "The smallest domain: one account, deposits and withdrawals, a balance that is never negative, and a withdrawal limit an administrator can override."
  ns := `Examples
  aggregates := [
    { id := "account", state := `Examples.Account, cmd := `Examples.Account.Cmd
      evt := `Examples.Account.Evt, err := some `Examples.Account.Why
      invariants := [`Examples.Account.nonneg_sound] }]

abbrev World := List Evt

def snap (w : World) : List (String × Json) :=
  let a := account.replay w
  [("account", Json.mkObj [("exists", toJson !w.isEmpty), ("view", Json.mkObj [("balance", toJson a.balance)]), ("raw", toJson a)])]

def beat (note : String) (c : Cmd) : Beat World :=
  submitBeat (C := Cmd) (E := Evt) (X := Why) account "account" note "customer"
    (fun _ => [limit]) (fun _ => ctx) id (fun _ l => l) c

def scenarios : List Scenario := [
  { id := "limits", title := "Deposits, a limit, an overdraft",
    doc := "The daily limit is $100. A withdrawal over it is blocked by policy; one over the balance is refused by the aggregate itself.",
    frames := play snap [] [
      beat "Open the account with $120" (.deposit 120),
      beat "Take out $50: within the limit and the balance" (.withdraw 50),
      beat "Take out $200: over the daily limit, so policy blocks it" (.withdraw 200),
      beat "Take out $90: within the limit, but only $70 is left, so the account refuses" (.withdraw 90),
      beat "Take out the $70 that is left" (.withdraw 70) ] }]

#eval emit spec scenarios
