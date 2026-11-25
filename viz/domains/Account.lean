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

story limits "limits" "Deposits, a limit, an overdraft"
  about: "The daily limit is $100. A withdrawal over it is blocked by policy; one over the balance is refused by the account itself."
  from ([] : World) using snap
  says: "A blank page: no account exists until the first deposit opens one."
  | beat "Open the account with $120" (.deposit 120)
    expect: accepted "deposited"
    says: "The customer deposits $120. That first deposit is what brings the account into being."
    note: "account" "The balance is everything deposited minus everything withdrawn: $120."
  | beat "Take out $50" (.withdraw 50)
    expect: accepted "withdrew"
    says: "A $50 withdrawal is under the $100 daily limit and within the balance, so it goes through."
    note: "account" "$120 − $50 = $70 left."
  | beat "Take out $200" (.withdraw 200)
    expect: blocked "withdrawal-limit"
    says: "$200 is over the daily limit. The bank's policy stops it before the account is even asked; only an administrator could let it through."
    note: "account" "Unchanged: a refused command records nothing."
  | beat "Take out $90" (.withdraw 90)
    expect: refused "insufficientFunds"
    says: "$90 is within the limit, so policy allows it. But only $70 is left, and the account itself refuses to go below zero."
    note: "account" "Policy and the account check different things: the limit is the bank's rule, never going negative is the account's own."
  | beat "Take out the $70 that is left" (.withdraw 70)
    expect: accepted "withdrew"
    says: "Taking out exactly what is left is fine."
    note: "account" "Empty, never negative. Lean proves no sequence of commands can make it negative."

#eval emit spec [limits]
