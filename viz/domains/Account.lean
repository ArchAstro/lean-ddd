import DDD.Viz
import Examples.Account
import Examples.AccountService

/-!
# The account example, for the viewer

Run `lake exe ddd-viz` (or `lake env lean viz/domains/Account.lean`), then open
`site/index.html`.
-/

open Lean DDD DDD.Viz Examples Examples.Account Examples.AccountService

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
  systems := [
    { id := "acquirer", name := "Card acquirer", kind := "payment provider"
      doc := "Takes money from customers' cards, and gives it back."
      apis := [("charges", "Holds and captures"), ("refunds", "Money back to a card")] }]
  ports := [
    { id := "charges", decl := `Examples.AccountService.Charges, system := some "acquirer"
      apis := ["charges"], acl := [`Examples.AccountService.depositOf, `Examples.AccountService.declineOf] },
    { id := "refunds", decl := `Examples.AccountService.Refunds, system := some "acquirer"
      apis := ["refunds"] }]
  services := [
    { id := "account-service", name := "Account service"
      doc := "What a customer does with their account, end to end."
      ports := ["charges", "refunds"]
      useCases := [
        { id := "depositByCard", decl := `Examples.AccountService.depositByCard, asks := ["charges"], changes := ["account"] },
        { id := "refundDeposit", decl := `Examples.AccountService.refundDeposit, asks := ["refunds"], changes := ["account"] },
        { id := "withdraw", decl := `Examples.AccountService.withdraw, changes := ["account"] }] }]

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

/-! ## The acquirer, scripted -/

/-- The Charges API as a script: holds with `status`, captures `taken` in `currency`, or
times out. -/
def charges (status := "approved") (taken : Option Nat := none) (currency := "USD")
    (down := false) : Charges Script where
  authorize card n := Script.reply "charges" "authorize" s!"{card.token}, {n}"
    (if down then .error .timeout else .ok { auth_id := "auth_1", amount_minor := n, currency := "USD", status })
  capture id := Script.reply "charges" "capture" id
    (.ok { capture_id := "cap_1", auth_id := id, amount_minor := taken.getD 0, currency } :
      Except AcquirerError CaptureDto)

/-- The Refunds API as a script. -/
def refunds (down := false) : Refunds Script where
  refund cap n := Script.reply "refunds" "refund" s!"{cap}, {n}"
    (if down then .error .timeout else .ok { refund_id := "ref_1", amount_minor := n })

/-- What a use case returned, as an outcome. -/
def outcome (w : World) : Except (AppError Why) World → World × Viz.Outcome
  | .ok w' => (w', { ok := true, events := newEvents w w' })
  | .error e => (w, Viz.Outcome.ofAppError e)

def byCard (note : String) (amount : Nat) (ch : Charges Script) : Beat World :=
  serviceBeat "account-service" "depositByCard" note "customer" ["account"]
    s!"depositByCard tok_visa {amount}" fun w => outcome w <$> depositByCard ch w ⟨"tok_visa"⟩ amount

def refundBeat (note : String) (amount : Nat) (rf : Refunds Script) : Beat World :=
  serviceBeat "account-service" "refundDeposit" note "customer" ["account"]
    s!"refundDeposit cap_1 {amount}" fun w => outcome w <$> refundDeposit rf w "cap_1" amount

story card "card" "Deposits by card"
  about: "The account service takes money from a card through the acquirer's Charges API, and gives it back through its Refunds API. The account never talks to the acquirer: the service asks, translates the answer, and only then tells the account."
  from ([] : World) using snap
  says: "No account yet. Every step here goes through the account service, which talks to the card acquirer."
  | byCard "Deposit $80 by card" 80 (charges (taken := some 80))
    asks: "charges.authorize", "charges.capture"
    expect: accepted "deposited"
    says: "The service holds $80 on the card, captures it, and the anti-corruption layer turns the capture into a deposit of 80. Only then does the account hear about it."
    note: "account" "$80, from a capture the acquirer confirmed."
  | byCard "Deposit $40 with a declined card" 40 (charges (status := "declined"))
    asks: "charges.authorize"
    expect: failed "card-declined"
    says: "The acquirer declines the hold. The layer turns its `declined` into the domain's card-declined, and the service stops: nothing is captured, the account is never asked."
    note: "account" "Unchanged."
  | byCard "Deposit $30 while the acquirer is down" 30 (charges (down := true))
    asks: "charges.authorize"
    expect: failed "acquirer-unavailable"
    says: "The acquirer times out. That is an infrastructure failure, not a domain refusal: no event, nothing saved, try again later."
  | byCard "Deposit $25, captured in euros" 25 (charges (taken := some 25) (currency := "EUR"))
    asks: "charges.authorize", "charges.capture"
    expect: failed "capture-unusable"
    says: "The capture comes back in euros. The account only holds dollars, so the layer refuses to translate it, and nothing is deposited."
  | refundBeat "Refund $30 to the card" 30 (refunds)
    asks: "refunds.refund"
    expect: accepted "withdrew"
    says: "The account pays the $30 back first; then the Refunds API returns it to the card. Both or neither."
    note: "account" "$80 − $30 = $50."
  | refundBeat "Refund $60" 60 (refunds)
    asks:
    expect: refused "insufficientFunds"
    says: "$60 is within the limit, but only $50 is left. The account refuses to pay back more than it holds, so the service never calls the acquirer."

#eval emit spec [limits, card]
