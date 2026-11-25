import DDD
import Examples.Account

/-!
# Example: the account's application service, and a card acquirer

The account domain (`Examples.Account`) is pure. This file puts the application layer
around it:

1. **An external system:** a card acquirer, with two APIs, Charges and Refunds.
2. **Two ports, one per API:** `Charges` (two operations) and `Refunds` (one). Each
   operation has its own DTOs, the acquirer's own model: `AuthorizationDto`, `CaptureDto`,
   `RefundDto`, `AcquirerError`.
3. **An anti-corruption layer:** `depositOf` and `declineOf` turn the acquirer's DTOs into
   what the account understands, or say why not. `depositOf_pos` proves it never yields a
   deposit of nothing.
4. **An application service, `AccountService`,** with three use cases: `depositByCard`
   asks `Charges`, `refundDeposit` asks `Refunds`, and `withdraw` asks nothing. Each loads
   the account's log, asks, sends the domain a command, and returns the log to save.

The use cases take their ports as arguments, over any monad: production passes adapters;
the story in `viz/domains/Account.lean` passes scripted answers.
-/

namespace Examples.AccountService
open DDD Examples Examples.Account

/-! ## The acquirer's model -/

/-- A card, as the acquirer tokenises it. -/
structure CardToken where
  /-- The acquirer's opaque token for the card. -/
  token : String
  deriving Repr

/-- A hold on a card, as the Charges API returns it. -/
structure AuthorizationDto where
  /-- The acquirer's id for the hold. -/
  auth_id : String
  /-- What was held, in the currency's smallest unit. -/
  amount_minor : Nat
  /-- The ISO code of the currency held. -/
  currency : String
  /-- The acquirer's word for the outcome: `approved`, `declined` or `review`. -/
  status : String
  deriving Repr

/-- Money taken from a hold, as the Charges API returns it. -/
structure CaptureDto where
  /-- The acquirer's id for the capture. -/
  capture_id : String
  /-- The hold it took the money from. -/
  auth_id : String
  /-- What was taken, in the currency's smallest unit. -/
  amount_minor : Nat
  /-- The ISO code of the currency taken. -/
  currency : String
  deriving Repr

/-- Money given back to a card, as the Refunds API returns it. -/
structure RefundDto where
  /-- The acquirer's id for the refund. -/
  refund_id : String
  /-- What was given back, in the currency's smallest unit. -/
  amount_minor : Nat
  deriving Repr

/-- What the acquirer's APIs fail with. -/
inductive AcquirerError where
  /-- The acquirer did not answer in time. -/
  | timeout
  /-- Too many requests; try again later. -/
  | rateLimited
  /-- The acquirer would not accept the request. -/
  | invalidRequest (message : String)
  deriving Repr

/-! ## Ports: one per API -/

/-- Taking money from a card: the acquirer's Charges API. -/
structure Charges (m : Type → Type) where
  /-- Hold an amount on a card. -/
  authorize : (card : CardToken) → (amount : Nat) → m (Except AcquirerError AuthorizationDto)
  /-- Take the money a hold reserved. -/
  capture : (authId : String) → m (Except AcquirerError CaptureDto)

/-- Giving money back to a card: the acquirer's Refunds API. -/
structure Refunds (m : Type → Type) where
  /-- Give back part or all of a capture. -/
  refund : (captureId : String) → (amount : Nat) → m (Except AcquirerError RefundDto)

/-! ## The anti-corruption layer -/

/-- A capture, as the amount to deposit in cents. Only dollars, and only a capture of
something: anything else is refused, with the reason. -/
def depositOf (c : CaptureDto) : Except String Nat :=
  if c.currency ≠ "USD" then .error "capture-unusable"
  else if c.amount_minor = 0 then .error "capture-unusable"
  else .ok c.amount_minor

/-- A hold the acquirer did not approve, as the reason in the domain's words. -/
def declineOf (a : AuthorizationDto) : Option String :=
  if a.status = "approved" then none
  else if a.status = "declined" then some "card-declined"
  else some "card-under-review"

/-- The layer never turns a capture into a deposit of nothing. -/
theorem depositOf_pos {c : CaptureDto} {n : Nat} (h : depositOf c = .ok n) : 0 < n := by
  unfold depositOf at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; omega

/-! ## The application service -/

/-- Deposit by card: hold the amount, take it, and deposit what was taken. Nothing is
deposited unless the acquirer approved the hold and the capture is one the account can take. -/
def depositByCard {m : Type → Type} [Monad m] (charges : Charges m) (log : List Evt)
    (card : CardToken) (amount : Nat) : m (Except (AppError Why) (List Evt)) := do
  let .ok hold ← charges.authorize card amount | return .error (.failed "acquirer-unavailable")
  if let some why := declineOf hold then return .error (.failed why)
  let .ok cap ← charges.capture hold.auth_id | return .error (.failed "acquirer-unavailable")
  match depositOf cap with
  | .error why => return .error (.failed why)
  | .ok n =>
    return match submit account [limit] .enforcing [] ctx log log.length (.deposit n) with
      | .ok (log', _) => .ok log'
      | .error why => .error (.refused why)

/-- Refund a card deposit: the account pays it back first, then the acquirer refunds the
card. If the refund fails, nothing is saved. -/
def refundDeposit {m : Type → Type} [Monad m] (refunds : Refunds m) (log : List Evt)
    (captureId : String) (amount : Nat) : m (Except (AppError Why) (List Evt)) := do
  match submit account [limit] .enforcing [] ctx log log.length (.withdraw amount) with
  | .error why => return .error (.refused why)
  | .ok (log', _) =>
    let .ok _ ← refunds.refund captureId amount | return .error (.failed "acquirer-unavailable")
    return .ok log'

/-- Withdraw cash at the counter. It asks no one outside. -/
def withdraw (log : List Evt) (amount : Nat) : Except (AppError Why) (List Evt) :=
  match submit account [limit] .enforcing [] ctx log log.length (.withdraw amount) with
  | .ok (log', _) => .ok log'
  | .error why => .error (.refused why)

end Examples.AccountService
