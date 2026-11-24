import DDD

/-!
# Example: a bank account

A small, self-contained domain built on `DDD`:

1. a state type that is an aggregate (`AggregateRoot Account`), with an invariant
   (the balance never goes negative),
2. its soundness proof, the one obligation a domain owes the framework,
3. a policy rule written with `rule!`,
4. commands sent through `submit`, checked with `#guard`.
-/

namespace Examples
open DDD

/-- A bank account, holding a customer's balance. -/
structure Account where
  /-- The money in the account; it never goes below zero. -/
  balance : Int
  deriving Repr

namespace Account

/-- A request a customer makes of their account. -/
inductive Cmd where
  /-- Ask to deposit money into the account. -/
  | deposit (n : Nat)
  /-- Ask to withdraw money from the account. -/
  | withdraw (n : Nat)
  deriving Repr

/-- Something that happened to the account. -/
inductive Evt where
  /-- Money was deposited into the account. -/
  | deposited (n : Nat)
  /-- Money was withdrawn from the account. -/
  | withdrew (n : Nat)
  deriving Repr

/-- Why the bank refused a request on the account. -/
inductive Why where
  /-- The withdrawal is more than the balance. -/
  | insufficientFunds
  deriving Repr

def decide (a : Account) : Cmd → Except Why (List Evt)
  | .deposit n => .ok [.deposited n]
  | .withdraw n =>
    if (n : Int) ≤ a.balance then .ok [.withdrew n] else .error .insufficientFunds

def evolve (a : Account) : Evt → Account
  | .deposited n => { a with balance := a.balance + n }
  | .withdrew n => { a with balance := a.balance - n }

/-- `Account` is an aggregate. The balance is an `Int` so that the invariant says something. -/
instance : AggregateRoot Account where
  Cmd := Cmd
  Evt := Evt
  Err := Why
  init := { balance := 0 }
  decide := decide
  evolve := evolve

/-- The account as one whole, which accepts or refuses each request and records what happened. -/
abbrev account := Aggregate.of Account

/-- The balance is never negative, on any log of accepted commands. -/
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

/-- The account terms the bank's rules consult, here the daily limit on withdrawals. -/
structure Ctx where
  /-- The daily limit: the largest withdrawal allowed without an administrator's override. -/
  dailyLimit : Nat

/-- Large withdrawals need an administrator's override. -/
def limit : Rule Ctx Account Cmd :=
  rule! "withdrawal-limit" product cite "account terms"
    require (fun (ctx : Ctx) (_ : Account) (c : Cmd) =>
      match c with
      | .withdraw n => Decidable.decide (n ≤ ctx.dailyLimit)
      | .deposit _ => true)
    else deny_unless_administrator reviewed_by ["alice", "bob"]

def ctx : Ctx := ⟨100⟩
def log : List Evt := [.deposited 500]

def accepted : Except (Rejection Why) (List Evt × List Finding) → Bool
  | .ok _ => true
  | .error _ => false

-- Within the limit and the balance: accepted.
#guard accepted (submit account [limit] .enforcing [] ctx log 1 (.withdraw 50))
-- Over the limit: blocked by policy, until an administrator overrides.
#guard !accepted (submit account [limit] .enforcing [] ctx log 1 (.withdraw 200))
#guard accepted (submit account [limit] .enforcing
  [⟨"withdrawal-limit", .administrator, "approved by phone", "ticket-1"⟩] ctx log 1 (.withdraw 200))
-- Over the balance: the aggregate refuses, whatever policy says.
#guard !accepted (submit account [limit] .recording [] ctx log 1 (.withdraw 900))
-- Built on an out-of-date version: rejected as stale.
#guard !accepted (submit account [limit] .enforcing [] ctx log 0 (.deposit 1))

/-- Whatever passes `submit`, the balance stays non-negative. -/
example {rules : List (Rule Ctx Account Cmd)} {mode ovr c fs} {l l' : List Evt} {v : Nat}
    (hc : account.Committed l) (h : submit account rules mode ovr ctx l v c = .ok (l', fs)) :
    0 ≤ (account.replay l').balance :=
  submit_inv nonneg_sound hc h

end Account
end Examples
