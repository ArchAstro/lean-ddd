import DDD

/-!
# Example: a bank account

A small, self-contained domain built on `DDD`:

1. an aggregate with an invariant (the balance never goes negative),
2. its soundness proof, the one obligation a domain owes the framework,
3. a policy rule written with `rule!`,
4. commands sent through `submit`, checked with `#guard`.
-/

namespace Examples.Account
open DDD

inductive Cmd where
  | deposit (n : Nat)
  | withdraw (n : Nat)
  deriving Repr

inductive Evt where
  | deposited (n : Nat)
  | withdrew (n : Nat)
  deriving Repr

inductive Why where
  | insufficientFunds
  deriving Repr

/-- The balance is an `Int` so that the invariant says something. -/
def account : Aggregate Int Cmd Evt Why where
  init := 0
  decide
    | _, .deposit n => .ok [.deposited n]
    | s, .withdraw n => if (n : Int) ≤ s then .ok [.withdrew n] else .error .insufficientFunds
  evolve
    | s, .deposited n => s + n
    | s, .withdrew n => s - n

/-- The balance is never negative, on any log of accepted commands. -/
theorem nonneg_sound : account.Sound (fun s => 0 ≤ s) where
  init := by decide
  step := by
    intro s c es hs hd
    cases c with
    | deposit n =>
      simp [account] at hd; subst hd
      simp [Aggregate.fold, account]; omega
    | withdraw n =>
      simp only [account] at hd
      split at hd
      · cases hd; simp [Aggregate.fold, account]; omega
      · cases hd

/-- The context a rule may read: here, a daily withdrawal limit. -/
structure Ctx where
  dailyLimit : Nat

/-- Large withdrawals need an administrator's override. -/
def limit : Rule Ctx Int Cmd :=
  rule! "withdrawal-limit" product cite "account terms"
    require (fun (ctx : Ctx) (_ : Int) (c : Cmd) =>
      match c with
      | .withdraw n => decide (n ≤ ctx.dailyLimit)
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
example {rules : List (Rule Ctx Int Cmd)} {mode ovr c fs} {l l' : List Evt} {v : Nat}
    (hc : account.Committed l) (h : submit account rules mode ovr ctx l v c = .ok (l', fs)) :
    0 ≤ account.replay l' :=
  submit_inv nonneg_sound hc h

end Examples.Account
