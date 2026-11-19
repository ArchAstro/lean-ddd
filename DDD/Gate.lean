import DDD.CommandPath

/-!
# The gate in front of the command path

Recording mode is a capability, checked before policy runs. It is available inside an
import window, or to a correction. A rule cannot make this check, because rules do not
block in recording mode.
-/

namespace DDD

/-- An import window. It cannot be longer than 180 days. -/
structure Window where
  opened : Nat
  days : Nat
  short : days ≤ 180

def Window.openOn (w : Window) (now : Nat) : Bool :=
  decide (w.opened ≤ now) && decide (now ≤ w.opened + w.days)

inductive Refusal (X : Type) where
  | forbidden (why : String)
  | rejected (r : Rejection X)
  deriving Repr

variable {Ctx S C E X : Type}

/-- May this command run in recording mode? -/
def mayRecord (window : Option Window) (correction : Bool) (now : Nat) : Bool :=
  correction || (match window with | none => false | some w => w.openOn now)

def guardedSubmit (agg : Aggregate S C E X) (rules : List (Rule Ctx S C)) (mode : Mode)
    (window : Option Window) (correction : Bool) (now : Nat)
    (ovr : List Override) (ctx : Ctx) (log : List E) (expected : Nat) (c : C) :
    Except (Refusal X) (List E × List Finding) :=
  if mode = .recording ∧ mayRecord window correction now = false then
    .error (.forbidden "recording mode outside the import window")
  else
    match submit agg rules mode ovr ctx log expected c with
    | .ok r => .ok r
    | .error e => .error (.rejected e)

variable {agg : Aggregate S C E X} {rules : List (Rule Ctx S C)} {mode : Mode}
  {window : Option Window} {correction : Bool} {now : Nat}
  {ovr : List Override} {ctx : Ctx} {log log' : List E} {expected : Nat} {c : C}
  {fs : List Finding}

/-- Whatever the gate lets through went through `submit`, so every command-path
guarantee still holds. -/
theorem guardedSubmit_ok
    (h : guardedSubmit agg rules mode window correction now ovr ctx log expected c =
      .ok (log', fs)) :
    submit agg rules mode ovr ctx log expected c = .ok (log', fs) ∧
      (mode = .recording → mayRecord window correction now = true) := by
  unfold guardedSubmit at h
  split at h
  · cases h
  · rename_i hn
    split at h
    · rename_i r hs
      cases h
      refine ⟨hs, ?_⟩
      intro hm
      cases hw : mayRecord window correction now with
      | true => rfl
      | false => exact absurd ⟨hm, hw⟩ hn
    · cases h

/-- Outside the window, and not as a correction, nothing is recorded in recording mode. -/
theorem recording_needs_window (h : mayRecord window correction now = false) :
    ∀ r, guardedSubmit agg rules .recording window correction now ovr ctx log expected c ≠
      .ok r := by
  intro r hr
  simp [guardedSubmit, h] at hr

/-- A window is closed after at most 180 days. -/
theorem window_closes (w : Window) (now : Nat) (h : w.opened + 180 < now) :
    w.openOn now = false := by
  have := w.short
  simp [Window.openOn]; omega

/-- Enforcing mode is always available. -/
theorem enforcing_ungated :
    guardedSubmit agg rules .enforcing window correction now ovr ctx log expected c =
      (match submit agg rules .enforcing ovr ctx log expected c with
        | .ok r => .ok r
        | .error e => .error (.rejected e)) := by
  simp [guardedSubmit]

end DDD
