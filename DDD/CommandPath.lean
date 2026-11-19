import DDD.Aggregate
import DDD.Policy

/-!
# The command path

`submit` is the only way a command reaches a stream:

1. reject a command built on an out-of-date version;
2. evaluate policy against the current state;
3. let the aggregate decide whether the command is possible;
4. append.

Policy and the aggregate see the same state, because step 1 pins the version.
-/

namespace DDD

inductive Rejection (X : Type) where
  | stale (expected actual : Nat)
  | policy (v : Verdict)
  | impossible (x : X)
  deriving Repr

variable {Ctx S C E X : Type}

def submit (agg : Aggregate S C E X) (rules : List (Rule Ctx S C)) (mode : Mode)
    (ovr : List Override) (ctx : Ctx) (log : List E) (expected : Nat) (c : C) :
    Except (Rejection X) (List E × List Finding) :=
  if expected ≠ log.length then .error (.stale expected log.length)
  else
    let v := evaluate rules mode ovr ctx (agg.replay log) c
    if v.proceeds then
      match agg.decide (agg.replay log) c with
      | .ok es => .ok (log ++ es, v.findings)
      | .error x => .error (.impossible x)
    else .error (.policy v)

variable {agg : Aggregate S C E X} {rules : List (Rule Ctx S C)} {mode : Mode}
  {ovr : List Override} {ctx : Ctx} {log log' : List E} {expected : Nat} {c : C}
  {fs : List Finding}

/-- Everything that must have been true for a command to be accepted. -/
theorem submit_ok (h : submit agg rules mode ovr ctx log expected c = .ok (log', fs)) :
    expected = log.length ∧
    (evaluate rules mode ovr ctx (agg.replay log) c).proceeds = true ∧
    fs = (evaluate rules mode ovr ctx (agg.replay log) c).findings ∧
    ∃ es, agg.decide (agg.replay log) c = .ok es ∧ log' = log ++ es := by
  unfold submit at h
  split at h
  · cases h
  · rename_i hv
    simp only at h
    split at h
    · rename_i hp
      split at h
      · rename_i es hd
        cases h
        exact ⟨by omega, hp, rfl, es, hd, rfl⟩
      · cases h
    · cases h

/-- A command built on an out-of-date version is rejected. -/
theorem submit_stale (h : expected ≠ log.length) :
    submit agg rules mode ovr ctx log expected c = .error (.stale expected log.length) := by
  simp [submit, h]

/-- Append-only: the old log is a prefix of the new one. -/
theorem submit_append_only (h : submit agg rules mode ovr ctx log expected c = .ok (log', fs)) :
    log <+: log' := by
  obtain ⟨_, _, _, es, _, rfl⟩ := submit_ok h
  exact List.prefix_append _ _

theorem submit_committed (hc : agg.Committed log)
    (h : submit agg rules mode ovr ctx log expected c = .ok (log', fs)) :
    agg.Committed log' := by
  obtain ⟨_, _, _, es, hd, rfl⟩ := submit_ok h
  exact .step hc hd

/-- Core invariants hold after every accepted command, whatever the mode, the rules or
the overrides. Policy cannot weaken the core. -/
theorem submit_inv {Inv : S → Prop} (hs : agg.Sound Inv) (hc : agg.Committed log)
    (h : submit agg rules mode ovr ctx log expected c = .ok (log', fs)) :
    Inv (agg.replay log') :=
  (submit_committed hc h).inv agg hs

/-- In recording mode, a command on the current version is accepted exactly when the
core finds it possible. -/
theorem submit_recording (es : List E) (hd : agg.decide (agg.replay log) c = .ok es) :
    submit agg rules .recording ovr ctx log log.length c =
      .ok (log ++ es, (evaluate rules .recording ovr ctx (agg.replay log) c).findings) := by
  simp [submit, recording_never_stops, hd]

/-- In enforcing mode with no overrides, an accepted command passed every gating rule. -/
theorem submit_enforcing_clean
    (h : submit agg rules .enforcing [] ctx log expected c = .ok (log', fs))
    {r : Rule Ctx S C} (hr : r ∈ rules) (hg : r.gate ≠ none) :
    r.eval ctx (agg.replay log) c = .pass :=
  enforcing_clean (submit_ok h).2.1 hr hg

/-- Every failed rule on an accepted command is in the findings that `submit` returns. -/
theorem submit_no_silent_violation
    (h : submit agg rules mode ovr ctx log expected c = .ok (log', fs))
    {r : Rule Ctx S C} (hr : r ∈ rules) (hf : r.eval ctx (agg.replay log) c = .fail) :
    ∃ f ∈ fs, f.rule = r.id := by
  obtain ⟨_, hp, rfl, _⟩ := submit_ok h
  exact no_silent_violation hp hr hf

end DDD
