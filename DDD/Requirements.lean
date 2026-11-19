import DDD.CommandPath

/-!
# Requirements

Some rules do not judge a draft; they add something it needs: an approval from a named
body, or a document. In enforcing mode a draft commits only when every need has been
fulfilled. In recording mode an unmet need becomes a finding.
-/

namespace DDD

inductive Need where
  | approval (body : String)
  | document (type : String)
  deriving DecidableEq, Repr

structure NeedRule (Ctx S C : Type) where
  id : String
  needs : Ctx → S → C → List Need

variable {Ctx S C E X : Type}

def needsFor (rules : List (NeedRule Ctx S C)) (ctx : Ctx) (s : S) (c : C) :
    List (String × Need) :=
  rules.flatMap (fun r => (r.needs ctx s c).map (fun n => (r.id, n)))

def unmet (needs : List (String × Need)) (fulfilled : List Need) : List (String × Need) :=
  needs.filter (fun n => !fulfilled.contains n.2)

def Need.describe : Need → String
  | .approval body => "approval: " ++ body
  | .document type => "document: " ++ type

inductive NeedRefusal (X : Type) where
  | unmet (needs : List (String × Need))
  | rejected (r : Rejection X)
  deriving Repr

def submitWithNeeds (agg : Aggregate S C E X) (rules : List (Rule Ctx S C))
    (needRules : List (NeedRule Ctx S C)) (mode : Mode) (ovr : List Override) (ctx : Ctx)
    (log : List E) (expected : Nat) (c : C) (fulfilled : List Need) :
    Except (NeedRefusal X) (List E × List Finding) :=
  let u := unmet (needsFor needRules ctx (agg.replay log) c) fulfilled
  if mode = .enforcing ∧ u ≠ [] then .error (.unmet u)
  else
    match submit agg rules mode ovr ctx log expected c with
    | .ok (log', fs) => .ok (log', fs ++ u.map (fun n => ⟨n.1, .missingFact n.2.describe⟩))
    | .error e => .error (.rejected e)

variable {agg : Aggregate S C E X} {rules : List (Rule Ctx S C)}
  {needRules : List (NeedRule Ctx S C)} {mode : Mode} {ovr : List Override} {ctx : Ctx}
  {log log' : List E} {expected : Nat} {c : C} {fulfilled : List Need} {fs : List Finding}

/-- In enforcing mode, a draft that commits had every approval and document it needed. -/
theorem needs_met
    (h : submitWithNeeds agg rules needRules .enforcing ovr ctx log expected c fulfilled =
      .ok (log', fs)) :
    ∀ n ∈ needsFor needRules ctx (agg.replay log) c, n.2 ∈ fulfilled := by
  unfold submitWithNeeds at h
  simp only at h
  split at h
  · cases h
  · rename_i hn
    intro n hn'
    have hu : unmet (needsFor needRules ctx (agg.replay log) c) fulfilled = [] := by
      cases hx : unmet (needsFor needRules ctx (agg.replay log) c) fulfilled with
      | nil => rfl
      | cons a as => exact absurd ⟨trivial, by simp [hx]⟩ hn
    have := List.filter_eq_nil_iff.mp hu n hn'
    simpa using this

/-- Whatever commits went through `submit`, so every command-path guarantee holds. -/
theorem needs_then_submit
    (h : submitWithNeeds agg rules needRules mode ovr ctx log expected c fulfilled =
      .ok (log', fs)) :
    ∃ fs0, submit agg rules mode ovr ctx log expected c = .ok (log', fs0) := by
  unfold submitWithNeeds at h
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i l f hs; cases h; exact ⟨f, hs⟩
    · cases h

end DDD
