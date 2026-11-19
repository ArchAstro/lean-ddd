import DDD.Policy
import DDD.Aggregate

/-!
# Auditing a history

Run every rule over every entry of a log, each against the state just before it. This
is the health check after an import, and the preview before adopting a new pack version.
It reads the log and writes nothing.
-/

namespace DDD

variable {Ctx S C X : Type}

def auditFrom (agg : Aggregate S C C X) (rules : List (Rule Ctx S C)) (ctx : Ctx) :
    S → List C → List Finding
  | _, [] => []
  | s, c :: cs =>
    (evaluate rules .recording [] ctx s c).findings ++ auditFrom agg rules ctx (agg.evolve s c) cs

/-- Every finding the rules raise over a whole history. -/
def audit (agg : Aggregate S C C X) (rules : List (Rule Ctx S C)) (ctx : Ctx) (log : List C) :
    List Finding :=
  auditFrom agg rules ctx agg.init log

theorem auditFrom_complete (agg : Aggregate S C C X) (rules : List (Rule Ctx S C)) (ctx : Ctx)
    {r : Rule Ctx S C} (hr : r ∈ rules) (c : C) (post : List C) :
    ∀ (pre : List C) (s : S), r.eval ctx (agg.fold s pre) c = .fail →
      ∃ f ∈ auditFrom agg rules ctx s (pre ++ c :: post), f.rule = r.id
  | [], s, hf => by
    obtain ⟨f, hm, hid⟩ :=
      no_silent_violation (recording_never_stops rules [] ctx s c) hr hf
    exact ⟨f, List.mem_append_left _ hm, hid⟩
  | x :: pre, s, hf => by
    obtain ⟨f, hm, hid⟩ := auditFrom_complete agg rules ctx hr c post pre (agg.evolve s x) hf
    exact ⟨f, List.mem_append_right _ hm, hid⟩

/-- The audit misses nothing: any entry that fails any rule, anywhere in the history,
shows up as a finding. -/
theorem audit_complete (agg : Aggregate S C C X) (rules : List (Rule Ctx S C)) (ctx : Ctx)
    {r : Rule Ctx S C} (hr : r ∈ rules) (pre : List C) (c : C) (post : List C)
    (hf : r.eval ctx (agg.replay pre) c = .fail) :
    ∃ f ∈ audit agg rules ctx (pre ++ c :: post), f.rule = r.id :=
  auditFrom_complete agg rules ctx hr c post pre agg.init hf

/-- What adopting new rules would change: rule ids with findings that are new, and
rule ids whose findings go away. -/
def upgradePreview (agg : Aggregate S C C X) (old new : List (Rule Ctx S C)) (ctx : Ctx)
    (log : List C) : List String × List String :=
  let before := (audit agg old ctx log).map (·.rule)
  let after := (audit agg new ctx log).map (·.rule)
  ((after.filter (fun x => !before.contains x)).eraseDups,
   (before.filter (fun x => !after.contains x)).eraseDups)

/-- Adopting the same rules changes nothing. -/
theorem upgradePreview_same (agg : Aggregate S C C X) (rules : List (Rule Ctx S C)) (ctx : Ctx)
    (log : List C) : upgradePreview agg rules rules ctx log = ([], []) := by
  have h : ∀ l : List String, l.filter (fun x => !l.contains x) = [] := by
    intro l
    apply List.filter_eq_nil_iff.mpr
    intro a ha; simp [ha]
  simp only [upgradePreview, h]
  rfl

end DDD
