/-!
# Bitemporal journal

Every event carries two dates: the legal (effective) date and the date it was recorded.
A view is taken "as of" a pair of dates. Nothing is ever removed, so a report can be
reproduced exactly as it was issued.
-/

namespace DDD

structure Recorded (E : Type) where
  event : E
  effective : Nat
  recordedAt : Nat
  deriving Repr

variable {E : Type}

/-- Events effective on or before `legal`, as known on `known`. -/
def asOf (legal known : Nat) (j : List (Recorded E)) : List E :=
  (j.filter (fun r => decide (r.effective ≤ legal) && decide (r.recordedAt ≤ known))).map (·.event)

/-- Record events at time `now`. -/
def record (now : Nat) (effective : E → Nat) (es : List E) (j : List (Recorded E)) :
    List (Recorded E) :=
  j ++ es.map (fun e => ⟨e, effective e, now⟩)

/-- Recording is append-only. -/
theorem record_prefix (now : Nat) (effective : E → Nat) (es : List E) (j : List (Recorded E)) :
    j <+: record now effective es j :=
  List.prefix_append _ _

/-- Anything recorded after the "as known on" date does not change the view. -/
theorem asOf_reproducible (legal known : Nat) (j new : List (Recorded E))
    (h : ∀ r ∈ new, known < r.recordedAt) :
    asOf legal known (j ++ new) = asOf legal known j := by
  have hnil : new.filter
      (fun r => decide (r.effective ≤ legal) && decide (r.recordedAt ≤ known)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro r hr
    have := h r hr
    simp
    omega
  simp [asOf, List.filter_append, hnil]

/-- A report issued at `known` stays the same after any later recording, including
later corrections dated in the past. -/
theorem record_reproducible (legal known now : Nat) (effective : E → Nat) (es : List E)
    (j : List (Recorded E)) (h : known < now) :
    asOf legal known (record now effective es j) = asOf legal known j := by
  apply asOf_reproducible
  intro r hr
  simp at hr
  obtain ⟨_, _, rfl⟩ := hr
  exact h

/-- With both dates at or after everything in the journal, the view is the whole log. -/
theorem asOf_all (legal known : Nat) (j : List (Recorded E))
    (h : ∀ r ∈ j, r.effective ≤ legal ∧ r.recordedAt ≤ known) :
    asOf legal known j = j.map (·.event) := by
  unfold asOf
  congr 1
  apply List.filter_eq_self.mpr
  intro r hr
  have := h r hr
  simp [this.1, this.2]

end DDD
