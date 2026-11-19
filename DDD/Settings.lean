/-!
# Settings

A setting is a named value read by rules, reactions and jobs. It can be set at several
scopes, written here widest first (for example product, pack, tenant, group, item).
The narrowest scope that sets a value wins. Any scope may set a bound; every value at
that scope or narrower must lie inside it.
-/

namespace DDD

structure Bound where
  lo : Nat
  hi : Nat
  deriving Repr

def Bound.contains (b : Bound) (v : Nat) : Bool := decide (b.lo ≤ v) && decide (v ≤ b.hi)

structure Layer where
  value : Option Nat := none
  bound : Option Bound := none
  deriving Repr

/-- The effective value: start from `cur`, let each narrower scope replace it. -/
def resolveFrom (cur : Nat) : List Layer → Nat
  | [] => cur
  | l :: rest => resolveFrom (l.value.getD cur) rest

def bounds (chain : List Layer) : List Bound := chain.filterMap (·.bound)

/-- The check made when a setting is written: at every scope, the value in effect there
lies inside that scope's bound and every wider bound. -/
def respects (cur : Nat) (bs : List Bound) : List Layer → Bool
  | [] => true
  | l :: rest =>
    let v := l.value.getD cur
    let bs' := l.bound.toList ++ bs
    bs'.all (·.contains v) && respects v bs' rest

/-- Write a layer at position `i`. A write that breaks a bound is refused. -/
def setLayer (default : Nat) (chain : List Layer) (i : Nat) (l : Layer) : Option (List Layer) :=
  let chain' := chain.set i l
  if respects default [] chain' then some chain' else none

/-- A narrower scope may tighten but never loosen: the effective value lies inside every
bound set anywhere in the chain. -/
theorem resolve_within :
    ∀ (chain : List Layer) (cur : Nat) (bs : List Bound),
      respects cur bs chain = true → (∀ b ∈ bs, b.contains cur = true) →
      ∀ b ∈ bs ++ bounds chain, b.contains (resolveFrom cur chain) = true
  | [], cur, bs, _, hcur, b, hb => by
    simp [bounds] at hb
    simpa [resolveFrom] using hcur b hb
  | l :: rest, cur, bs, h, _, b, hb => by
    simp only [respects, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hv, hrest⟩ := h
    have ih := resolve_within rest (l.value.getD cur) (l.bound.toList ++ bs) hrest hv
    apply ih
    simp only [bounds, List.filterMap_cons, List.mem_append] at hb
    simp only [List.mem_append, bounds]
    rcases hb with hb | hb
    · exact Or.inl (Or.inr hb)
    · cases hbound : l.bound with
      | none => rw [hbound] at hb; exact Or.inr hb
      | some b0 =>
        rw [hbound] at hb
        simp only [List.mem_cons] at hb
        rcases hb with hb | hb
        · subst hb; exact Or.inl (Or.inl (by simp))
        · exact Or.inr hb

/-- An accepted write leaves a chain whose effective value is inside every bound. -/
theorem setLayer_within (default : Nat) (chain chain' : List Layer) (i : Nat) (l : Layer)
    (h : setLayer default chain i l = some chain') :
    ∀ b ∈ bounds chain', b.contains (resolveFrom default chain') = true := by
  unfold setLayer at h
  simp only at h
  split at h
  · rename_i hr
    cases h
    intro b hb
    exact resolve_within _ default [] hr (by simp) b (by simpa using hb)
  · cases h

/-- The narrowest scope wins. -/
theorem narrowest_wins (cur v : Nat) (chain : List Layer) (b : Option Bound) :
    resolveFrom cur (chain ++ [⟨some v, b⟩]) = v := by
  induction chain generalizing cur with
  | nil => rfl
  | cons l rest ih => exact ih _

/-- A scope that sets nothing inherits. -/
theorem unset_inherits (cur : Nat) (chain : List Layer) (b : Option Bound) :
    resolveFrom cur (chain ++ [⟨none, b⟩]) = resolveFrom cur chain := by
  induction chain generalizing cur with
  | nil => rfl
  | cons l rest ih => exact ih _

end DDD
