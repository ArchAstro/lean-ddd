import DDD.Policy

/-!
# Packs and parameters

A pack is a versioned bundle of rules and parameters for one jurisdiction. An entity
runs the rules of the packs it is registered under, at the versions it has adopted.
A parameter is a number that changes over time; a rule names it and gets the value in
force on the evaluation date.
-/

namespace DDD

inductive ParamStatus where
  | inForce
  | announced
  | proposed
  deriving DecidableEq, Repr

structure ParamValue where
  value : Nat
  since : Nat
  thru : Option Nat := none
  status : ParamStatus := .inForce
  deriving Repr

def ParamValue.covers (v : ParamValue) (d : Nat) : Bool :=
  decide (v.since ≤ d) && (match v.thru with | none => true | some u => decide (d ≤ u))

/-- In force on `d`. Announced and proposed values are for what-if only. -/
def ParamValue.inEffect (v : ParamValue) (d : Nat) : Bool :=
  decide (v.status = .inForce) && v.covers d

structure Param where
  name : String
  values : List ParamValue
  deriving Repr

def Param.on (p : Param) (d : Nat) : Option Nat :=
  (p.values.find? (·.inEffect d)).map (·.value)

/-- What-if: also consider values that are announced but not yet in force. -/
def Param.onIncludingAnnounced (p : Param) (d : Nat) : Option Nat :=
  (p.values.find? (fun v => decide (v.status ≠ .proposed) && v.covers d)).map (·.value)

/-- No two in-force values cover the same date. -/
def Param.consistent (p : Param) : Prop :=
  p.values.Pairwise (fun a b => ∀ d, ¬ (a.inEffect d = true ∧ b.inEffect d = true))

theorem Param.on_in_effect {p : Param} {d v : Nat} (h : p.on d = some v) :
    ∃ pv ∈ p.values, pv.inEffect d = true ∧ pv.value = v := by
  simp only [Param.on, Option.map_eq_some_iff] at h
  obtain ⟨pv, hf, rfl⟩ := h
  have he : pv.inEffect d = true := List.find?_some (p := fun x : ParamValue => x.inEffect d) hf
  exact ⟨pv, List.mem_of_find?_eq_some hf, he, rfl⟩

theorem pairwise_mem {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b ∨ R a b ∨ R b a := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.pairwise_cons] at h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (h.1 b hb))
    · exact Or.inr (Or.inr (h.1 a ha))
    · exact ih h.2 ha hb

/-- With consistent values there is exactly one answer: any value in force on the date
is the one a rule gets. -/
theorem Param.on_unique {p : Param} (hc : p.consistent) {d : Nat} {pv : ParamValue}
    (hm : pv ∈ p.values) (he : pv.inEffect d = true) : p.on d = some pv.value := by
  cases hf : p.values.find? (·.inEffect d) with
  | none =>
    have := List.find?_eq_none.mp hf pv hm
    exact absurd he this
  | some pv' =>
    have hm' := List.mem_of_find?_eq_some hf
    have he' : pv'.inEffect d = true := List.find?_some (p := fun x : ParamValue => x.inEffect d) hf
    rcases pairwise_mem hc hm hm' with rfl | h | h
    · simp [Param.on, hf]
    · exact absurd ⟨he, he'⟩ (h d)
    · exact absurd ⟨he', he⟩ (h d)

/-- A value that is only announced is never what a rule gets. -/
theorem Param.announced_not_in_effect (v : ParamValue) (d : Nat) (h : v.status = .announced) :
    v.inEffect d = false := by
  simp [ParamValue.inEffect, h]

/-! ## Packs -/

structure Pack (Ctx S C : Type) where
  id : String
  version : Nat
  /-- `none` applies everywhere: product policy and contract terms. -/
  jurisdiction : Option String
  rules : List (Rule Ctx S C)
  params : List Param := []

variable {Ctx S C : Type}

def Pack.appliesTo (p : Pack Ctx S C) (registeredIn : List String)
    (adopted : List (String × Nat)) : Bool :=
  (match p.jurisdiction with | none => true | some j => registeredIn.contains j) &&
    adopted.contains (p.id, p.version)

/-- The rules an entity runs. -/
def rulesFor (packs : List (Pack Ctx S C)) (registeredIn : List String)
    (adopted : List (String × Nat)) : List (Rule Ctx S C) :=
  (packs.filter (·.appliesTo registeredIn adopted)).flatMap (·.rules)

/-- The value of a named parameter across the entity's packs. -/
def paramFor (packs : List (Pack Ctx S C)) (registeredIn : List String)
    (adopted : List (String × Nat)) (name : String) (d : Nat) : Option Nat :=
  ((packs.filter (·.appliesTo registeredIn adopted)).flatMap (·.params)).findSome?
    (fun p => if p.name = name then p.on d else none)

def Pack.publishable (p : Pack Ctx S C) : Bool := p.rules.all (·.publishable)

/-- Every rule an entity runs comes from a pack for a jurisdiction it is registered in
(or one that applies everywhere), at a version it has adopted. -/
theorem rulesFor_spec {packs : List (Pack Ctx S C)} {registeredIn : List String}
    {adopted : List (String × Nat)} {r : Rule Ctx S C}
    (h : r ∈ rulesFor packs registeredIn adopted) :
    ∃ p ∈ packs, r ∈ p.rules ∧ (p.id, p.version) ∈ adopted ∧
      ∀ j, p.jurisdiction = some j → j ∈ registeredIn := by
  simp only [rulesFor, List.mem_flatMap, List.mem_filter] at h
  obtain ⟨p, ⟨hp, ha⟩, hr⟩ := h
  simp only [Pack.appliesTo, Bool.and_eq_true] at ha
  refine ⟨p, hp, hr, by simpa using ha.2, ?_⟩
  intro j hj
  rw [hj] at ha
  simpa using ha.1

/-- A pack for a jurisdiction the entity is not registered in contributes nothing. -/
theorem unregistered_pack_is_silent (p : Pack Ctx S C) (registeredIn : List String)
    (adopted : List (String × Nat)) (j : String) (hj : p.jurisdiction = some j)
    (hn : j ∉ registeredIn) : rulesFor [p] registeredIn adopted = [] := by
  have : p.appliesTo registeredIn adopted = false := by
    simp [Pack.appliesTo, hj, hn]
  simp [rulesFor, this]

/-- A new pack version changes nothing until the entity adopts it. -/
theorem unadopted_version_is_silent (p : Pack Ctx S C) (registeredIn : List String)
    (adopted : List (String × Nat)) (hn : (p.id, p.version) ∉ adopted) :
    rulesFor [p] registeredIn adopted = [] := by
  have : p.appliesTo registeredIn adopted = false := by
    simp [Pack.appliesTo, hn]
  simp [rulesFor, this]

/-- Every rule an entity runs from published packs is itself publishable. -/
theorem rulesFor_publishable {packs : List (Pack Ctx S C)} {registeredIn : List String}
    {adopted : List (String × Nat)} (hp : ∀ p ∈ packs, p.publishable = true)
    {r : Rule Ctx S C} (h : r ∈ rulesFor packs registeredIn adopted) : r.publishable = true := by
  obtain ⟨p, hmem, hr, _⟩ := rulesFor_spec h
  have := hp p hmem
  simp only [Pack.publishable, List.all_eq_true] at this
  exact this r hr

end DDD
