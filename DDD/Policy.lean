/-!
# Policy

Policy is evaluated on a draft command and a snapshot of the state. It never changes
the state. A rule returns one of three outcomes; the rule's override class, its
assurance and the mode decide what that outcome does.
-/

namespace DDD

/-- Three-valued result of a rule. `unknown` names the fact that is missing. -/
inductive Outcome where
  | pass
  | fail
  | unknown (fact : String)
  deriving DecidableEq, Repr

/-- Who a person acts as when they record an override. -/
inductive Authority where
  | administrator
  | counsel
  deriving DecidableEq, Repr

/-- Who may proceed past a blocking rule. Nobody holds `never`. -/
inductive OverrideClass where
  | administrator
  | counsel
  | never
  deriving DecidableEq, Repr

def OverrideClass.rank : OverrideClass → Nat
  | .administrator => 0
  | .counsel => 1
  | .never => 2

/-- Counsel may also clear an administrator-class block. -/
def OverrideClass.satisfiedBy : OverrideClass → Authority → Bool
  | .administrator, _ => true
  | .counsel, .counsel => true
  | _, _ => false

/-- A rule that counsel has not reviewed is informational. -/
inductive Assurance where
  | informational
  | reviewed
  deriving DecidableEq, Repr

inductive Mode where
  | enforcing
  | recording
  deriving DecidableEq, Repr

structure Override where
  rule : String
  authority : Authority
  reason : String
  attestation : String
  deriving Repr

/-- Where a rule comes from. Only the first is law. -/
inductive PolicyKind where
  | legal
  | contract
  | company
  | product
  deriving DecidableEq, Repr

/-- A test case that ships with a rule. -/
structure Case (Ctx S C : Type) where
  ctx : Ctx
  state : S
  cmd : C
  expect : Outcome

/-- A rule over context `Ctx`, state `S` and draft command `C`. `blocks = none` is a
warning; `some k` blocks until someone of class `k` overrides. -/
structure Rule (Ctx S C : Type) where
  id : String
  blocks : Option OverrideClass
  assurance : Assurance
  eval : Ctx → S → C → Outcome
  kind : PolicyKind := .legal
  cite : String := ""
  reviewers : List String := []
  examples : List (Case Ctx S C) := []

variable {Ctx S C : Type}

/-- The class that actually gates a draft. An informational rule gates nothing. -/
def Rule.gate (r : Rule Ctx S C) : Option OverrideClass :=
  match r.assurance with
  | .informational => none
  | .reviewed => r.blocks

inductive FindingKind where
  | violation
  | overridden (authority : Authority) (reason : String)
  | missingFact (fact : String)
  deriving Repr

structure Finding where
  rule : String
  kind : FindingKind
  deriving Repr

inductive Disposition where
  | clear
  | noted (f : Finding)
  | blocked (rule : String) (needs : OverrideClass)
  | needsFact (rule : String) (fact : String)
  deriving Repr

def Disposition.stops : Disposition → Bool
  | .blocked _ _ => true
  | .needsFact _ _ => true
  | _ => false

def Disposition.finding? : Disposition → Option Finding
  | .noted f => some f
  | _ => none

def Disposition.missing? : Disposition → Option String
  | .needsFact _ fact => some fact
  | _ => none

/-- The first override on file for this rule from someone with enough authority. -/
def overriddenBy (ovr : List Override) (id : String) (k : OverrideClass) : Option Override :=
  ovr.find? (fun o => o.rule == id && k.satisfiedBy o.authority)

/-- What one rule's outcome does. -/
def dispose (mode : Mode) (ovr : List Override) (r : Rule Ctx S C) : Outcome → Disposition
  | .pass => .clear
  | .fail =>
    match mode with
    | .recording => .noted ⟨r.id, .violation⟩
    | .enforcing =>
      match r.gate with
      | none => .noted ⟨r.id, .violation⟩
      | some k =>
        match overriddenBy ovr r.id k with
        | some o => .noted ⟨r.id, .overridden o.authority o.reason⟩
        | none => .blocked r.id k
  | .unknown fact =>
    match mode with
    | .recording => .noted ⟨r.id, .missingFact fact⟩
    | .enforcing =>
      match r.gate with
      | none => .noted ⟨r.id, .missingFact fact⟩
      | some _ => .needsFact r.id fact

structure Verdict where
  dispositions : List Disposition
  deriving Repr

def Verdict.proceeds (v : Verdict) : Bool := v.dispositions.all (fun d => !d.stops)
def Verdict.findings (v : Verdict) : List Finding := v.dispositions.filterMap (·.finding?)
def Verdict.missing (v : Verdict) : List String := v.dispositions.filterMap (·.missing?)

def evaluate (rules : List (Rule Ctx S C)) (mode : Mode) (ovr : List Override)
    (ctx : Ctx) (s : S) (c : C) : Verdict :=
  ⟨rules.map (fun r => dispose mode ovr r (r.eval ctx s c))⟩

/-! ## Theorems -/

theorem proceeds_iff {rules : List (Rule Ctx S C)} {mode ovr ctx s c} :
    (evaluate rules mode ovr ctx s c).proceeds = true ↔
      ∀ r ∈ rules, (dispose mode ovr r (r.eval ctx s c)).stops = false := by
  simp [Verdict.proceeds, evaluate, List.all_eq_true]

theorem mem_findings {rules : List (Rule Ctx S C)} {mode ovr ctx s c} {f : Finding} :
    f ∈ (evaluate rules mode ovr ctx s c).findings ↔
      ∃ r ∈ rules, (dispose mode ovr r (r.eval ctx s c)).finding? = some f := by
  simp [Verdict.findings, evaluate, List.mem_filterMap]

/-- In recording mode no rule ever stops a command. -/
theorem dispose_recording (ovr : List Override) (r : Rule Ctx S C) (o : Outcome) :
    (dispose .recording ovr r o).stops = false := by
  cases o <;> simp [dispose, Disposition.stops]

theorem recording_never_stops (rules : List (Rule Ctx S C)) (ovr ctx s c) :
    (evaluate rules .recording ovr ctx s c).proceeds = true :=
  proceeds_iff.mpr (fun r _ => dispose_recording ovr r _)

/-- A rule that counsel has not reviewed can warn but can never block. -/
theorem informational_never_stops (mode : Mode) (ovr : List Override) (r : Rule Ctx S C)
    (o : Outcome) (h : r.assurance = .informational) :
    (dispose mode ovr r o).stops = false := by
  cases o <;> cases mode <;> simp [dispose, Rule.gate, h, Disposition.stops]

/-- No override clears a `never` rule. -/
theorem never_cannot_be_overridden (ovr : List Override) (r : Rule Ctx S C)
    (h : r.gate = some .never) :
    dispose .enforcing ovr r .fail = .blocked r.id .never := by
  have : overriddenBy ovr r.id .never = none := by
    simp [overriddenBy, OverrideClass.satisfiedBy]
  simp [dispose, h, this]

/-- An administrator's override does not clear a counsel-class rule. -/
theorem administrator_cannot_override_counsel (ovr : List Override) (r : Rule Ctx S C)
    (h : r.gate = some .counsel) (ha : ∀ o ∈ ovr, o.authority = .administrator) :
    dispose .enforcing ovr r .fail = .blocked r.id .counsel := by
  have : overriddenBy ovr r.id .counsel = none := by
    simp only [overriddenBy, List.find?_eq_none]
    intro o ho
    simp [ha o ho, OverrideClass.satisfiedBy]
  simp [dispose, h, this]

/-- A failed rule is either blocked or leaves a finding that names the rule. -/
theorem dispose_fail (mode : Mode) (ovr : List Override) (r : Rule Ctx S C) :
    (dispose mode ovr r .fail).stops = true ∨
      ∃ f, (dispose mode ovr r .fail).finding? = some f ∧ f.rule = r.id := by
  cases mode with
  | recording => right; exact ⟨_, rfl, rfl⟩
  | enforcing =>
    simp only [dispose]
    split
    · right; exact ⟨_, rfl, rfl⟩
    · split
      · right; exact ⟨_, rfl, rfl⟩
      · left; rfl

/-- No silent violation: if a command proceeds, every failed rule has left a finding.
This holds in both modes, with or without overrides. -/
theorem no_silent_violation {rules : List (Rule Ctx S C)} {mode ovr ctx s c}
    (hp : (evaluate rules mode ovr ctx s c).proceeds = true)
    {r : Rule Ctx S C} (hr : r ∈ rules) (hf : r.eval ctx s c = .fail) :
    ∃ f ∈ (evaluate rules mode ovr ctx s c).findings, f.rule = r.id := by
  have hs := proceeds_iff.mp hp r hr
  rw [hf] at hs
  rcases dispose_fail mode ovr r with h | ⟨f, h1, h2⟩
  · rw [hs] at h; cases h
  · exact ⟨f, mem_findings.mpr ⟨r, hr, by rw [hf]; exact h1⟩, h2⟩

/-- In enforcing mode with no overrides, a command proceeds only if every gating rule
passed. Unknown stops it as surely as a failure. -/
theorem enforcing_clean {rules : List (Rule Ctx S C)} {ctx s c}
    (hp : (evaluate rules .enforcing [] ctx s c).proceeds = true)
    {r : Rule Ctx S C} (hr : r ∈ rules) (hg : r.gate ≠ none) :
    r.eval ctx s c = .pass := by
  have hs := proceeds_iff.mp hp r hr
  cases ho : r.eval ctx s c with
  | pass => rfl
  | fail =>
    rw [ho] at hs
    cases hk : r.gate with
    | none => exact absurd hk hg
    | some k => simp [dispose, hk, overriddenBy, Disposition.stops] at hs
  | unknown fact =>
    rw [ho] at hs
    cases hk : r.gate with
    | none => exact absurd hk hg
    | some k => simp [dispose, hk, Disposition.stops] at hs

/-- A gating rule with an unknown outcome stops the command and names the fact. -/
theorem unknown_stops (ovr : List Override) (r : Rule Ctx S C) (fact : String)
    (hg : r.gate ≠ none) :
    dispose .enforcing ovr r (.unknown fact) = .needsFact r.id fact := by
  cases hk : r.gate with
  | none => exact absurd hk hg
  | some k => simp [dispose, hk]

/-! ## Raising a rule's class

A company may raise a rule's override class through a setting. It may not lower it. -/

def OverrideClass.max (a b : OverrideClass) : OverrideClass := if a.rank ≤ b.rank then b else a

def OverrideClass.ofRank : Nat → OverrideClass
  | 0 => .administrator
  | 1 => .counsel
  | _ => .never

/-- The rule with its class raised to at least `k`. A warning stays a warning. -/
def Rule.raise (r : Rule Ctx S C) (k : OverrideClass) : Rule Ctx S C :=
  { r with blocks := r.blocks.map (·.max k) }

theorem satisfiedBy_mono {a b : OverrideClass} {who : Authority} (h : a.rank ≤ b.rank)
    (hb : b.satisfiedBy who = true) : a.satisfiedBy who = true := by
  cases a <;> cases b <;> cases who <;> simp_all [OverrideClass.rank, OverrideClass.satisfiedBy]

theorem rank_le_max (a b : OverrideClass) : a.rank ≤ (a.max b).rank := by
  unfold OverrideClass.max; split <;> omega

/-- Raising never lowers: whatever value the setting holds, the class is at least the
rule's own. -/
theorem raise_ge (r : Rule Ctx S C) (k k0 : OverrideClass) (h : r.blocks = some k0) :
    ∃ k1, (r.raise k).blocks = some k1 ∧ k0.rank ≤ k1.rank :=
  ⟨k0.max k, by simp [Rule.raise, h], rank_le_max k0 k⟩

/-- Raising a class never lets through a command the original rule would have stopped. -/
theorem raise_never_loosens (mode : Mode) (ovr : List Override) (r : Rule Ctx S C)
    (k : OverrideClass) (o : Outcome)
    (h : (dispose mode ovr (r.raise k) o).stops = false) :
    (dispose mode ovr r o).stops = false := by
  cases mode with
  | recording => exact dispose_recording ovr r o
  | enforcing =>
    cases ha : r.assurance with
    | informational => exact informational_never_stops _ ovr r o ha
    | reviewed =>
      cases hb : r.blocks with
      | none => cases o <;> simp [dispose, Rule.gate, ha, hb, Disposition.stops]
      | some k0 =>
        have hg : r.gate = some k0 := by simp [Rule.gate, ha, hb]
        have hg' : (r.raise k).gate = some (k0.max k) := by simp [Rule.gate, Rule.raise, ha, hb]
        cases o with
        | pass => rfl
        | unknown fact => simp [dispose, hg', Disposition.stops] at h
        | fail =>
          simp only [dispose, hg, hg'] at h ⊢
          cases h1 : overriddenBy ovr (r.raise k).id (k0.max k) with
          | none => simp [h1, Disposition.stops] at h
          | some ov =>
            have hp := List.find?_some h1
            have hm := List.mem_of_find?_eq_some h1
            simp only [Bool.and_eq_true] at hp
            have : (overriddenBy ovr r.id k0).isSome = true := by
              simp only [overriddenBy, List.find?_isSome]
              exact ⟨ov, hm, by
                simp only [Bool.and_eq_true]
                exact ⟨hp.1, satisfiedBy_mono (rank_le_max k0 k) hp.2⟩⟩
            cases h2 : overriddenBy ovr r.id k0 with
            | none => simp [h2] at this
            | some _ => rfl

/-! ## Publishing a rule -/

/-- Every example that ships with the rule gives the outcome it claims. -/
def Rule.examplesPass (r : Rule Ctx S C) : Bool :=
  r.examples.all (fun e => decide (r.eval e.ctx e.state e.cmd = e.expect))

/-- What a rule needs before it is published in a pack: two passing examples; if it is
law, some way to override it; if it claims review, two reviewers. -/
def Rule.publishable (r : Rule Ctx S C) : Bool :=
  decide (2 ≤ r.examples.length) && r.examplesPass &&
    (decide (r.kind ≠ .legal) || decide (r.blocks ≠ some .never)) &&
    (decide (r.assurance ≠ .reviewed) || decide (2 ≤ r.reviewers.length))

/-- No published legal rule is beyond override. -/
theorem publishable_legal_overridable (r : Rule Ctx S C) (h : r.publishable = true)
    (hk : r.kind = .legal) : r.blocks ≠ some .never := by
  simp only [Rule.publishable, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h.1.2 with h' | h'
  · exact absurd hk h'
  · exact h'

/-- A published rule that blocks has been reviewed by two people. -/
theorem publishable_gate_reviewed (r : Rule Ctx S C) (h : r.publishable = true)
    (hg : r.gate ≠ none) : 2 ≤ r.reviewers.length := by
  simp only [Rule.publishable, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h.2 with h' | h'
  · cases ha : r.assurance with
    | informational => simp [Rule.gate, ha] at hg
    | reviewed => exact absurd ha h'
  · exact h'

end DDD
