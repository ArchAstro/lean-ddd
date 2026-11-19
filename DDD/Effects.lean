/-!
# Post-commit effects

After a command is committed, post-commit rules look at the new state and the events
and produce effects: deadlines, classifications, things to mark stale. Effects go to a
compliance record. They are never events, so they cannot change the stream.
-/

namespace DDD

inductive Effect where
  | obligation (kind : String) (subject : Nat) (due : Nat)
  | classify (subject : Nat) (label : String) (amount : Nat)
  | invalidate (what : String)
  | warn (text : String)
  deriving Repr, DecidableEq

structure PostRule (Ctx S E : Type) where
  id : String
  react : Ctx → S → E → List Effect

variable {Ctx S E : Type}

/-- All effects of a batch of committed events, tagged with the rule that produced them.
`s` is the state after the commit. -/
def afterCommit (rules : List (PostRule Ctx S E)) (ctx : Ctx) (s : S) (es : List E) :
    List (String × Effect) :=
  es.flatMap (fun e => rules.flatMap (fun r => (r.react ctx s e).map (fun x => (r.id, x))))

structure Obligation where
  rule : String
  kind : String
  subject : Nat
  due : Nat
  done : Bool := false
  deriving Repr, DecidableEq

/-- The compliance record. -/
structure Compliance where
  obligations : List Obligation := []
  classifications : List (Nat × String × Nat) := []
  stale : List String := []
  warnings : List String := []
  deriving Repr

def Compliance.absorbOne (c : Compliance) (x : String × Effect) : Compliance :=
  match x.2 with
  | .obligation kind subject due =>
    { c with obligations := c.obligations ++ [{ rule := x.1, kind, subject, due }] }
  | .classify subject label amount =>
    { c with classifications := c.classifications ++ [(subject, label, amount)] }
  | .invalidate what => { c with stale := c.stale ++ [what] }
  | .warn text => { c with warnings := c.warnings ++ [text] }

def Compliance.absorb (c : Compliance) (xs : List (String × Effect)) : Compliance :=
  xs.foldl Compliance.absorbOne c

/-- Mark the obligations of one kind for one subject as met. -/
def Compliance.complete (c : Compliance) (kind : String) (subject : Nat) : Compliance :=
  { c with obligations := c.obligations.map (fun o =>
      if o.kind = kind ∧ o.subject = subject then { o with done := true } else o) }

def Compliance.overdue (c : Compliance) (today : Nat) : List Obligation :=
  c.obligations.filter (fun o => !o.done && decide (o.due < today))

theorem absorbOne_keeps (c : Compliance) (x : String × Effect) :
    c.obligations <+: (c.absorbOne x).obligations := by
  unfold Compliance.absorbOne
  split
  · exact List.prefix_append _ _
  · exact List.prefix_refl _
  · exact List.prefix_refl _
  · exact List.prefix_refl _

/-- Effects only ever add obligations. None is dropped or rewritten. -/
theorem absorb_keeps (xs : List (String × Effect)) (c : Compliance) :
    c.obligations <+: (c.absorb xs).obligations := by
  induction xs generalizing c with
  | nil => exact List.prefix_refl _
  | cons x xs ih =>
    exact List.IsPrefix.trans (absorbOne_keeps c x) (ih (c.absorbOne x))

/-- A deadline that has passed stays overdue until someone records it as met. -/
theorem overdue_until_done (c : Compliance) (o : Obligation) (today later : Nat)
    (h : o ∈ c.overdue today) (hl : today ≤ later) : o ∈ c.overdue later := by
  simp only [Compliance.overdue, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, h.2.1, by omega⟩

/-- With no post-commit rules there are no effects. -/
theorem afterCommit_nil (ctx : Ctx) (s : S) (es : List E) :
    afterCommit ([] : List (PostRule Ctx S E)) ctx s es = [] := by
  simp [afterCommit]

/-- Replaying nothing produces nothing: effects come only from committed events. -/
theorem afterCommit_no_events (rules : List (PostRule Ctx S E)) (ctx : Ctx) (s : S) :
    afterCommit rules ctx s [] = [] := rfl

end DDD
