/-!
# Reactions

A reaction proposes a command when an event happens. Whether the command is committed
depends on the reaction's mode.
-/

namespace DDD

inductive ReactionMode where
  | automatic
  | confirm
  | off
  deriving DecidableEq, Repr

/-- What kind of thing set the reaction off. -/
inductive Trigger where
  | outsideData
  | termsDate
  | committedFact
  | taxPosition
  deriving DecidableEq, Repr

/-- Default mode by trigger. A setting may change it. -/
def Trigger.defaultMode : Trigger → ReactionMode
  | .outsideData => .confirm
  | .termsDate => .automatic
  | .committedFact => .automatic
  | .taxPosition => .confirm

inductive ReactionResult (C : Type) where
  | commit (c : C)
  | task (c : C)
  | nothing
  deriving Repr

structure Reaction (S E C : Type) where
  name : String
  trigger : Trigger
  propose : S → E → Option C

variable {S E C : Type}

def Reaction.run (r : Reaction S E C) (mode : ReactionMode) (confirmed : Bool) (s : S) (e : E) :
    ReactionResult C :=
  match r.propose s e with
  | none => .nothing
  | some c =>
    match mode with
    | .off => .nothing
    | .automatic => .commit c
    | .confirm => if confirmed then .commit c else .task c

/-- A reaction that is off does nothing. -/
theorem Reaction.off_does_nothing (r : Reaction S E C) (confirmed : Bool) (s : S) (e : E) :
    r.run .off confirmed s e = .nothing := by
  unfold Reaction.run; split <;> rfl

/-- In confirm mode nothing is committed until a person confirms. -/
theorem Reaction.confirm_waits (r : Reaction S E C) (s : S) (e : E) (c : C) :
    r.run .confirm false s e ≠ .commit c := by
  unfold Reaction.run; split <;> simp

/-- Outside data and tax-position changes wait for a person by default. -/
theorem Trigger.outside_data_confirms : Trigger.outsideData.defaultMode = .confirm := rfl
theorem Trigger.tax_position_confirms : Trigger.taxPosition.defaultMode = .confirm := rfl

end DDD
