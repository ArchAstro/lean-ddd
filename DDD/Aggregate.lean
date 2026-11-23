/-!
# Aggregates

An aggregate is a consistency boundary: a state, a way to decide whether a command is
possible, and a way to fold the resulting events into the state.

* `decide` is pure. It never performs a side effect and never changes the state.
* `evolve` is total. Replaying a log can never fail.
* The state is always `replay log`, so the log is the only source of truth.
-/

namespace DDD

/-- State `S`, commands `C`, events `E`, rejection reasons `X`. -/
structure Aggregate (S C E X : Type) where
  init : S
  decide : S → C → Except X (List E)
  evolve : S → E → S

namespace Aggregate

variable {S C E X : Type} (agg : Aggregate S C E X)

/-- Apply events to a state, in order. -/
def fold (s : S) (es : List E) : S := es.foldl agg.evolve s

/-- The state of a stream is a pure function of its log. -/
def replay (log : List E) : S := agg.fold agg.init log

@[simp] theorem fold_nil (s : S) : agg.fold s [] = s := rfl

theorem fold_append (s : S) (xs ys : List E) :
    agg.fold s (xs ++ ys) = agg.fold (agg.fold s xs) ys := by
  simp [fold, List.foldl_append]

/-- A snapshot plus the events after it gives the same state as a full replay. -/
theorem snapshot_correct (xs ys : List E) :
    agg.replay (xs ++ ys) = agg.fold (agg.replay xs) ys :=
  agg.fold_append _ xs ys

/-- An invariant is sound when the empty stream satisfies it and every accepted command
keeps it. This is the only proof obligation a domain model owes the framework. -/
structure Sound (Inv : S → Prop) : Prop where
  init : Inv agg.init
  step : ∀ s c es, Inv s → agg.decide s c = .ok es → Inv (agg.fold s es)

/-- Logs that can be produced by accepted commands only. -/
inductive Committed : List E → Prop
  | nil : Committed []
  | step {log : List E} {c : C} {es : List E} :
      Committed log → agg.decide (agg.replay log) c = .ok es → Committed (log ++ es)

/-- Every state reachable through accepted commands satisfies a sound invariant. -/
theorem Committed.inv {Inv : S → Prop} (h : agg.Sound Inv) {log : List E}
    (hc : agg.Committed log) : Inv (agg.replay log) := by
  induction hc with
  | nil => exact h.init
  | step _ hd ih =>
    rw [snapshot_correct]
    exact h.step _ _ _ ih hd

/-! ## Atomic batches -/

/-- Decide a list of commands as one unit. Each command sees the effect of the ones
before it. One failure rejects the whole batch. -/
def decideAll : S → List C → Except X (List E)
  | _, [] => .ok []
  | s, c :: cs =>
    match agg.decide s c with
    | .error x => .error x
    | .ok es =>
      match decideAll (agg.fold s es) cs with
      | .error x => .error x
      | .ok rest => .ok (es ++ rest)

/-- The same aggregate, taking batches as its command. -/
def batch : Aggregate S (List C) E X where
  init := agg.init
  decide := agg.decideAll
  evolve := agg.evolve

theorem decideAll_inv {Inv : S → Prop} (h : agg.Sound Inv) :
    ∀ (cs : List C) (s : S) (es : List E),
      Inv s → agg.decideAll s cs = .ok es → Inv (agg.fold s es)
  | [], s, es, hs, hd => by
    simp [decideAll] at hd
    subst hd
    simpa using hs
  | c :: cs, s, es, hs, hd => by
    simp only [decideAll] at hd
    split at hd
    · cases hd
    · rename_i es1 h1
      split at hd
      · cases hd
      · rename_i rest h2
        cases hd
        rw [fold_append]
        exact decideAll_inv h cs _ _ (h.step _ _ _ hs h1) h2

/-- Batching keeps every sound invariant. -/
theorem batch_sound {Inv : S → Prop} (h : agg.Sound Inv) : agg.batch.Sound Inv where
  init := h.init
  step := fun s cs es hs hd => agg.decideAll_inv h cs s es hs hd

/-- A rejected batch produces no events at all. -/
theorem batch_atomic (s : S) (cs : List C) (x : X) (h : agg.decideAll s cs = .error x) :
    ∀ es, agg.decideAll s cs ≠ .ok es := by
  intro es h'; rw [h] at h'; cases h'

end Aggregate

/-! ## A state type that is an aggregate

`Aggregate` is a record of functions over four types. A domain usually has one state type
per aggregate, so the state type can carry the rest: its commands, events, rejections and
the three functions. `Aggregate.of S` is then the record, and every theorem above applies.
-/

/-- The state type `S` is an aggregate: it names its commands, events and rejection
reasons, and says how to start, decide and evolve. -/
class AggregateRoot (S : Type) where
  /-- Commands. -/
  Cmd : Type
  /-- Events. -/
  Evt : Type
  /-- Rejection reasons. -/
  Err : Type
  init : S
  decide : S → Cmd → Except Err (List Evt)
  evolve : S → Evt → S

/-- The aggregate of a state type. -/
@[reducible] def Aggregate.of (S : Type) [AggregateRoot S] :
    Aggregate S (AggregateRoot.Cmd S) (AggregateRoot.Evt S) (AggregateRoot.Err S) where
  init := AggregateRoot.init
  decide := AggregateRoot.decide
  evolve := AggregateRoot.evolve

namespace Aggregate

variable (S : Type) [AggregateRoot S]

@[simp] theorem of_init : (Aggregate.of S).init = AggregateRoot.init := rfl

@[simp] theorem of_decide (s : S) (c : AggregateRoot.Cmd S) :
    (Aggregate.of S).decide s c = AggregateRoot.decide s c := rfl

@[simp] theorem of_evolve (s : S) (e : AggregateRoot.Evt S) :
    (Aggregate.of S).evolve s e = AggregateRoot.evolve s e := rfl

end Aggregate
end DDD
