import DDD.CommandPath

/-!
# Jobs

A job is a list of steps built from a closed set of verbs. The runner executes one step
at a time. Only `commit` can change a stream, and it goes through `submit`, so policy
is evaluated again on the state the command is actually applied to.

A job with no `commit` is a view: it can read, show and notify, and never writes.
-/

namespace DDD

inductive Verb (S C : Type) where
  /-- Propose a fixed command. -/
  | draft (c : C)
  /-- Read a number from the current state into a named variable. -/
  | read (name : String) (f : S → Nat)
  /-- Propose a command built from the variables and the current state. -/
  | draftFrom (f : (String → Nat) → S → C)
  /-- Evaluate policy on the draft. Stops if a needed fact is missing. -/
  | check
  /-- Record an override that the check asked for. -/
  | fulfil (o : Override)
  | sign (party : String)
  | collect (what : String)
  /-- Do nothing until the state satisfies a condition. -/
  | wait (ready : S → Bool)
  /-- `when`: run the next `n` steps only if the condition holds. -/
  | skipUnless (cond : (String → Nat) → S → Bool) (n : Nat)
  /-- Submit the draft. The only verb that writes to the stream. -/
  | commit
  /-- Write a note outside the stream (a refusal, an export record). -/
  | record (note : String)
  /-- Start a follow-on job. -/
  | start (job : String)
  | notify (who : String)
  | present (what : String)

def Verb.isCommit {S C : Type} : Verb S C → Bool
  | .commit => true
  | _ => false

inductive Status where
  | running
  | done
  | stopped (why : String)
  | abandoned
  deriving Repr, DecidableEq

/-- The row a runner keeps for one job. None of it is in the stream. -/
structure Run (S C : Type) where
  todo : List (Verb S C)
  draft : Option C := none
  vars : List (String × Nat) := []
  overrides : List Override := []
  seen : Nat := 0
  status : Status := .running

def Run.var {S C : Type} (r : Run S C) (name : String) : Nat :=
  ((r.vars.find? (fun p => p.1 == name)).map (·.2)).getD 0

/-- Everything outside the run row that a job can touch. -/
structure World (E : Type) where
  log : List E := []
  findings : List Finding := []
  outbox : List String := []
  notes : List String := []
  started : List String := []

structure Env (Ctx S C E X : Type) where
  agg : Aggregate S C E X
  rules : List (Rule Ctx S C)
  mode : Mode
  ctx : Ctx

variable {Ctx S C E X : Type}

/-- `commit`: submit the draft against the version the job last saw. If the stream
has moved, look again and retry; the retry evaluates policy on the new state. -/
def commitStep (env : Env Ctx S C E X) (w : World E) (r : Run S C) (c : C)
    (rest : List (Verb S C)) : World E × Run S C :=
  match submit env.agg env.rules env.mode r.overrides env.ctx w.log r.seen c with
  | .ok (log', fs) => ({ w with log := log', findings := w.findings ++ fs }, { r with todo := rest })
  | .error (.stale _ _) => (w, { r with seen := w.log.length })
  | .error (.policy _) => (w, { r with status := .stopped "blocked by policy" })
  | .error (.impossible _) => (w, { r with status := .stopped "impossible" })

def stepVerb (env : Env Ctx S C E X) (w : World E) (r : Run S C) (v : Verb S C)
    (rest : List (Verb S C)) : World E × Run S C :=
  match v with
  | .draft c => (w, { r with todo := rest, draft := some c })
  | .read name f => (w, { r with todo := rest, vars := (name, f (env.agg.replay w.log)) :: r.vars })
  | .draftFrom f => (w, { r with todo := rest, draft := some (f r.var (env.agg.replay w.log)) })
  | .check =>
    match r.draft with
    | none => (w, { r with status := .stopped "nothing drafted" })
    | some c =>
      match (evaluate env.rules env.mode r.overrides env.ctx (env.agg.replay w.log) c).missing with
      | [] => (w, { r with todo := rest, seen := w.log.length })
      | fact :: _ => (w, { r with status := .stopped ("missing fact: " ++ fact) })
  | .fulfil o => (w, { r with todo := rest, overrides := o :: r.overrides })
  | .sign _ => (w, { r with todo := rest })
  | .collect _ => (w, { r with todo := rest })
  | .wait ready => if ready (env.agg.replay w.log) then (w, { r with todo := rest }) else (w, r)
  | .skipUnless cond n =>
    if cond r.var (env.agg.replay w.log) then (w, { r with todo := rest })
    else (w, { r with todo := rest.drop n })
  | .commit =>
    match r.draft with
    | none => (w, { r with status := .stopped "nothing drafted" })
    | some c => commitStep env w r c rest
  | .record note => ({ w with notes := w.notes ++ [note] }, { r with todo := rest })
  | .start job => ({ w with started := w.started ++ [job] }, { r with todo := rest })
  | .notify who => ({ w with outbox := w.outbox ++ [who] }, { r with todo := rest })
  | .present _ => (w, { r with todo := rest })

def step (env : Env Ctx S C E X) (w : World E) (r : Run S C) : World E × Run S C :=
  match r.status with
  | .running =>
    match r.todo with
    | [] => (w, { r with status := .done })
    | v :: rest => stepVerb env w r v rest
  | _ => (w, r)

def run (env : Env Ctx S C E X) : Nat → World E → Run S C → World E × Run S C
  | 0, w, r => (w, r)
  | n + 1, w, r => run env n (step env w r).1 (step env w r).2

def Run.abandon (r : Run S C) : Run S C := { r with status := .abandoned }

/-- A view is a job with no `commit`. -/
def Run.isView (r : Run S C) : Prop := ∀ v ∈ r.todo, v.isCommit = false

/-! ## Theorems -/

theorem commitStep_log (env : Env Ctx S C E X) (w : World E) (r : Run S C) (c : C)
    (rest : List (Verb S C)) :
    (commitStep env w r c rest).1.log = w.log ∨
      ∃ fs, submit env.agg env.rules env.mode r.overrides env.ctx w.log r.seen c =
        .ok ((commitStep env w r c rest).1.log, fs) := by
  unfold commitStep
  split
  · rename_i log' fs h; right; exact ⟨fs, h⟩
  · left; rfl
  · left; rfl
  · left; rfl

theorem commitStep_todo (env : Env Ctx S C E X) (w : World E) (r : Run S C) (c : C)
    (rest : List (Verb S C)) :
    (commitStep env w r c rest).2.todo = rest ∨ (commitStep env w r c rest).2.todo = r.todo := by
  unfold commitStep
  split
  · left; rfl
  · right; rfl
  · right; rfl
  · right; rfl

theorem stepVerb_log (env : Env Ctx S C E X) (w : World E) (r : Run S C) (v : Verb S C)
    (rest : List (Verb S C)) :
    (stepVerb env w r v rest).1.log = w.log ∨
      ∃ c, v = .commit ∧ r.draft = some c ∧
        stepVerb env w r v rest = commitStep env w r c rest := by
  cases v with
  | commit =>
    simp only [stepVerb]
    split
    · left; rfl
    · rename_i c hd; right; exact ⟨c, trivial, hd, rfl⟩
  | check =>
    simp only [stepVerb]
    split
    · left; rfl
    · split <;> (left; rfl)
  | wait ready => simp only [stepVerb]; split <;> (left; rfl)
  | skipUnless cond n => simp only [stepVerb]; split <;> (left; rfl)
  | _ => left; rfl

theorem stepVerb_todo (env : Env Ctx S C E X) (w : World E) (r : Run S C) (v : Verb S C)
    (rest : List (Verb S C)) (hr : r.todo = v :: rest) :
    ∀ x ∈ (stepVerb env w r v rest).2.todo, x ∈ r.todo := by
  have hrest : ∀ x ∈ rest, x ∈ r.todo := fun x hx => by rw [hr]; exact List.mem_cons_of_mem _ hx
  cases v with
  | commit =>
    simp only [stepVerb]
    split
    · intro x hx; exact hx
    · rename_i c _
      rcases commitStep_todo env w r c rest with h | h
      · rw [h]; exact hrest
      · rw [h]; exact fun x hx => hx
  | check =>
    simp only [stepVerb]
    split
    · intro x hx; exact hx
    · split
      · exact hrest
      · intro x hx; exact hx
  | wait ready =>
    simp only [stepVerb]
    split
    · exact hrest
    · intro x hx; exact hx
  | skipUnless cond n =>
    simp only [stepVerb]
    split
    · exact hrest
    · intro x hx; exact hrest x (List.mem_of_mem_drop hx)
  | _ => exact hrest

/-- A step either leaves the stream alone, or it is a `commit` of the current draft. -/
theorem step_log (env : Env Ctx S C E X) (w : World E) (r : Run S C) :
    (step env w r).1.log = w.log ∨
      ∃ c rest, r.todo = .commit :: rest ∧ r.draft = some c ∧
        step env w r = commitStep env w r c rest := by
  unfold step
  split
  · split
    · left; rfl
    · rename_i v rest ht
      rcases stepVerb_log env w r v rest with h | ⟨c, rfl, hd, hs⟩
      · left; exact h
      · right; exact ⟨c, rest, ht, hd, hs⟩
  · left; rfl

/-- A job's list of steps only ever shrinks. -/
theorem step_todo (env : Env Ctx S C E X) (w : World E) (r : Run S C) :
    ∀ x ∈ (step env w r).2.todo, x ∈ r.todo := by
  unfold step
  split
  · split
    · intro x hx; exact hx
    · rename_i v rest ht; exact stepVerb_todo env w r v rest ht
  · intro x hx; exact hx

/-- Only `commit` writes to the stream. -/
theorem step_writes_only_on_commit (env : Env Ctx S C E X) (w : World E) (r : Run S C)
    (h : ∀ rest, r.todo ≠ .commit :: rest) : (step env w r).1.log = w.log := by
  rcases step_log env w r with h' | ⟨_, rest, ht, _⟩
  · exact h'
  · exact absurd ht (h rest)

/-- A job never rewrites history. -/
theorem step_append_only (env : Env Ctx S C E X) (w : World E) (r : Run S C) :
    w.log <+: (step env w r).1.log := by
  rcases step_log env w r with h | ⟨c, rest, _, _, hs⟩
  · rw [h]; exact List.prefix_refl _
  · rw [hs]
    rcases commitStep_log env w r c rest with h | ⟨fs, h⟩
    · rw [h]; exact List.prefix_refl _
    · exact submit_append_only h

/-- A job only ever produces logs the aggregate accepted. -/
theorem step_committed (env : Env Ctx S C E X) (w : World E) (r : Run S C)
    (hc : env.agg.Committed w.log) : env.agg.Committed (step env w r).1.log := by
  rcases step_log env w r with h | ⟨c, rest, _, _, hs⟩
  · rw [h]; exact hc
  · rw [hs]
    rcases commitStep_log env w r c rest with h | ⟨fs, h⟩
    · rw [h]; exact hc
    · exact submit_committed hc h

theorem run_append_only (env : Env Ctx S C E X) :
    ∀ (n : Nat) (w : World E) (r : Run S C), w.log <+: (run env n w r).1.log
  | 0, _, _ => List.prefix_refl _
  | n + 1, w, r =>
    List.IsPrefix.trans (step_append_only env w r) (run_append_only env n _ _)

theorem run_committed (env : Env Ctx S C E X) :
    ∀ (n : Nat) (w : World E) (r : Run S C),
      env.agg.Committed w.log → env.agg.Committed (run env n w r).1.log
  | 0, _, _, hc => hc
  | n + 1, w, r, hc => run_committed env n _ _ (step_committed env w r hc)

/-- However a job runs, for however long, core invariants hold at the end. -/
theorem run_inv (env : Env Ctx S C E X) {Inv : S → Prop} (hs : env.agg.Sound Inv)
    (n : Nat) (w : World E) (r : Run S C) (hc : env.agg.Committed w.log) :
    Inv (env.agg.replay (run env n w r).1.log) :=
  (run_committed env n w r hc).inv env.agg hs

/-- A job that is not running does nothing. -/
theorem step_inert (env : Env Ctx S C E X) (w : World E) (r : Run S C)
    (h : r.status ≠ .running) : step env w r = (w, r) := by
  unfold step
  split
  · rename_i hr; exact absurd hr h
  · rfl

/-- An abandoned job leaves no trace. -/
theorem abandoned_leaves_no_trace (env : Env Ctx S C E X) (n : Nat) (w : World E)
    (r : Run S C) : (run env n w r.abandon).1 = w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have : step env w r.abandon = (w, r.abandon) := step_inert env w _ (by simp [Run.abandon])
    simp only [run, this]
    exact ih

theorem step_view (env : Env Ctx S C E X) (w : World E) (r : Run S C) (h : r.isView) :
    (step env w r).2.isView ∧ (step env w r).1.log = w.log := by
  refine ⟨fun v hv => h v (step_todo env w r v hv), ?_⟩
  apply step_writes_only_on_commit
  intro rest ht
  have := h .commit (by rw [ht]; exact List.mem_cons_self)
  cases this

/-- A view never writes to the stream, however long it runs. -/
theorem view_never_writes (env : Env Ctx S C E X) :
    ∀ (n : Nat) (w : World E) (r : Run S C), r.isView → (run env n w r).1.log = w.log
  | 0, _, _, _ => rfl
  | n + 1, w, r, h => by
    have hs := step_view env w r h
    simp only [run]
    rw [view_never_writes env n _ _ hs.1, hs.2]

end DDD
