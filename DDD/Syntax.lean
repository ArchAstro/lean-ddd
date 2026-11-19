import DDD.Job

/-!
# Rule and job syntax

Rules and jobs are written in Lean itself. These macros give them the shape used in
the design documents and expand to the plain structures, so everything proved about
`Rule`, `Verb` and `Run` applies to what is written here.
-/

namespace DDD

/-! ## Jobs -/

/-- `when c then s`: skip the steps of `s` unless `c` holds. -/
def whenThen {S C : Type} (c : (String → Nat) → S → Bool) (s : List (Verb S C)) :
    List (Verb S C) :=
  .skipUnless c s.length :: s

declare_syntax_cat jobstep (behavior := both)
syntax &"draft" term:max : jobstep
syntax &"read" str " := " term:max : jobstep
syntax &"draft_from" term:max : jobstep
syntax &"check" : jobstep
syntax &"fulfil" term:max : jobstep
syntax &"sign" str : jobstep
syntax &"collect" str : jobstep
syntax &"wait" term:max : jobstep
syntax &"commit" : jobstep
syntax &"record" str : jobstep
syntax &"start" str : jobstep
syntax &"notify" str : jobstep
syntax &"present" str : jobstep
syntax &"when" term:max &"then" jobstep : jobstep

syntax "step% " jobstep : term
syntax "steps![" jobstep,* "]" : term

macro_rules
  | `(step% draft $t) => `([Verb.draft $t])
  | `(step% read $n := $f) => `([Verb.read $n $f])
  | `(step% draft_from $f) => `([Verb.draftFrom $f])
  | `(step% check) => `([Verb.check])
  | `(step% fulfil $o) => `([Verb.fulfil $o])
  | `(step% sign $p) => `([Verb.sign $p])
  | `(step% collect $w) => `([Verb.collect $w])
  | `(step% wait $f) => `([Verb.wait $f])
  | `(step% commit) => `([Verb.commit])
  | `(step% record $n) => `([Verb.record $n])
  | `(step% start $j) => `([Verb.start $j])
  | `(step% notify $w) => `([Verb.notify $w])
  | `(step% present $w) => `([Verb.present $w])
  | `(step% when $c then $s) => `(whenThen $c (step% $s))

macro_rules
  | `(steps![]) => `([])
  | `(steps![$s]) => `(step% $s)
  | `(steps![$s, $ss,*]) => `((step% $s) ++ steps![$ss,*])

/-! ## Rules -/

declare_syntax_cat rulekind (behavior := both)
syntax &"law" : rulekind
syntax &"contract" : rulekind
syntax &"company" : rulekind
syntax &"product" : rulekind

declare_syntax_cat ruleeffect (behavior := both)
syntax &"warn" : ruleeffect
syntax &"deny" : ruleeffect
syntax &"deny_unless_administrator" : ruleeffect
syntax &"deny_unless_counsel" : ruleeffect

declare_syntax_cat ruleassurance (behavior := both)
syntax &"informational" : ruleassurance
syntax &"reviewed_by" term:max : ruleassurance

syntax "rulekind% " rulekind : term
syntax "ruleeffect% " ruleeffect : term
macro_rules
  | `(rulekind% law) => `(PolicyKind.legal)
  | `(rulekind% contract) => `(PolicyKind.contract)
  | `(rulekind% company) => `(PolicyKind.company)
  | `(rulekind% product) => `(PolicyKind.product)
macro_rules
  | `(ruleeffect% warn) => `((none : Option OverrideClass))
  | `(ruleeffect% deny) => `(some OverrideClass.never)
  | `(ruleeffect% deny_unless_administrator) => `(some OverrideClass.administrator)
  | `(ruleeffect% deny_unless_counsel) => `(some OverrideClass.counsel)

/-- `rule! "id" law cite "source" require cond else effect assurance`, where `cond`
takes the context, the state and the draft and says whether the draft is acceptable. -/
syntax "rule! " str rulekind &"cite" str &"require" term:max " else " ruleeffect
  ruleassurance : term

macro_rules
  | `(rule! $id $k cite $c require $f else $e informational) =>
    `({ id := $id, kind := rulekind% $k, cite := $c, blocks := ruleeffect% $e,
        assurance := Assurance.informational,
        eval := fun ctx st t => if $f ctx st t then Outcome.pass else Outcome.fail })
  | `(rule! $id $k cite $c require $f else $e reviewed_by $r) =>
    `({ id := $id, kind := rulekind% $k, cite := $c, blocks := ruleeffect% $e,
        assurance := Assurance.reviewed, reviewers := $r,
        eval := fun ctx st t => if $f ctx st t then Outcome.pass else Outcome.fail })

end DDD
