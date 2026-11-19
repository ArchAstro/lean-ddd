import Lean

/-!
# Stored form

How a value is written down and read back: as a flat list of numbers and strings.

`Codec α` carries the two directions and the proof that reading what was written gives
the value back, whatever follows it. `derive_codec T` builds the instance, proof
included, for a structure or an inductive type whose fields all have one.
-/

namespace DDD

/-- One stored token. -/
inductive Tok where
  | n (value : Nat)
  | s (text : String)
  deriving DecidableEq, Repr

class Codec (α : Type) where
  enc : α → List Tok
  dec : List Tok → Option (α × List Tok)
  /-- Reading what was written returns the value and leaves the rest untouched. -/
  law : ∀ (a : α) (rest : List Tok), dec (enc a ++ rest) = some (a, rest)

attribute [simp] Codec.law

namespace Codec

instance : Codec Nat where
  enc a := [.n a]
  dec | .n a :: r => some (a, r) | _ => none
  law := by intro a rest; rfl

instance : Codec String where
  enc a := [.s a]
  dec | .s a :: r => some (a, r) | _ => none
  law := by intro a rest; rfl

instance : Codec Bool where
  enc a := [.n (if a then 1 else 0)]
  dec | .n 0 :: r => some (false, r) | .n 1 :: r => some (true, r) | _ => none
  law := by intro a rest; cases a <;> rfl

instance [Codec α] : Codec (Option α) where
  enc | none => [.n 0] | some a => .n 1 :: enc a
  dec
    | .n 0 :: r => some (none, r)
    | .n 1 :: r => (dec r).bind fun p => some (some p.1, p.2)
    | _ => none
  law := by intro a rest; cases a <;> simp

instance [Codec α] [Codec β] : Codec (α × β) where
  enc p := enc p.1 ++ enc p.2
  dec ts := (dec ts).bind fun p => (dec p.2).bind fun q => some ((p.1, q.1), q.2)
  law := by intro a rest; simp [List.append_assoc]

/-- Read `k` values in a row. -/
def decN [Codec α] : Nat → List Tok → Option (List α × List Tok)
  | 0, r => some ([], r)
  | k + 1, r => (dec r).bind fun p => (decN k p.2).bind fun q => some (p.1 :: q.1, q.2)

def encAll [Codec α] : List α → List Tok
  | [] => []
  | a :: l => enc a ++ encAll l

theorem decN_encAll [Codec α] (l : List α) (rest : List Tok) :
    decN l.length (encAll l ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [encAll, decN, List.append_assoc, ih]

/-- A list is its length, then its items. -/
instance [Codec α] : Codec (List α) where
  enc l := .n l.length :: encAll l
  dec | .n k :: r => decN k r | _ => none
  law := by intro a rest; simp [decN_encAll]

/-- Write a whole value. -/
def write [Codec α] (a : α) : List Tok := enc a

/-- Read a whole value: nothing may be left over. -/
def read [Codec α] (ts : List Tok) : Option α :=
  match dec (α := α) ts with
  | some (a, []) => some a
  | _ => none

/-- **Round trip**: what is written reads back as itself. -/
theorem read_write [Codec α] (a : α) : read (write a) = some a := by
  have h := Codec.law a []
  simp only [List.append_nil] at h
  simp [read, write, h]

end Codec

open Lean Elab Command in
/-- `derive_codec T₁ T₂ …` builds `Codec` instances, with their proofs. A value is stored as
its constructor's number followed by its fields in order. -/
elab "derive_codec " ids:ident+ : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let .inductInfo info ← getConstInfo name | throwError "{name} is not a structure or inductive type"
    let mut encArms := ""
    let mut decArms := ""
    let mut i := 0
    for c in info.ctors do
      let .ctorInfo ci ← getConstInfo c | throwError "{c}?"
      let k := ci.numFields
      let xs := (List.range k).map fun j => s!"x{j}"
      let body := xs.foldr (fun x acc => s!"(DDD.Codec.enc {x} ++ {acc})") "[]"
      encArms := encArms ++ s!"\n    | @{c} {" ".intercalate xs} => DDD.Tok.n {i} :: {body}"
      let args := " ".intercalate ((List.range k).map fun j => s!"p{j}.1")
      let last := if k = 0 then "r" else s!"p{k - 1}.2"
      let mut d := s!"some (@{c} {args}, {last})"
      for j in (List.range k).reverse do
        let src := if j = 0 then "r" else s!"p{j - 1}.2"
        d := s!"(DDD.Codec.dec {src}).bind fun p{j} => {d}"
      decArms := decArms ++ s!"\n    | DDD.Tok.n {i} :: r => {d}"
      i := i + 1
    let src := s!"instance : DDD.Codec {name} where\n  enc a := match a with{encArms}\n  dec ts := match ts with{decArms}\n    | _ => none\n  law := by intro a rest; cases a <;> simp [List.append_assoc]"
    match Parser.runParserCategory (← getEnv) `command src with
    | .ok stx => elabCommand stx
    | .error e => throwError "derive_codec {name}: {e}\n{src}"

end DDD
