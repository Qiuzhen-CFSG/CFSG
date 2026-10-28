module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Data

/-!
# Schreier words for the literal six-relator presentation

The tree representatives and signed non-tree edges define 367 words: the two
protected max3 generators and 365 actual Schreier elements. Free-word checks
identify every edge with its label; telescoping then supplies the relations
needed by the independent subgroup-generation argument. No permutation
faithfulness, finite order, or subgroup-membership assertion is encoded here.

Source: `../source/Discover.g`, the retained table, and elementary Schreier rewriting.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover
open Subgroup.CosetWordCertificate

abbrev Label := Fin 367

def letterCode (a : Letter Bool) : Nat :=
  (if a.1 then 2 else 0) + (if a.2 then 0 else 1)

def next (i : Nat) (a : Letter Bool) : Nat :=
  destinations (4 * i + letterCode a) % 364

def dest (i : Fin 364) (a : Letter Bool) : Fin 364 :=
  ⟨next i a, Nat.mod_lt _ (by decide)⟩

def edgeWord (i : Nat) (a : Letter Bool) : Word Label :=
  let c := edgeCodes (4 * i + letterCode a)
  if c = 0 then [] else [(⟨((c - 1) / 2) % 367, Nat.mod_lt _ (by decide)⟩,
    c % 2 == 1)]

def schreierWord (i : Nat) (a : Letter Bool) : Word Bool :=
  repWord i ++ [a] ++ FreeGroup.invRev (repWord (next i a))

def rawWord (k : Label) : Word Bool :=
  if k.val = 0 then boundLetters false else
  if k.val = 1 then boundLetters true else
    schreierWord (choices k.val).1 (choices k.val).2

def rawGenerator (k : Label) : Presentation.Presented :=
  eval Presentation.generator (rawWord k)

def protectedLabel (b : Bool) : Label := ⟨if b then 1 else 0, by cases b <;> decide⟩

theorem rawGenerator_protected (b : Bool) :
    rawGenerator (protectedLabel b) = boundGenerator b := by
  cases b <;> exact eval_boundLetters _

/-- Substitute each signed label by its literal word in the original pair. -/
def expand : Word Label → Word Bool
  | [] => []
  | (k, b) :: w => (if b then rawWord k else FreeGroup.invRev (rawWord k)) ++ expand w

theorem eval_expand (w : Word Label) :
    eval Presentation.generator (expand w) = eval rawGenerator w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨k, b⟩
    cases b <;> simp [expand, eval_append, eval_cons, eval_invRev, ih, rawGenerator]

def representative (i : Nat) : Presentation.Presented := eval Presentation.generator (repWord i)

/-- This finite check certifies an equality in the free group, not an action. -/
def edgeCheck (i : Nat) (a : Letter Bool) : Bool :=
  decide (reduce (expand (edgeWord i a)) = reduce (schreierWord i a))

theorem edge_sound_of_check (i : Nat) (a : Letter Bool) (h : edgeCheck i a = true) :
    eval rawGenerator (edgeWord i a) =
      edgeElement representative Presentation.generator i a (next i a) := by
  have hc : reduce (expand (edgeWord i a)) = reduce (schreierWord i a) := by
    simpa only [edgeCheck, decide_eq_true_eq] using h
  have he := congrArg (eval Presentation.generator) hc
  simpa only [eval_reduce, eval_expand, schreierWord, eval_append, eval_invRev,
    edgeElement, representative] using he

def rawTrace (i : Nat) : Word Bool → Word Label
  | [] => []
  | a :: w => edgeWord i a ++ rawTrace (next i a) w

/-- All six source words at every vertex, and the two protected word equations. -/
def RawRelations {G : Type*} [Group G] (x : Label → G) : Prop :=
  (∀ (i : Fin 364) (r : Fin 6), eval x (rawTrace i (relatorLetters r)) = 1) ∧
  (∀ b, eval x (rawTrace 0 (boundLetters b)) = x (protectedLabel b))

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover
