module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card

/-!
# The sixteen even words on five coordinates

Flipping all coordinates except one preserves parity. Every even word is
zero, one such flip of zero, or two such flips of zero. These finite binary
identities involve only five coordinates and are kernel-checked directly;
the arbitrary-graph recognition is proved structurally in the companion
modules. The identities provide its actual sixteen-point coordinate set.
-/

@[expose] public section
namespace Theory.Combinatorics.QuadrangleTwentySeven
abbrev Word := Fin 5→Bool
def EvenWordPred (w:Word) : Prop := (Finset.univ.filter fun i=>w i).card%2=0
abbrev EvenWord := {w:Word // EvenWordPred w}
def zeroWord:Word:=fun _=>false
def flip (i:Fin 5) (w:Word) : Word := fun j=>if j=i then w j else !(w j)
instance (w:Word):Decidable (EvenWordPred w) := inferInstanceAs (Decidable (_%_=0))

theorem even_card : Fintype.card EvenWord=16 := by decide

theorem zero_even : EvenWordPred zeroWord := by decide

theorem flip_even : ∀i w,EvenWordPred w→EvenWordPred (flip i w) := by decide

theorem even_cases : ∀w,EvenWordPred w→
    w=zeroWord ∨ (∃i,w=flip i zeroWord) ∨ (∃i j,i≠j ∧w=flip i (flip j zeroWord)) := by decide

theorem flip_involutive (i:Fin 5) : Function.Involutive (flip i) := by
  intro w
  funext j
  by_cases hj:j=i <;> simp [flip,hj]

theorem flip_ne : ∀i w,flip i w≠w := by decide

theorem even_has_equal_coordinate : ∀v w,EvenWordPred v→EvenWordPred w→∃i,v i=w i := by decide
end Theory.Combinatorics.QuadrangleTwentySeven
