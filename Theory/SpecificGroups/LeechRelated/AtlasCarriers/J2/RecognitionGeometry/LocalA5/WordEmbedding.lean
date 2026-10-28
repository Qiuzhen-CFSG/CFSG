module

public import Theory.GroupTheory.WordSubgroup

/-!
# Homomorphisms certified on word generators

To check a finite word-defined map, it suffices to check left multiplication
by the generators and that the chosen words cover the source. Word induction
then proves the whole multiplication law. This is used for the two actual
A₅ embeddings in the Hall–Janko local geometry, avoiding quadratic tables.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Theory.GroupTheory

/-- Extend checked generator transitions to the full multiplication law. -/
@[expose] def homOfWordTransitions {G H : Type*} [Group G] [Group H] {n : Nat}
    (gs : Fin n → G) (hs : Fin n → H) (word : G → List (Fin n))
    (f : G → H) (hword : ∀ g, evalWord gs (word g) = g)
    (hone : f 1 = 1) (hstep : ∀ i g, f (gs i * g) = hs i * f g) : G →* H where
  toFun := f
  map_one' := hone
  map_mul' p q := by
    have hw (w : List (Fin n)) (q : G) :
        f (evalWord gs w * q) = evalWord hs w * f q := by
      induction w with
      | nil => simp only [evalWord, one_mul]
      | cons i w ih =>
        simp only [evalWord, mul_assoc, hstep, ih]
    have hp : f p = evalWord hs (word p) := by
      simpa only [hword, mul_one, hone] using hw (word p) 1
    rw [← hword p, hw, hword, hp]

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
