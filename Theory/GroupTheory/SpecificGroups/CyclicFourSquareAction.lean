module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Tactic

/-!
# An order-three action on the square of the cyclic group of order four

Let `B` swap the two coordinates. If an endomorphism `A` satisfies
`A³ = 1`, `BABA = 1`, and sends `(2,2)` to `(2,0)`, then its matrix is
one of `[[0,3],[1,3]]` and `[[0,1],[3,3]]`. In particular its values on
`(1,1)` and `(3,1)` have precisely the two alternatives below.

An endomorphism is determined by the two coordinate generators. The finite
calculation checks their 256 possible image pairs in the kernel, then the
homomorphism law gives the stated values. This supplies the coordinate step
in Fong (1967), p. 70, before equation (5).
-/

/-- The product of two multiplicatively written cyclic groups of order four. -/
public abbrev CyclicFourSquare := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

namespace CyclicFourSquare

/-- A pair of residues, viewed as an element of the multiplicative product. -/
@[expose] public def coord (i j : ZMod 4) : CyclicFourSquare :=
  (Multiplicative.ofAdd i, Multiplicative.ofAdd j)

private def lin (a b x : CyclicFourSquare) : CyclicFourSquare := a ^ x.1.toAdd.val * b ^ x.2.toAdd.val

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
private theorem finite_calculation (a b : CyclicFourSquare)
    (h3s : lin a b (lin a b a) = coord 1 0)
    (h3t : lin a b (lin a b b) = coord 0 1)
    (hbs : (lin a b a.swap).swap = coord 1 0)
    (hbt : (lin a b b.swap).swap = coord 0 1)
    (hj : lin a b (coord 2 2) = coord 2 0) :
    (a = coord 0 1 ∧ b = coord 3 3) ∨ (a = coord 0 3 ∧ b = coord 1 3) := by
  revert h3s h3t hbs hbt hj a b
  decide +kernel

private theorem linear_apply (f : CyclicFourSquare →* CyclicFourSquare) (x : CyclicFourSquare) :
    f x = lin (f (coord 1 0)) (f (coord 0 1)) x := by
  have hx : x = (coord 1 0) ^ x.1.toAdd.val * (coord 0 1) ^ x.2.toAdd.val := by
    revert x
    decide +kernel
  calc
    f x = f ((coord 1 0) ^ x.1.toAdd.val * (coord 0 1) ^ x.2.toAdd.val) := congrArg f hx
    _ = _ := by rw [map_mul, map_pow, map_pow]; rfl

set_option synthInstance.maxSize 1024 in
/-- The two possible images of the diagonal and the inverse antidiagonal. -/
public theorem action_images_of_cube_swap (f : CyclicFourSquare →* CyclicFourSquare)
    (hcube : ∀ x, f (f (f x)) = x)
    (hswap : ∀ x, (f (f x).swap).swap = x)
    (hj : f (coord 2 2) = coord 2 0) :
    (f (coord 1 1) = coord 3 0 ∧ f (coord 3 1) = coord 3 2) ∨
    (f (coord 1 1) = coord 1 2 ∧ f (coord 3 1) = coord 1 0) := by
  have ha := hcube (coord 1 0)
  have hb := hcube (coord 0 1)
  have hsa := hswap (coord 1 0)
  have hsb := hswap (coord 0 1)
  rw [linear_apply f (f (f (coord 1 0))), linear_apply f (f (coord 1 0))] at ha
  rw [linear_apply f (f (f (coord 0 1))), linear_apply f (f (coord 0 1))] at hb
  rw [linear_apply f (f (coord 1 0)).swap] at hsa
  rw [linear_apply f (f (coord 0 1)).swap] at hsb
  rw [linear_apply] at hj
  rcases finite_calculation _ _ ha hb hsa hsb hj with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · left
    rw [linear_apply f (coord 1 1), linear_apply f (coord 3 1), hs, ht]
    decide +kernel
  · right
    rw [linear_apply f (coord 1 1), linear_apply f (coord 3 1), hs, ht]
    decide +kernel

end CyclicFourSquare
