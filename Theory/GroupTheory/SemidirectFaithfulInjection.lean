module
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Injectivity from the normal factor of a faithful semidirect product

Let an arbitrary group A act faithfully by automorphisms on an abelian
group N. A homomorphism from N semidirect A to a group B is injective
whenever its restriction to the canonical copy of N is injective. No
finiteness, prime-order or solvability hypothesis is needed.

For a kernel element x, conjugation of the canonical left element n is
the canonical left element given by the action of x.right on n; the left
coordinate of x disappears because N is abelian. Applying the homomorphism
and injectivity on N shows that x.right acts trivially. Faithfulness gives
x.right=1. The element x therefore belongs to the canonical copy of N,
where the homomorphism's injectivity forces x=1.

The proof uses the multiplication and inclusion formulas of Mathlib's
`GroupTheory.SemidirectProduct`. This general kernel criterion supports
transport of the faithful C5 semidirect C4 quotient action in Parrott's
1972 Tits-group argument, independently of that finite-group application.
-/

namespace SemidirectProduct

/-- A homomorphism out of a faithful abelian semidirect product is injective if its left restriction is. -/
public theorem injective_of_left_injective
    {N A B : Type*} [CommGroup N] [Group A] [Group B]
    {φ : A →* MulAut N} (hφ : Function.Injective φ)
    (f : N ⋊[φ] A →* B) (hleft : Function.Injective (f.comp inl)) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  have hfx : f x = 1 := hx
  have haction (n : N) : φ x.right n = n := by
    apply hleft
    change f (inl (φ x.right n)) = f (inl n)
    have hconj : x * inl n * x⁻¹ = inl (φ x.right n) := by
      ext <;> simp [mul_assoc, mul_comm]
    rw [← hconj, map_mul, map_mul, map_inv, hfx]
    simp
  have hright : x.right = 1 := by
    apply hφ
    rw [map_one]
    exact MulEquiv.ext haction
  have hxleft : x = inl x.left := by
    ext <;> simp [hright]
  have hleftone : x.left = 1 := by
    apply hleft
    change f (inl x.left) = f (inl 1)
    rw [← hxleft, hfx, map_one, map_one]
  exact Subgroup.mem_bot.mpr (by rw [hxleft, hleftone, map_one])

end SemidirectProduct
