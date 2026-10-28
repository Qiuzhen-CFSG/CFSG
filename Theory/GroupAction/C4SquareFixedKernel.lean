module

public import Theory.GroupTheory.PGroup.C4SquareBasis

/-!
# The automorphisms of a C₄-square fixing its involutions

The kernel of the action on square-one elements is elementary abelian.
For an automorphism in this kernel, each displacement has square one and
is therefore fixed by every other kernel element. This gives both the
commutation and square identities without an enumeration of automorphisms.

Source: the congruence kernel in Aut(C₄ × C₄), used in MacWilliams,
Trans. AMS 150 (1970), §2 and §4; compare Janko–Thompson (1970), 1.4(c).
-/

namespace C4SquareExtension

private theorem fourth_power (x : Model) : x ^ 4 = 1 := by
  exact (by decide : ∀ y : Model, y ^ 4 = 1) x

private theorem displacement_square (f : MulAut Model)
    (hf : ∀ x : Model, x ^ 2 = 1 → f x = x) (x : Model) :
    (f x * x⁻¹) ^ 2 = 1 := by
  rw [mul_pow, ← map_pow, hf (x ^ 2) (by rw [← pow_mul]; exact fourth_power x),
    inv_pow, mul_inv_cancel]

private theorem apply_apply (f g : MulAut Model)
    (hf : ∀ x : Model, x ^ 2 = 1 → f x = x)
    (hg : ∀ x : Model, x ^ 2 = 1 → g x = x) (x : Model) :
    f (g x) = f x * (g x * x⁻¹) := by
  have h := hf _ (displacement_square g hg x)
  rw [map_mul, map_inv] at h
  calc
    f (g x) = (f (g x) * (f x)⁻¹) * f x := by group
    _ = _ := by rw [h]; ac_rfl

/-- Automorphisms of a C₄-square fixing its involutions commute. -/
public theorem commute_of_fix_square_one (f g : MulAut Model)
    (hf : ∀ x : Model, x ^ 2 = 1 → f x = x)
    (hg : ∀ x : Model, x ^ 2 = 1 → g x = x) : Commute f g := by
  apply MulEquiv.ext
  intro x
  change f (g x) = g (f x)
  rw [apply_apply f g hf hg, apply_apply g f hg hf]
  ac_rfl

/-- Every automorphism in the involution-fixing kernel has square one. -/
public theorem square_eq_one_of_fix_square_one (f : MulAut Model)
    (hf : ∀ x : Model, x ^ 2 = 1 → f x = x) : f ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  change f (f x) = x
  rw [apply_apply f f hf hf]
  have h := displacement_square f hf x
  calc
    f x * (f x * x⁻¹) = (f x * x⁻¹) ^ 2 * x := by rw [mul_pow]; simp only [pow_two]; group
    _ = x := by rw [h, one_mul]

end C4SquareExtension
