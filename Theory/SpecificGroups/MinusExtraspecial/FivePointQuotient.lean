module
public import Theory.SpecificGroups.MinusExtraspecial.FivePointLifts
public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The actual central quotient as the binary five-point core

Commuting with the five singular lifts gives five binary coordinates. Their
sum is zero, their common kernel is the full center, and every even-weight
vector occurs. Automorphisms permute these coordinates by their actual action
on the five singular points. Thus the full central quotient carries the
natural binary permutation module with its original automorphism action.

Only multiplication in the 32-element core is computed. Equivariance for
arbitrary automorphisms follows from the lift-image theorem.
-/

public section
namespace MinusExtraspecial.FivePointQuotient
open Subgroup FivePointLifts FixedFourCalculation.Outside
open scoped BigOperators

private def bit (x : Model) (i : Fin 5) : ZMod 2 :=
  if x * lift i = lift i * x then 0 else 1

private theorem bit_sum (x : Model) : ∑ i, bit x i = 0 := by
  revert x
  decide +kernel

private theorem bit_mul (x y : Model) (i : Fin 5) :
    bit (x * y) i = bit x i + bit y i := by
  revert x y i
  decide +kernel

/-- The actual commutation coordinates on the full minus extraspecial core. -/
def coordinates : Model →* Multiplicative (BinaryPermutation.core (Fin 5)) where
  toFun x := Multiplicative.ofAdd ⟨bit x, bit_sum x⟩
  map_one' := by
    apply Subtype.ext
    funext i
    change bit 1 i = 0
    simp only [bit, one_mul, mul_one, ↓reduceIte]
  map_mul' x y := by
    apply Subtype.ext
    funext i
    exact bit_mul x y i

/-- The coordinate kernel is the full intrinsic center. -/
theorem coordinates_kernel : coordinates.ker = center Model := by
  ext x
  change (Multiplicative.ofAdd (⟨bit x, bit_sum x⟩ : BinaryPermutation.core (Fin 5)) = 1) ↔ _
  rw [MinusExtraspecial.mem_center_iff]
  have hh : ∀ x : Model, (∀ i, bit x i = 0) ↔ x = 1 ∨ x = quaternion z := by
    decide +kernel
  rw [←hh]
  constructor
  · intro h i
    exact congrArg (fun v : Multiplicative (BinaryPermutation.core (Fin 5)) => v.toAdd.val i) h
  · intro h
    apply Subtype.ext
    funext i
    exact h i

/-- Every vector in the binary five-point core is obtained from an actual
element of the extraspecial group. -/
theorem coordinates_surjective : Function.Surjective coordinates := by
  intro v
  have hh : ∀ w : Fin 5 → ZMod 2, (∑ i, w i) = 0 → ∃ x : Model, bit x = w := by
    decide +kernel
  obtain ⟨x,hx⟩ := hh v.toAdd.val v.toAdd.property
  exact ⟨x, Subtype.ext hx⟩

private theorem commute_central_lift (x : Model) (i : Fin 5) :
    x * (quaternion z * lift i) = quaternion z * lift i * x ↔
      x * lift i = lift i * x := by
  have hz : x * quaternion z = quaternion z * x :=
    Subgroup.mem_center_iff.mp ((MinusExtraspecial.mem_center_iff _).mpr (Or.inr rfl)) x
  rw [←mul_assoc x, hz, mul_assoc, mul_assoc]
  exact mul_left_cancel_iff

private theorem bit_action (a : MulAut Model) (x : Model) (i : Fin 5) :
    bit (a x) (fivePointAction a i) = bit x i := by
  have hh : a x * a (lift i) = a (lift i) * a x ↔ x * lift i = lift i * x := by
    rw [←map_mul, ←map_mul, a.injective.eq_iff]
  rcases lift_image a i with hi | hi
  · rw [hi] at hh
    exact if_congr hh rfl rfl
  · rw [hi, commute_central_lift] at hh
    exact if_congr hh rfl rfl

/-- The coordinates retain the actual full automorphism action, marked by
its permutation of the five singular points. -/
theorem coordinates_equivariant (a : MulAut Model) (x : Model) :
    (coordinates (a x)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (fivePointAction a) (coordinates x).toAdd := by
  apply Subtype.ext
  funext i
  change bit (a x) i = bit x ((fivePointAction a).symm i)
  simpa only [Equiv.apply_symm_apply] using bit_action a x ((fivePointAction a).symm i)

/-- The full central quotient has the actual even-weight permutation coordinates. -/
noncomputable def centralQuotientEquiv :
    (Model ⧸ center Model) ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
  (QuotientGroup.congr _ _ (MulEquiv.refl Model) (by
    change (center Model).map (MonoidHom.id Model) = coordinates.ker
    rw [Subgroup.map_id, coordinates_kernel])).trans
    (QuotientGroup.quotientKerEquivOfSurjective coordinates coordinates_surjective)

/-- The quotient equivalence uses the canonical quotient map of the full center. -/
theorem centralQuotientEquiv_mk (x : Model) :
    centralQuotientEquiv (QuotientGroup.mk' (center Model) x) = coordinates x := by
  rfl

end MinusExtraspecial.FivePointQuotient
