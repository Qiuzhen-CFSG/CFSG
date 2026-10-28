module

public import Theory.GroupTheory.Amalgam.DihedralTwelvePair
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Concrete groups in the dihedral-twelve pair

The product vertex is the dihedral group of order twelve: send a rotation
of order six to the product of the central involution and a three-cycle.
The middle group is elementary of order four. The finite verification checks
only the twelve dihedral words and their multiplication.

Source: Aschbacher–Smith F.6.5(2)(ii), printed p.305.
-/

public section
open Subgroup
namespace Theory.GroupTheory.RankTwoAmalgam

private def z : swapMiddle := ⟨Equiv.swap 0 1, mem_zpowers _⟩
private def rho : SymmetricThree := Equiv.swap 0 1 * Equiv.swap 1 2
private def vertexWord : DihedralGroup 6 → DihedralTwelveVertex
  | .r i => (z ^ i.val, rho ^ i.val)
  | .sr i => (z ^ i.val, Equiv.swap 0 1 * rho ^ i.val)
private def vertexHom : DihedralGroup 6 →* DihedralTwelveVertex where
  toFun := vertexWord
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

/-- The concrete product vertex is `D₁₂`, with `DihedralGroup n` of order `2n`. -/
noncomputable def dihedralTwelveVertexEquiv : DihedralTwelveVertex ≃* DihedralGroup 6 := by
  have hi : Function.Injective vertexHom := by decide +kernel
  have hc : Nat.card DihedralTwelveVertex = Nat.card (DihedralGroup 6) := by
    rw [Nat.card_prod, swapMiddle_card]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial, DihedralGroup.card]
  exact (MulEquiv.ofBijective vertexHom
    ((Nat.bijective_iff_injective_and_card vertexHom).mpr ⟨hi, hc.symm⟩)).symm

/-- The model's full common subgroup is the elementary group of order four. -/
theorem dihedralTwelvePair_middle_isKleinFour : IsKleinFour (swapMiddle × swapMiddle) where
  card_four := by rw [Nat.card_prod, swapMiddle_card]
  exponent_two := by
    let : Nontrivial swapMiddle := Finite.one_lt_card_iff_nontrivial.mp (by rw [swapMiddle_card]; decide)
    apply Monoid.exponent_eq_prime_iff Nat.prime_two |>.mpr
    intro x hx
    apply orderOf_eq_prime (p := 2) ?_ hx
    apply Prod.ext
    · change x.1 ^ 2 = 1
      simpa only [swapMiddle_card] using (pow_card_eq_one' (x := x.1))
    · change x.2 ^ 2 = 1
      simpa only [swapMiddle_card] using (pow_card_eq_one' (x := x.2))

end Theory.GroupTheory.RankTwoAmalgam
