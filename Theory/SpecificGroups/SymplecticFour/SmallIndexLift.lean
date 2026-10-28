module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoSylowSource
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Two-subgroup bound in an extension of Sp4(4)

A self-centralizing normal Sp4(4) embeds its ambient group in its actual
automorphism group. The latter has order dividing 4 times 979200, whose
two-part is 1024. Every ambient two-subgroup therefore has order at most
1024, including possible diagram and field automorphisms.

The original mover in GenerationTwoSymplecticCrossKernelLift has relative
order sixty-four, so its edge index is at most sixteen. This supplies the
small coset action needed to lift the generators in MS93 (5.5), pp.915--917.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The bound retains the entire ambient automorphism extension. -/
theorem two_subgroup_card_le_1024_of_centric_four_component
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (e : B ≃* Sp F) (hB : Nat.card B = 979200)
    (hC : centralizer (B : Set G) = ⊥)
    (P : Subgroup G) (hP : IsPGroup 2 P) : Nat.card P ≤ 1024 := by
  have hout : Nat.card (MulAut.Outer B) = 4 := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv,
      DiagramAutomorphisms.card_outer_eq_two_mul (m := 2) (by simpa using hF) (by decide)]
  have hinner : Nat.card (MulAut.innerSubgroup B) ∣ Nat.card B :=
    card_range_dvd (MulAut.conj : B →* MulAut B)
  have hAut : Nat.card (MulAut B) ∣ 3916800 := by
    rw [←(MulAut.innerSubgroup B).card_mul_index]
    change Nat.card (MulAut.innerSubgroup B) * Nat.card (MulAut.Outer B) ∣ _
    rw [hout]
    exact Nat.mul_dvd_mul (hB ▸ hinner) (dvd_refl 4)
  have hG : Nat.card G ∣ 3916800 :=
    (card_dvd_of_injective (MulAut.conjNormal (H := B))
      (MulAut.conjNormal_injective_of_centralizer_eq_bot B hC)).trans hAut
  obtain ⟨n,hn⟩ := hP.exists_card_eq
  have hd : 2^n ∣ 3916800 := hn ▸ P.card_subgroup_dvd_card.trans hG
  have hcop : Nat.Coprime (2^n) 3825 :=
    (Nat.prime_two.coprime_pow_of_not_dvd (by decide : ¬2 ∣ 3825)).symm
  have hp : 2^n ∣ 1024 := hcop.dvd_mul_right.mp hd
  rw [hn]
  exact Nat.le_of_dvd (by decide) hp
end Theory.SpecificGroups.SymplecticFour
