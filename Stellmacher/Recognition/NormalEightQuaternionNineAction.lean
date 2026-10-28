module

public import Stellmacher.Recognition.NormalEightQuaternionOuterAction
public import Theory.GroupTheory.QuaternionCentralProductNineAction
public import Theory.GroupTheory.NormalizedOddSylowLift

/-!
# Actual independent cubic actors on the quaternion core

The order-nine subgroup of the actual omega quotient restricts faithfully to
the two quaternion factors. Thus the independent-cubic construction applies
without an exact order assumption on the ambient normalizer. We retain any
prescribed order-nine subgroup, allowing later normalization to keep the
selected outside involution fixed.

Source: Janko–Thompson (1970), §4, printed pp.390–391.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage
open Subgroup NormalFourCentralOmegaTwo
variable {G : Type*} [Group G] [Finite G]

/-- Independent cubic actors in a prescribed subgroup of the actual quotient. -/
public theorem quaternion_core_independent_cubics_of_nine_subgroup
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (U : Subgroup (OmegaQuotient S)) (hU : Nat.card U = 9) :
    ∃ actors : QuaternionIndependentCubics
      (B.map (pCore 2 (OmegaQuotient S)).subtype)
      (C.map (pCore 2 (OmegaQuotient S)).subtype), actors.A = U := by
  let H := pCore 2 (OmegaQuotient S)
  let B' := B.map H.subtype
  let C' := C.map H.subtype
  have hB' : Nonempty (B' ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hB
    exact ⟨(B.equivMapOfInjective H.subtype H.subtype_injective).symm.trans e⟩
  have hC' : Nonempty (C' ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hC
    exact ⟨(C.equivMapOfInjective H.subtype H.subtype_injective).symm.trans e⟩
  have hjoin' : B' ⊔ C' = H := by
    rw [← Subgroup.map_sup, hjoin, ← MonoidHom.range_eq_map, range_subtype]
  have hinter' : Nat.card (B' ⊓ C' : Subgroup (OmegaQuotient S)) = 2 := by
    rw [← map_inf B C H.subtype H.subtype_injective,
      card_map_of_injective H.subtype_injective]
    exact hinter
  have hcomm' : ∀ b ∈ B', ∀ c ∈ C', b * c = c * b := by
    rintro b ⟨b₀, hb, rfl⟩ c ⟨c₀, hc, rfl⟩
    exact congrArg H.subtype (hcomm b₀ hb c₀ hc)
  apply independent_cubics_of_nine_subgroup B' C' U hB' hC' hinter' hcomm'
  · rw [hjoin']
    exact omegaQuotient_centralizer_pCore_le hN S hZ
  · exact hU
  · rw [hjoin', H.normalizer_eq_top]
    exact le_top

/-- The actual quaternion core admits faithful independent cubic actors. -/
public theorem quaternion_core_exists_independent_cubics
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hindex : 4 ≤ (omegaCorePreimage S).index) :
    Nonempty (QuaternionIndependentCubics
      (B.map (pCore 2 (OmegaQuotient S)).subtype)
      (C.map (pCore 2 (OmegaQuotient S)).subtype)) := by
  obtain ⟨U, hU⟩ := quaternion_core_exists_nine_subgroup
    hN S hZ hH B C hB hC hjoin hinter hcomm hindex
  obtain ⟨actors, _⟩ := quaternion_core_independent_cubics_of_nine_subgroup
    hN S hZ B C hB hC hjoin hinter hcomm U hU
  exact ⟨actors⟩

/-- A normalized order-nine subgroup of the quotient has an actual
three-subgroup lift normalized by the original selected involution. -/
public theorem quaternion_nine_subgroup_normalized_ambient_lift
    (S : Sylow 2 G) (U : Subgroup (OmegaQuotient S)) (hU : Nat.card U = 9)
    (t : S) (ht : orderOf t = 2)
    (htu : omegaQuotientHom S t ∈ normalizer (U : Set (OmegaQuotient S))) :
    ∃ Q : Subgroup (omegaNormalizer S), IsPGroup 3 Q ∧
      Q.map (QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S))) = U ∧
      inclusion (sylow_le_omegaNormalizer S) t ∈ normalizer (Q : Set (omegaNormalizer S)) := by
  let q := QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S))
  have hker : Odd (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.not_even_iff_odd.mp (fun h =>
      (Nat.prime_two.coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (p := 2) (G := omegaNormalizer S)))
        (even_iff_two_dvd.mp h))
  have hthree : IsPGroup 3 U := IsPGroup.of_card (p := 3) (n := 2) hU
  have hodd : Odd (Nat.card U) := by rw [hU]; decide
  apply normalized_sylow_lift_of_odd_kernel q
    (QuotientGroup.mk'_surjective _) hker U hthree hodd
    (inclusion (sylow_le_omegaNormalizer S) t)
  · have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
    rw [← map_pow, ht2, map_one]
  · rw [omegaQuotientHom_apply] at htu
    have he : inclusion (sylow_le_omegaNormalizer S) t =
        (⟨(t : G), sylow_le_omegaNormalizer S t.property⟩ : omegaNormalizer S) :=
      Subtype.ext rfl
    simpa only [he] using htu

end Stellmacher.Recognition.NormalEightNonnormalImage
