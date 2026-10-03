module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalFourLargeCoreActionSetup
public import Theory.GroupTheory.QuaternionCentralProductSylowIndex
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupTheory.CoreFreeOrderSeventyTwo
public import Theory.GroupTheory.QuaternionCentralProductOuterEight
public import Theory.GroupTheory.QuaternionCentralProductNineOrbit

/-!
# The actual quaternion core's outer action

The canonical Frattini action has kernel the actual two-core. Its range
therefore has trivial two-core, and its order divides 72 by the quaternion
factor automorphism bound. A Sylow index at least four forces nine to divide
this range order. A Sylow three-subgroup of the original quotient consequently
has order nine, providing actual conjugating elements rather than an abstract
subgroup of the full automorphism group.

The intrinsic order-eight outer-action identification and the orbit of
noncentral involutions are separate structural steps.

Source: Janko–Thompson (1970), §4, printed p.390.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The actual outer action range has no normal two-subgroup. -/
public theorem quaternion_outer_action_twoCore_eq_bot
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2) :
    pCore 2 (omegaCoreFrattiniAction S).range = ⊥ :=
  pCore_range_eq_bot_of_ker_eq_pCore 2 _ (omegaCoreFrattiniAction_kernel hN S hZ)

/-- The actual outer image has order dividing 72, rather than just an
upper bound on its two-part. -/
public theorem quaternion_outer_action_card_dvd_seventy_two
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) :
    Nat.card (omegaCoreFrattiniAction S).range ∣ 72 := by
  have hd := card_dvd_of_selfCentralizing_quaternion_factors _
    (omegaQuotient_centralizer_pCore_le hN S hZ)
    (IsExtraspecial.center_order_p 2 _) B C hB hC hinter hcomm hjoin
  rw [← index_ker, omegaCoreFrattiniAction_kernel hN S hZ]
  have hc := (pCore 2 (OmegaQuotient S)).card_mul_index
  rw [hH] at hc
  rw [← hc] at hd
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 32) hd

/-- The original Sylow index is realized inside the actual action range. -/
public theorem quaternion_outer_action_four_dvd_card
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hindex : 4 ≤ (omegaCorePreimage S).index) :
    4 ∣ Nat.card (omegaCoreFrattiniAction S).range := by
  obtain ⟨R, ⟨e⟩⟩ := omegaCorePreimage_quotient_equiv_sylow_range S
    (omegaCoreFrattiniAction S) (omegaCoreFrattiniAction_kernel hN S hZ)
  have hR : 4 ≤ Nat.card R := by
    rw [← Nat.card_congr e.toEquiv]
    exact hindex
  obtain ⟨n, hn⟩ := R.isPGroup'.exists_card_eq
  have hnlo : 2 ≤ n := by
    by_contra hnlo
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show n ≤ 1 by omega)
    rw [← hn] at hp
    omega
  have hd : 4 ∣ Nat.card R := hn ▸ pow_dvd_pow 2 hnlo
  exact hd.trans (R : Subgroup (omegaCoreFrattiniAction S).range).card_subgroup_dvd_card

/-- The full order-nine part occurs in the actual outer image. Its existence
follows from the exact action kernel, not from the index bound alone. -/
public theorem quaternion_outer_action_nine_dvd_card
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
    9 ∣ Nat.card (omegaCoreFrattiniAction S).range :=
  nine_dvd_card_of_twoCore_eq_bot_of_card_dvd_seventy_two
    (quaternion_outer_action_twoCore_eq_bot hN S hZ)
    (quaternion_outer_action_card_dvd_seventy_two hN S hZ hH B C hB hC hjoin hinter hcomm)
    (quaternion_outer_action_four_dvd_card hN S hZ hindex)

/-- The actual central-omega quotient contains a subgroup of order nine.
These are actual ambient actors on the supplied quaternion core. -/
public theorem quaternion_core_exists_nine_subgroup
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
    ∃ U : Subgroup (OmegaQuotient S), Nat.card U = 9 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnine : 9 ∣ Nat.card (OmegaQuotient S) :=
    (quaternion_outer_action_nine_dvd_card hN S hZ hH B C hB hC hjoin hinter hcomm hindex).trans
      (card_range_dvd (omegaCoreFrattiniAction S))
  have hbound := card_dvd_of_selfCentralizing_quaternion_factors _
    (omegaQuotient_centralizer_pCore_le hN S hZ)
    (IsExtraspecial.center_order_p 2 _) B C hB hC hinter hcomm hjoin
  let U : Sylow 3 (OmegaQuotient S) := Classical.choice inferInstance
  refine ⟨U, ?_⟩
  have h9U : 9 ∣ Nat.card U := U.pow_dvd_card_of_pow_dvd_card (n := 2) hnine
  obtain ⟨n, hn⟩ := U.isPGroup'.exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra hnle
    have hd : 27 ∣ 2304 :=
      (show 3 ^ 3 ∣ 3 ^ n from pow_dvd_pow 3 (by omega)).trans
        (hn ▸ (U : Subgroup (OmegaQuotient S)).card_subgroup_dvd_card.trans hbound)
    norm_num at hd
  interval_cases n <;> simp_all

/-- An actual index-eight quotient is the dihedral Sylow case of the
Frattini outer action. -/
public theorem quaternion_outer_action_index_eight_dihedral
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
    (hindex : (omegaCorePreimage S).index = 8) :
    Nonempty ((S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4) := by
  obtain ⟨R, ⟨e⟩⟩ := omegaCorePreimage_quotient_equiv_sylow_range S
    (omegaCoreFrattiniAction S) (omegaCoreFrattiniAction_kernel hN S hZ)
  let U : Subgroup (MulAut (pCore 2 (OmegaQuotient S) ⧸
      frattini (pCore 2 (OmegaQuotient S)))) :=
    R.map (omegaCoreFrattiniAction S).range.subtype
  have hUle : U ≤ (quotientAut (frattini (pCore 2 (OmegaQuotient S)))).range := by
    have hrange : (omegaCoreFrattiniAction S).range ≤
        (quotientAut (frattini (pCore 2 (OmegaQuotient S)))).range := by
      intro a ha
      obtain ⟨g, hg⟩ := ha
      have hact : omegaCoreFrattiniAction S g =
          quotientAut (frattini (pCore 2 (OmegaQuotient S)))
            (MulAut.conjNormal g) := by
        apply MulEquiv.ext
        intro v
        induction v using Quotient.inductionOn with
        | h x =>
          change (omegaCoreFrattiniAction S g)
              (QuotientGroup.mk' (frattini (pCore 2 (OmegaQuotient S))) x) = _
          rw [omegaCoreFrattiniAction_apply_mk]
          exact (quotientAut_apply_mk _ _ _).symm
      exact ⟨MulAut.conjNormal g, hact.symm.trans hg⟩
    exact ((Subgroup.map_le_range (omegaCoreFrattiniAction S).range.subtype R).trans_eq
      (omegaCoreFrattiniAction S).range.range_subtype).trans hrange
  have hRcard : Nat.card R = 8 := by
    have hi : (omegaCorePreimage S).index = Nat.card R :=
      (index_eq_card _).trans (Nat.card_congr e.toEquiv)
    omega
  have hUcard : Nat.card U = 8 := by
    rw [card_map_of_injective (omegaCoreFrattiniAction S).range.subtype_injective,
      hRcard]
  have hUp : IsPGroup 2 U := R.isPGroup'.map (omegaCoreFrattiniAction S).range.subtype
  obtain ⟨d⟩ := quaternion_central_product_frattini_outer_eight_dihedral
    hH B C hB hC hjoin hinter hcomm U hUle hUp hUcard
  let eU : R ≃* U := R.equivMapOfInjective
    (omegaCoreFrattiniAction S).range.subtype
    (omegaCoreFrattiniAction S).range.subtype_injective
  exact ⟨e.trans (eU.trans d)⟩

/-- The actual order-nine subgroup fuses all noncentral involutions of the
quaternion core in the ambient central-omega quotient. -/
public theorem quaternion_core_noncentral_involution_conjugacy
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
    (U : Subgroup (OmegaQuotient S)) (hU : Nat.card U = 9)
    (x y : pCore 2 (OmegaQuotient S))
    (hx : orderOf x = 2) (hxZ : x ∉ center (pCore 2 (OmegaQuotient S)))
    (hy : orderOf y = 2) (hyZ : y ∉ center (pCore 2 (OmegaQuotient S))) :
    IsConj (x : OmegaQuotient S) (y : OmegaQuotient S) := by
  exact quaternion_involution_orbit_of_order_nine
    (pCore 2 (OmegaQuotient S))
    (omegaQuotient_centralizer_pCore_le hN S hZ)
    hH B C hB hC hjoin hinter hcomm U hU x y hx hxZ hy hyZ

end Stellmacher.Recognition.NormalEightNonnormalImage
