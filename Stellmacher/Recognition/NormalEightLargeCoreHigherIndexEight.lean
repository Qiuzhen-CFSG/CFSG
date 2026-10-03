module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoElementaryAlternative
public import Theory.GroupTheory.QuaternionCentralProductSylowIndex
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion
public import Stellmacher.Recognition.NormalEightQuaternionHigherIndexSetup
public import Stellmacher.Recognition.NormalEightQuaternionAbelianQuotient
public import Stellmacher.Recognition.NormalEightQuaternionDihedralQuotient

/-!
# Higher-index cores containing an elementary eight

An elementary eight in the actual quotient core cannot be normalized by the
quotient Sylow: its inverse image would be a forbidden normal elementary
eight in the original Sylow. In particular it is not characteristic in the
core, and it has a distinct Sylow conjugate. Distinctness alone does not say
that the two eights generate the core.

Intrinsic recognition constructs quaternion–quaternion factors from the
single elementary eight. The actual core action supplies the quotient cases
and an outside conjugate of the central involution. The cyclic-four,
four-group, and dihedral-eight fusion/transfer exclusions then give the
contradiction, using only the bound on normal elementary subgroups.

Source: Janko–Thompson (1970), §4, printed pp.390–392.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- A core elementary eight is never normalized by the whole quotient Sylow
under the normal-only elementary bound. -/
public theorem core_elementary_eight_not_sylow_normalized
    (S : Sylow 2 G)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (E : Subgroup (pCore 2 (OmegaQuotient S))) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) :
    ¬ (omegaQuotientSylow S : Subgroup (OmegaQuotient S)) ≤
      normalizer (E.map (pCore 2 (OmegaQuotient S)).subtype : Set (OmegaQuotient S)) := by
  let U := E.map (pCore 2 (OmegaQuotient S)).subtype
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  intro hn
  have hlt := omegaQuotient_sylow_normalized_elementary_card_lt_eight S hno U
    ((map_subtype_le E).trans (pCore_isPGroup.le_sylow_of_normal _)) hn
  rw [card_map_of_injective (pCore 2 (OmegaQuotient S)).subtype_injective, hE] at hlt
  omega

/-- Normality in the core cannot be strengthened to characteristicity. -/
public theorem core_elementary_eight_not_characteristic
    (S : Sylow 2 G)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (E : Subgroup (pCore 2 (OmegaQuotient S))) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) : ¬ E.Characteristic := by
  intro hchar
  let : E.Characteristic := hchar
  let U := E.map (pCore 2 (OmegaQuotient S)).subtype
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  have hlt := omegaQuotient_normal_elementary_card_lt_eight S hno U
  rw [card_map_of_injective (pCore 2 (OmegaQuotient S)).subtype_injective, hE] at hlt
  omega

/-- A second Sylow conjugate exists, without an unjustified assertion that
it generates the core together with the original eight. -/
public theorem core_elementary_eight_exists_distinct_sylow_conjugate
    (S : Sylow 2 G)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (E : Subgroup (pCore 2 (OmegaQuotient S))) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) :
    ∃ s : OmegaQuotient S, s ∈ omegaQuotientSylow S ∧
      (E.map (pCore 2 (OmegaQuotient S)).subtype).map (MulAut.conj s).toMonoidHom ≠
        E.map (pCore 2 (OmegaQuotient S)).subtype := by
  have hn := core_elementary_eight_not_sylow_normalized S hno E hE
  obtain ⟨s, hs, hsn⟩ := SetLike.not_le_iff_exists.mp hn
  exact ⟨s, hs, fun heq => hsn (mem_normalizer_iff_map_conj_eq.mpr heq)⟩

/-- Quaternion factors reduce the higher-index numerical possibilities to
four and eight; identifying their quotient structures is still necessary. -/
public theorem higherIndexEight_index_four_or_eight_of_quaternion_factors
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : 4 ≤ (omegaCorePreimage S).index)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hjoin : B ⊔ C = ⊤) :
    (omegaCorePreimage S).index = 4 ∨ (omegaCorePreimage S).index = 8 := by
  have hle := sylow_relIndex_le_eight_of_quaternion_factors
    (pCore 2 (OmegaQuotient S)) (omegaQuotient_centralizer_pCore_le hN S hZ)
    (IsExtraspecial.center_order_p 2 _) hH B C hB hC hinter hcomm hjoin
    (omegaQuotientSylow S)
  rw [← index_omegaCorePreimage] at hle
  obtain ⟨n, hn⟩ := (S.isPGroup'.to_quotient (omegaCorePreimage S)).exists_card_eq
  change (omegaCorePreimage S).index = 2 ^ n at hn
  have hnle : n ≤ 3 := by
    by_contra h
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 4 ≤ n by omega)
    rw [← hn] at hp
    norm_num at hp
    omega
  interval_cases n <;> simp_all

/-- The higher-index order-32 core cannot contain an elementary eight under
 the normal-only elementary bound. Normality of the eight is required only
 inside the core; the quaternion structure and outside fusion are constructed. -/
public theorem higherIndexEight_false_of_elementary_eight
    [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : 4 ≤ (omegaCorePreimage S).index)
    (E : Subgroup (pCore 2 (OmegaQuotient S))) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (hZE : center (pCore 2 (OmegaQuotient S)) ≤ E) : False := by
  obtain ⟨B, C, hB, hC, hjoin, hinter, hcomm⟩ :=
    exists_quaternion_factors_of_extraspecial_thirty_two_elementary hH E hE hZE
  obtain ⟨z, t, hz, hzc, ht, hout, hzt⟩ := quaternion_core_outside_conjugate
    hns hN S hZ hH B C hB hC hjoin hinter hcomm hindex
  rcases quaternion_core_quotient_cases hN S hZ hH B C hB hC hjoin hinter hcomm hindex
    with ⟨hi, hcyclic⟩ | ⟨hi, hfour⟩ | hdihedral
  · exact quaternion_cyclic_four_quotient_false hns hN S A hA hnonab hZ hno W hW
      hunique hnormal hH B C hB hC hjoin hinter hcomm z t hz hzc ht hout hzt hi hcyclic
  · exact quaternion_four_quotient_false hns hN S A hA hnonab hZ hno W hW
      hunique hnormal hH B C hB hC hjoin hinter hcomm z t hz hzc ht hout hzt hi hfour
  · exact quaternion_dihedral_false hns hN S A hA hnonab hZ hno W hW hunique hnormal
      hH hindex B C hB hC hjoin hinter hcomm z t hz hzc ht hout hzt hdihedral

end Stellmacher.Recognition.NormalEightNonnormalImage
