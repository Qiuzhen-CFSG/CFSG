module

public import Theory.Representation.HexacodeAction.WeightFourEvenNormalTwo
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetStabilizer
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The unique normal elementary 64 in an affine weight-four point centralizer

A nontranslation elementary subgroup of order 64 projects to an offender.
Its unique best offender would be normalized by the full vector stabilizer.
The even normal two-subgroup calculation then identifies it with the actual
vector-stabilizer core, which fixes only a binary two-space. A best offender
fixes a four-space, so this is impossible.
-/

public noncomputable section
open Atlas.Codes Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.Hexacode
local notation "V" => Multiplicative hexacode
local notation "A" => V ⋊[hexAffineAction] HexAutomorphisms
local notation "ι" => (SemidirectProduct.inl : V →* A)
local notation "π" => (SemidirectProduct.rightHom : A →* HexAutomorphisms)

private theorem no_normal_offender_at_weightFour
    (v : hexacode) (hv : hammingNorm v.val = 4)
    (N : Subgroup HexAutomorphisms) (hN : N ≤ fullVectorStabilizer v)
    (hn : fullVectorStabilizer v ≤ normalizer (N : Set HexAutomorphisms)) :
    ¬ IsOffender action N := by
  intro ho
  let := ho.1.2
  obtain ⟨B,hBN,hB⟩ := ho.exists_bestOffender action
  let := hB.1.2
  have hBn : fullVectorStabilizer v ≤ normalizer (B : Set HexAutomorphisms) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply bestOffender_unique_in_pgroup N (IsElementaryAbelian.isPGroup 2 N)
    · exact (map_mono hBN).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hn hg))
    · exact hBN
    · exact hB.map_conj action g
    · exact hB
  have he : B = ((fullWeightVectorStabilizer v).pCoreIn 2).map hexSign.ker.subtype :=
    weightFour_even_normal_two_eq_core v hv B (hBN.trans hN)
      (IsElementaryAbelian.isPGroup 2 B) hB.1.1
      (((by rintro _ ⟨g,hg,rfl⟩; exact hg) :
        (fullWeightVectorStabilizer v).map hexSign.ker.subtype ≤ fullVectorStabilizer v).trans hBn)
      (bestOffender_le_even B hB)
  have hf : fixedSpace action B = (Submodule.span F {v}).restrictScalars Bit := by
    rw [he, ← fixedSpace_comp_map]
    exact weightFourVectorCore_fixed v hv
  have hd := bestOffender_fixedSpace_finrank B hB
  rw [hf,fieldPoint_binary_finrank _ (finrank_span_singleton
    (by intro hh; simp [hh] at hv))] at hd
  omega

private theorem affine_elementary_projection_offender
    (W : Subgroup A) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 64) (hne : W.map π ≠ ⊥) :
    IsOffender action (W.map π) := by
  let : IsElementaryAbelian 2 (W.map π) := IsElementaryAbelian.map π
  have hE : IsElementaryTwo (W.map π) := ⟨hne,inferInstance⟩
  let j : W.comap ι → fixedSpace action (W.map π) := fun v => ⟨v.val.toAdd,by
    intro d
    obtain ⟨w,hw,hd⟩ := d.property
    have hh := congrArg (fun x : W => x.val.left)
      (mul_comm (⟨w,hw⟩ : W) ⟨ι v.val,v.property⟩)
    change w.left * hexAffineAction w.right v.val = v.val * hexAffineAction 1 w.left at hh
    rw [map_one,MulAut.one_apply,mul_comm v.val w.left] at hh
    have he := congrArg Multiplicative.toAdd (mul_left_cancel hh)
    change action d.val v.val.toAdd = v.val.toAdd
    rw [← hd]
    exact he⟩
  have hj : Function.Injective j := by
    intro v w hvw
    apply Subtype.ext
    change v.val.toAdd = w.val.toAdd
    exact congrArg (fun x => x.val) hvw
  have hc : Nat.card (W ⊓ (ι).range : Subgroup A) ≤
      Nat.card (fixedSpace action (W.map π)) := by
    rw [inf_comm,← map_comap_eq,card_map_of_injective SemidirectProduct.inl_injective]
    exact Nat.card_le_card_of_injective j hj
  have hp := IsElementaryAbelian.card_inf_ker_mul_card_map W π
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom,hW] at hp
  have hb : 2 ^ 6 ≤ 2 ^ (Module.finrank (ZMod 2) (fixedSpace action (W.map π)) +
      rank (W.map π)) := by
    have hmul := Nat.mul_le_mul_right (Nat.card (W.map π)) hc
    rw [hp,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      hE.card_eq_two_pow_rank,← pow_add] at hmul
    exact hmul
  have hd := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  refine ⟨hE,?_⟩
  have hh := fixedCodim_add_finrank action (W.map π)
  rw [hexacode_finrank] at hh
  omega

/-- Any elementary subgroup of order 64 normalized by an affine subgroup
whose actor image is the full stabilizer of a weight-four vector is exactly
the translation subgroup. The actor image and subgroup are the literal ones. -/
theorem affine_point_elementary64_unique
    (v : hexacode) (hv : hammingNorm v.val = 4)
    (Q W : Subgroup A) [IsElementaryAbelian 2 W]
    (hQ : Q.map π = fullVectorStabilizer v) (hWQ : W ≤ Q)
    (hW : Nat.card W = 64) (hn : Q ≤ normalizer (W : Set A)) :
    W = (ι).range := by
  let : Finite (ι).range := Finite.of_surjective (ι).rangeRestrict
    (MonoidHom.rangeRestrict_surjective ι)
  have hproj : W.map π = ⊥ := by
    by_contra he
    apply no_normal_offender_at_weightFour v hv (W.map π)
      ((map_mono hWQ).trans_eq hQ)
      (hQ ▸ (map_mono hn).trans (W.le_normalizer_map π))
    exact affine_elementary_projection_offender W hW he
  have hle : W ≤ (ι).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact (map_eq_bot_iff W).mp hproj
  apply eq_of_le_of_card_ge hle
  rw [hW]
  change Nat.card (Set.range ι) ≤ 64
  rw [Nat.card_range_of_injective SemidirectProduct.inl_injective]
  exact le_of_eq ((Nat.card_congr
    (Multiplicative.toAdd : V ≃ hexacode)).trans hexacode_card)

/- The same argument only needs a normalized two-subgroup containing W. This
form is useful for the O₂ of a point centralizer: W itself need not be
normalized by the whole affine group. -/
theorem affine_point_elementary64_in_normal_two
    (v : hexacode) (hv : hammingNorm v.val = 4)
    (Q S W : Subgroup A) [IsElementaryAbelian 2 W]
    (hQ : Q.map π = fullVectorStabilizer v)
    (hS : IsPGroup 2 S) (hWS : W ≤ S) (hSQ : S ≤ Q)
    (hQS : Q ≤ normalizer (S : Set A))
    (hW : Nat.card W = 64) :
    W = (ι).range := by
  let : Finite (ι).range := Finite.of_surjective (ι).rangeRestrict
    (MonoidHom.rangeRestrict_surjective ι)
  have hproj : W.map π = ⊥ := by
    by_contra he
    obtain ⟨B,hBW,hB⟩ :=
      (affine_elementary_projection_offender W hW he).exists_bestOffender action
    have hBS : B ≤ S.map π := hBW.trans (map_mono hWS)
    have hfull : fullVectorStabilizer v ≤ normalizer (S.map π : Set HexAutomorphisms) := by
      rw [← hQ]
      exact (map_mono hQS).trans (le_normalizer_map π)
    have hBn : fullVectorStabilizer v ≤ normalizer (B : Set HexAutomorphisms) := by
      intro g hg
      apply mem_normalizer_iff_map_conj_eq.mpr
      apply bestOffender_unique_in_pgroup (S.map π) (hS.map π)
      · exact (map_mono hBS).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hfull hg))
      · exact hBS
      · exact hB.map_conj action g
      · exact hB
    exact no_normal_offender_at_weightFour v hv B
      ((hBS.trans (map_mono hSQ)).trans_eq hQ) hBn (hB.isOffender action)
  have hle : W ≤ (ι).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact (map_eq_bot_iff W).mp hproj
  apply eq_of_le_of_card_ge hle
  rw [hW]
  change Nat.card (Set.range ι) ≤ 64
  rw [Nat.card_range_of_injective SemidirectProduct.inl_injective]
  exact (Nat.card_congr
    (Multiplicative.toAdd : V ≃ hexacode)).trans hexacode_card |>.le

end Representation.Hexacode
