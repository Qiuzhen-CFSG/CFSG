/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/GolayOctadExteriorRestriction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolayOctadRestriction
public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayOctadTransitivity
/-!
Golay coordinate restrictions and signed-support transport in the Leech lattice.
The proofs retain the explicit code maps and coordinate identities used by the stabilizer geometry.

Source: Gerald Höhn, `Atlas/Conway/GolayOctadExteriorRestriction.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem golay_restriction_surjective_of_no_support (T : Finset Omega)
    (hT : ∀ w : BinaryWord, w ∈ golay → Finset.univ.filter (fun i => w i ≠ 0) ⊆ T → w = 0) :
    Function.Surjective (golayRestriction T) := by
  have hz : binaryDot.orthogonal (golayRestriction T).range = ⊥ := by
    apply le_antisymm _ bot_le
    intro w hw
    have hc := (golay_restriction_orthogonal T w).mp hw
    have he : codeZeroExtend T w = 0 := hT _ hc (by
      intro i hi
      by_contra hn
      exact (Finset.mem_filter.mp hi).2 (by simp [codeZeroExtend,hn]))
    change w = 0
    funext i
    have hh := congrFun he i.val
    simpa only [codeZeroExtend_apply,Pi.zero_apply] using hh
  have hr : (binaryDot (ι := T)).IsRefl := fun x y h => (binaryDot_symmetric y x).trans h
  have he := binaryDot.orthogonal_orthogonal binaryDot_nondegenerate hr (golayRestriction T).range
  rw [hz,LinearMap.BilinForm.orthogonal_bot] at he
  exact LinearMap.range_eq_top.mp he.symm

theorem golay_octad_erased_exterior_surjective (O J : Finset Omega) (hO : O ∈ octads)
    (hJ : J.card ≤ 2) (hOJ : Disjoint O J) (a : Omega) (ha : a ∈ O) :
    Function.Surjective (golayRestriction (O.erase a ∪ J)) := by
  apply golay_restriction_surjective_of_no_support
  intro w hw hsupport
  by_contra hw0
  let B := Finset.univ.filter (fun i => w i ≠ 0)
  have hB : B.card = hammingNorm w := rfl
  have hmin := golay_minimum w hw hw0
  have hdiv := golay_doublyEven w hw
  have hle : B.card ≤ 9 := by
    have h1 := Finset.card_le_card hsupport
    have h2 := Finset.card_union_le (O.erase a) J
    rw [Finset.card_erase_of_mem ha,octad_size O hO] at h2
    change B.card ≤ _ at h1
    omega
  have h8 : B.card = 8 := by omega
  have hBo : B ∈ octads := (octads_mem B).mpr ⟨⟨w,hw⟩,hB ▸ h8,rfl⟩
  have hd : B \ O ⊆ J := by
    intro i hi
    obtain ⟨hiB,hiO⟩ := Finset.mem_sdiff.mp hi
    rcases Finset.mem_union.mp (hsupport hiB) with h | h
    · exact (hiO (Finset.mem_erase.mp h).2).elim
    · exact h
  have hdi := Finset.card_le_card hd
  have he := Finset.card_sdiff_add_card_inter B O
  have h5 : 5 ≤ (B ∩ O).card := by omega
  obtain ⟨F,hF,hFc⟩ := Finset.exists_subset_card_eq h5
  have hBO : B = O := octad_unique_on_five F B O hFc hBo hO
    (hF.trans Finset.inter_subset_left) (hF.trans Finset.inter_subset_right)
  have haB : a ∈ B := hBO ▸ ha
  rcases Finset.mem_union.mp (hsupport haB) with h | h
  · exact (Finset.mem_erase.mp h).1 rfl
  · exact Finset.disjoint_left.mp hOJ ha h

theorem golay_octad_exterior_restriction (O J : Finset Omega) (hO : O ∈ octads)
    (hJ : J.card ≤ 2) (hOJ : Disjoint O J) (w : BinaryWord)
    (hw : ∑ i ∈ O, w i = 0) : ∃ c : golay, ∀ i ∈ O ∪ J, c.val i = w i := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < O.card by rw [octad_size O hO]; decide)
  obtain ⟨c,hc⟩ := golay_octad_erased_exterior_surjective O J hO hJ hOJ a ha (fun i => w i)
  have he (i : Omega) (hi : i ∈ O.erase a ∪ J) : c.val i = w i := congrFun hc ⟨i,hi⟩
  obtain ⟨v,hv,hvs⟩ := (octads_mem O).mp hO
  have hC : supportWord O ∈ golay := by
    have hh := binarySupportEquiv.left_inv v.val
    change supportWord (support v.val) = v.val at hh
    rw [hvs] at hh
    exact hh ▸ v.prop
  have hp := golay_selfOrthogonal hC c.val c.prop
  change binaryDot c.val (supportWord O) = 0 at hp
  rw [tetradSignParity_dot,tetradSignParity,Finset.sum_coe_sort] at hp
  have hcSum : (∑ i ∈ O.erase a, c.val i) = ∑ i ∈ O.erase a, w i :=
    Finset.sum_congr rfl (fun i hi => he i (Finset.mem_union_left _ hi))
  have haeq : c.val a = w a := by
    rw [← Finset.add_sum_erase _ _ ha,hcSum] at hp
    rw [← Finset.add_sum_erase _ _ ha] at hw
    exact add_right_cancel (hp.trans hw.symm)
  refine ⟨c,?_⟩
  intro i hi
  by_cases hia : i = a
  · simpa [hia] using haeq
  · apply he
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hia,hi⟩)
    · exact Finset.mem_union_right _ hi

end Atlas.Conway

