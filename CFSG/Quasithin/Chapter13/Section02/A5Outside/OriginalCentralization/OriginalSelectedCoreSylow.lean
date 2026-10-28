module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSelectedCoreContainment
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalNormalizerSylowUniqueness

/-!
# The original selected pair core lies in its normalizing Sylow subgroup

The pair core U lies in M=N(L). If U enlarged the index-two subgroup
T₀=N_T(R), their product would be an ambient Sylow subgroup contained
in M and normalizing U. Uniqueness over its join with the same L is
transported inside M. It would put N(U), and hence R, in M, a contradiction.

Only the actual generation, source-core normalization, and index bound
of the selected factor are used. No whole-family packaging is required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G}

private theorem core_le_left_normalizer
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : R ⊔ (T : Subgroup G) = H)
    (hind : ((T : Subgroup G) ⊓ normalizer (R : Set G)).relIndex (T : Subgroup G) ≤ 2)
    (hSR : Global.sourceS L H ≤ normalizer (R : Set G)) :
    (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 ≤
      normalizer (L : Set G) := by
  let N := ChapterF.Source.generated ![L,R] (Global.sourceS L H)
  let U := N.pCoreIn 2
  change U ≤ normalizer (L : Set G)
  by_cases hu : U = ⊥
  · exact hu ▸ bot_le
  let T₀ := (T : Subgroup G) ⊓ normalizer (R : Set G)
  obtain ⟨he,hi⟩ := original_selected_pair_core_normalizer d hH hgen hind hu
  change (T : Subgroup G) ⊓ normalizer (U : Set G) = T₀ at he
  have hindex : T₀.relIndex (T : Subgroup G) = 2 := by rwa [he] at hi
  have hT₀U : T₀ ≤ normalizer (U : Set G) := he.ge.trans inf_le_right
  have hTT₀ : (T : Subgroup G) ≤ normalizer (T₀ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show T₀ ≤ (T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hindex)
  have hST₀ : Global.sourceS L H ≤ T₀ :=
    le_inf (Global.sourceS_le_sylow d.normalizes_L hH.1.1.2) hSR
  have h := Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient
  have hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^2) := by
    refine ⟨GaloisField 2 2,inferInstance,inferInstance,
      GaloisField.card 2 2 (by decide),?_⟩
    obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    exact ⟨d.quotient.trans e.symm⟩
  obtain ⟨_,⟨Q,hQ⟩⟩ := d.chosen.rankOne_sourceS_intersection_left h hpsl hH
  have hTN : (T : Subgroup G) ≤ normalizer (L : Set G) ⊓ normalizer (T₀ : Set G) :=
    le_inf d.normalizes_L hTT₀
  let P := T.subtype hTN
  have hP : (P : Subgroup (normalizer (L : Set G) ⊓ normalizer (T₀ : Set G) : Subgroup G)).map
      (normalizer (L : Set G) ⊓ normalizer (T₀ : Set G)).subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTN
  have hNM : normalizer (T₀ : Set G) ≤ normalizer (L : Set G) := by
    apply Chapter4.Section03.RankOneUniqueness.normalizer_le_of_uniqueness_over_local_sylow
      d.chosen h hpsl T₀ (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans d.normalizes_L) Q (hQ.le.trans (inf_le_left.trans hST₀)) P
    rw [hP]
    exact d.source_unique_sylow_join
  let W := T₀ ⊔ U
  have hW : IsPGroup 2 W :=
    (T.isPGroup'.to_le (show T₀ ≤ (T : Subgroup G) from inf_le_left)).to_sup_of_normal_right'
      (isPGroup_pCoreIn 2 N) hT₀U
  have hib := (two_group_over_index_two_sylow T T₀ W inf_le_left hindex hW le_sup_left).1
  have hWU : W ≤ normalizer (T₀ : Set G) := by
    by_cases hi₁ : T₀.relIndex W = 1
    · exact (relIndex_eq_one.mp hi₁).trans T₀.le_normalizer
    · have hip : T₀.relIndex W ≠ 0 := (T₀.subgroupOf W).index_ne_zero_of_finite
      have hi₂ : T₀.relIndex W = 2 := by omega
      exact (normal_subgroupOf_iff_le_normalizer
        (show T₀ ≤ W from le_sup_left)).mp (normal_of_index_eq_two hi₂)
  exact (show U ≤ W from le_sup_right).trans (hWU.trans hNM)

/-- The original pair core lies in the selected factor's normalizer in T.
The inputs are literal source selection clauses, with no quotient marking. -/
theorem original_selected_pair_core_le_normalizing_sylow
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : R ⊔ (T : Subgroup G) = H)
    (hind : ((T : Subgroup G) ⊓ normalizer (R : Set G)).relIndex (T : Subgroup G) ≤ 2)
    (hSR : Global.sourceS L H ≤ normalizer (R : Set G)) :
    (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 ≤
      (T : Subgroup G) ⊓ normalizer (R : Set G) := by
  let N := ChapterF.Source.generated ![L,R] (Global.sourceS L H)
  let U := N.pCoreIn 2
  let T₀ := (T : Subgroup G) ⊓ normalizer (R : Set G)
  change U ≤ T₀
  by_cases hu : U = ⊥
  · exact hu ▸ bot_le
  obtain ⟨he,hi⟩ := original_selected_pair_core_normalizer d hH hgen hind hu
  change (T : Subgroup G) ⊓ normalizer (U : Set G) = T₀ at he
  have hindex : T₀.relIndex (T : Subgroup G) = 2 := by rwa [he] at hi
  have hT₀U : T₀ ≤ normalizer (U : Set G) := he.ge.trans inf_le_right
  have hUM : U ≤ normalizer (L : Set G) := core_le_left_normalizer d hH hgen hind hSR
  let W := T₀ ⊔ U
  have hW : IsPGroup 2 W :=
    (T.isPGroup'.to_le (show T₀ ≤ (T : Subgroup G) from inf_le_left)).to_sup_of_normal_right'
      (isPGroup_pCoreIn 2 N) hT₀U
  rcases (two_group_over_index_two_sylow T T₀ W inf_le_left hindex hW le_sup_left).2 with
    hw | ⟨P,hP⟩
  · exact (show U ≤ W from le_sup_right).trans_eq hw
  · have hPM : (P : Subgroup G) ≤ normalizer (L : Set G) := by
      rw [hP]
      exact sup_le (inf_le_left.trans d.normalizes_L) hUM
    have hPU : (P : Subgroup G) ≤ normalizer (U : Set G) := by
      rw [hP]
      exact sup_le hT₀U U.le_normalizer
    have hNU : N ≤ normalizer (U : Set G) :=
      N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
    have hNM := normalizer_le_of_unique_maximalTwoLocal
      (original_normalizer_sylow_unique d P hPM) (isPGroup_pCoreIn 2 N) hu
      (sup_le ((show L ≤ N from le_sup_left.trans le_sup_left).trans hNU) hPU)
    have hRM : R ≤ normalizer (L : Set G) :=
      (show R ≤ N from le_sup_right.trans le_sup_left).trans (hNU.trans hNM)
    exact (hH.1.2 (hgen ▸ sup_le hRM d.normalizes_L)).elim

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
