module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSelectedFamilyCoreOrbit
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSourceCoreNormalizer
public import Theory.GroupTheory.SylowIndexTwoOvergroup

/-!
# The selected generated core lies in the original left normalizer

For a nonzero selected pair core U, its normalizer T₀ in the original
Sylow equals the selected factor normalizer and has index two. The source
core S lies in T₀ and contains the full Sylow intersection with L.
The genuine 4.3.1 normalizer theorem therefore puts N_G(T₀) in N_G(L).

T₀ normalizes U, so UT₀ is a two-group. Its index over T₀ is at most two
by the ambient Sylow bound. Thus T₀ is normal in UT₀, and U lies in its
normalizer. This proves containment in N_G(L), while retaining both the
selected factor and its actual generated core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G} {ℛ : Set (Subgroup G)}

/-- Every original selected pair core lies in N_G(L). The actual source
family supplies the normalizer index and all Sylow containments. -/
theorem original_selected_pair_core_le_left_normalizer
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (geom : Global.RightGeometry T L H ℛ) (hR : R ∈ ℛ) :
    (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 ≤
      normalizer (L : Set G) := by
  let N := ChapterF.Source.generated ![L,R] (Global.sourceS L H)
  let U := N.pCoreIn 2
  change U ≤ normalizer (L : Set G)
  by_cases hu : U = ⊥
  · exact hu ▸ bot_le
  let T₀ := (T : Subgroup G) ⊓ normalizer (R : Set G)
  obtain ⟨he,hi⟩ := original_selected_family_core_normalizer d hH geom hR hu
  change (T : Subgroup G) ⊓ normalizer (U : Set G) = T₀ at he
  have hindex : T₀.relIndex (T : Subgroup G) = 2 := by rwa [he] at hi
  have hT₀U : T₀ ≤ normalizer (U : Set G) := he.ge.trans inf_le_right
  have hTT₀ : (T : Subgroup G) ≤ normalizer (T₀ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show T₀ ≤ (T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hindex)
  have hST₀ : Global.sourceS L H ≤ T₀ :=
    le_inf (Global.sourceS_le_sylow d.normalizes_L hH.1.1.2) (geom.S_normalizes R hR)
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

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
