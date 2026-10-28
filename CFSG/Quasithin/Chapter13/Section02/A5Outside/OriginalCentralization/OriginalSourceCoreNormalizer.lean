module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Normalizer
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NormalizedResidualF11
public import CFSG.Quasithin.Chapter4.Section03.A5.SourceSetup

/-!
# The original source core has its full normalizer in N(L)

The original ambient Sylow normalizes S=O₂(N(L)∩H), and S contains its
full intersection with L. The rank-one source form of 4.3.1 applies with
this same Sylow and the proved uniqueness over LT. No uniqueness over L,
alternating-block conclusion, or selected-right-factor normalization is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- The full normalizer of the literal source core lies in the original
left normalizer, using only actual Sylow-join uniqueness. -/
theorem original_source_core_normalizer_le
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    normalizer (Global.sourceS L H : Set G) ≤ normalizer (L : Set G) := by
  let S := Global.sourceS L H
  have h := Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient
  have hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^2) := by
    refine ⟨GaloisField 2 2,inferInstance,inferInstance,
      GaloisField.card 2 2 (by decide),?_⟩
    obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    exact ⟨d.quotient.trans e.symm⟩
  obtain ⟨hleft,⟨Q,hQ⟩⟩ := d.chosen.rankOne_sourceS_intersection_left h hpsl hH
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (le_inf d.normalizes_L hH.1.1.2).trans (Global.intersection_normalizes_sourceS L H)
  have hTN : (T : Subgroup G) ≤ normalizer (L : Set G) ⊓ normalizer (S : Set G) :=
    le_inf d.normalizes_L hTS
  let P := T.subtype hTN
  have hP : (P : Subgroup (normalizer (L : Set G) ⊓ normalizer (S : Set G) : Subgroup G)).map
      (normalizer (L : Set G) ⊓ normalizer (S : Set G)).subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTN
  apply Chapter4.Section03.RankOneUniqueness.normalizer_le_of_uniqueness_over_local_sylow
    d.chosen h hpsl S (pCore_isPGroup.map _)
    ((Global.sourceS_le_sylow d.normalizes_L hH.1.1.2).trans d.normalizes_L)
    Q (hQ.le.trans inf_le_left) P
  rw [hP]
  exact d.source_unique_sylow_join

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
