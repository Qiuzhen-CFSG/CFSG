module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.LocalCore
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.Cover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.ClassicalCover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.ExceptionalCover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.AlternatingCover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.DerivedG2Cover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.BinaryTitsCover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.RankOneCover
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.QuotientModels

/-!
# Properness of the rank-two quotient Borel hull

The local configuration supplies a nontrivial two-core in the component
intersection. Intrinsic model coverage then puts its normalizer together with
the actual component Sylow normalizer in a proper subgroup. Coverage is proved
for the complete source catalogue, retaining central covers, rank-one groups,
binary linear groups, triality at two, the small derived groups and A₆.
The final theorem discharges every coverage input using the actual component's
simplicity and perfectness; it asserts properness of the candidate hull.

Source: Aschbacher--Smith, 15.3.41, printed p.1138, and the first paragraph of
the final proof of 15.3.35, printed p.1139; the complete action alternatives
are 1.1.5(3)(a)--(c), printed pp.501--502.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection

variable {G : Type*} [Group G] [Finite G]
variable {L MI Yplus S : Subgroup G} [L.Normal]

/-- The geometric input concerns an actual nontrivial two-subgroup of the
component; the local configuration constructs it without a four-group premise. -/
theorem quotient_borel_join_proper_of_normalizer_cover (d : Setup L MI Yplus S)
    (hcover : BorelHull.TwoSubgroupNormalizerCover (centralizerQuotientComponent L)) :
    sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) ⊔
      (MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L) <
        centralizerQuotientComponent L := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let N := MI.map q
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨R, hR, hpR, hNR⟩ := BorelHull.component_twoSubgroup_for_cover d.quotient_local
  obtain ⟨P, hP⟩ := d.quotient_component_sylow
  apply (quotient_borel_join_proper_iff P hP).mpr
  have hPN : (P : Subgroup D) ≤ N.subgroupOf D := by
    intro x hx
    have hx' : (x : CentralizerQuotient L) ∈ S.map q ⊓ D := by
      rw [← hP]
      exact mem_map_of_mem D.subtype hx
    exact d.quotient_local.sylow_le hx'.1
  exact lt_of_le_of_lt (sup_le_sup_left hNR _)
    (hcover P R hR hpR (hPN.trans hNR))

/-- Every larger-field rank-two case supplies the required intrinsic coverage. -/
theorem BorelHull.largerField_twoSubgroupNormalizerCover
    {K : Type*} [Group K] [Finite K] (hK : LargerFieldRankTwoModel K) :
    BorelHull.TwoSubgroupNormalizerCover K := by
  cases hK with
  | linear n hn hm => exact BorelHull.linear_twoSubgroupNormalizerCover hn hm
  | symplectic n hn hm => exact BorelHull.symplectic_twoSubgroupNormalizerCover hn hm
  | g2 n _ hm => exact BorelHull.g2_twoSubgroupNormalizerCover hm
  | triality n hn hm => exact BorelHull.triality_twoSubgroupNormalizerCover (by omega) hm
  | ree m hm hK => exact BorelHull.ree_twoSubgroupNormalizerCover hm hK

/-- Properness is unconditional within each of the larger-field alternatives. -/
theorem quotient_borel_join_proper_of_largerField (d : Setup L MI Yplus S)
    (hm : LargerFieldRankTwoModel (centralizerQuotientComponent L)) :
    sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) ⊔
      (MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L) <
        centralizerQuotientComponent L :=
  quotient_borel_join_proper_of_normalizer_cover d
    (BorelHull.largerField_twoSubgroupNormalizerCover hm)

/-- The degree-one triality branch is retained and covered directly. -/
theorem quotient_borel_join_proper_of_triality_two (d : Setup L MI Yplus S)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (centralizerQuotientComponent L)) :
    sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) ⊔
      (MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L) <
        centralizerQuotientComponent L :=
  quotient_borel_join_proper_of_normalizer_cover d
    (BorelHull.triality_twoSubgroupNormalizerCover (n := 1) (by decide) hm)

/-- The complete source catalogue reduces properness to the remaining rank-one,
binary linear and Tits coverage calculations. All other branches are discharged
here, including central covers, triality at two and both small derived groups.
The source-theorem owner must prove the three explicit inputs. -/
theorem quotient_borel_join_proper_of_remaining_covers
    (d : Setup L MI Yplus S) {z : G} {α : MulAut L} (a : SourceAction L S z α)
    (hrankOne : ClassificationModels.IsBenderModel (centralizerQuotientComponent L) →
      BorelHull.TwoSubgroupNormalizerCover (centralizerQuotientComponent L))
    (hbinary : SmallBinaryModel (centralizerQuotientComponent L) →
      BorelHull.TwoSubgroupNormalizerCover (centralizerQuotientComponent L))
    (htits : Nonempty (centralizerQuotientComponent L ≃* Tits.ParrottGroup) →
      BorelHull.TwoSubgroupNormalizerCover (centralizerQuotientComponent L)) :
    sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) ⊔
      (MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L) <
        centralizerQuotientComponent L := by
  let := d.quasisimple
  let : IsSimpleGroup (centralizerQuotientComponent L) := centralizerQuotientComponent_simple L
  let : IsQuasisimple (centralizerQuotientComponent L) :=
    IsQuasisimple.of_surjective ((centralizerQuotientMap L).subgroupMap L)
      ((centralizerQuotientMap L).subgroupMap_surjective L)
  apply quotient_borel_join_proper_of_normalizer_cover d
  rcases component_model_cases L a.alternatives with hm | hm | hm
  · exact hbinary hm
  · exact BorelHull.largerField_twoSubgroupNormalizerCover hm
  · cases hm with
    | rank_one hm => exact hrankOne hm
    | linear_three_two hm => exact (d.not_linear_three_two hm).elim
    | triality_two hm =>
        exact BorelHull.triality_twoSubgroupNormalizerCover (n := 1) (by decide) hm
    | symplectic_derived hm => exact BorelHull.symplectic_derived_twoSubgroupNormalizerCover hm
    | g2_derived hm => exact BorelHull.g2_derived_twoSubgroupNormalizerCover hm
    | tits hm => exact htits hm
    | alternating_six hm => exact BorelHull.alternating_six_twoSubgroupNormalizerCover hm

/-- The candidate Borel hull in the actual centralizer quotient is proper.
All model coverage premises are discharged from the complete source catalogue. -/
theorem quotient_borel_join_proper
    (d : Setup L MI Yplus S) {z : G} {α : MulAut L} (a : SourceAction L S z α) :
    sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) ⊔
      (MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L) <
        centralizerQuotientComponent L := by
  let := d.quasisimple
  let : IsSimpleGroup (centralizerQuotientComponent L) := centralizerQuotientComponent_simple L
  let : IsQuasisimple (centralizerQuotientComponent L) :=
    IsQuasisimple.of_surjective ((centralizerQuotientMap L).subgroupMap L)
      ((centralizerQuotientMap L).subgroupMap_surjective L)
  exact quotient_borel_join_proper_of_remaining_covers d a
    BorelHull.rankOne_twoSubgroupNormalizerCover
    BorelHull.binary_twoSubgroupNormalizerCover
    BorelHull.tits_twoSubgroupNormalizerCover

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
