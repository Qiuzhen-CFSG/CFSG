module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Overlap
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The centralizer kernel is the original parabolic core

The overlap centralizes the Sylow omega-center. Its normal core therefore
centralizes every H-conjugate of that seed, and hence the entire omega module.
Together with the earlier kernel containment this identifies the literal
centralizer kernel with the original maximal-overgroup core. The resulting
quotient is core-free minimal parabolic and SQTK, on the original quotient
map and prescribed Sylow image.

The internal Structure import supplies the defining equation of the core;
no shared definition or public boundary is changed.
Source: Aschbacher--Smith 10.3.1, printed pp.755--756, using B.6.8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterB ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem omegaKernel_eq_parabolicCore
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    omegaKernel T H = minimalParabolicCore (T.subtype hH.1.1.2) (hstar_minimal D s hH) := by
  apply le_antisymm (omegaKernel_le_parabolicCore D s hfix hH)
  let J := minimalParabolicCore (T.subtype hH.1.1.2) (hstar_minimal D s hH)
  have hJM : J ≤ D.maximalLocal.subgroupOf H := by
    rw [← source_hstar_parabolicMax_eq_overlap D hH (hstar_minimal D s hH)]
    exact normalCore_le _
  have hcent : J.map H.subtype ≤ centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    (show J.map H.subtype ≤ H ⊓ D.maximalLocal from le_inf (map_subtype_le _)
      (map_le_iff_le_comap.mpr hJM)).trans
      (overlap_centralizes_sylow_seed D hfaith hmany s hfix hH)
  have hnormal : H ≤ normalizer (J.map H.subtype : Set G) := by
    intro h hh
    exact J.le_normalizer_map H.subtype (mem_map_of_mem H.subtype
      (show (⟨h,hh⟩ : H) ∈ normalizer (J : Set H) from by
        rw [normalizer_eq_top]; trivial))
  have hc : omegaModule T H ≤ centralizer (J.map H.subtype : Set G) :=
    conjugateSpanBy_le (le_centralizer_iff.mp hcent)
      (hnormal.trans (normalizer_le_normalizer_centralizer _))
  rw [omegaKernel_eq D hH]
  exact map_le_iff_le_comap.mp (le_centralizer_iff.mp hc)

/-- The original quotient has no remaining maximal-overgroup core. -/
theorem omegaQuotient_parabolicCore_eq_bot
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    minimalParabolicCore
      ((T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (omegaKernel T H)))
      (omegaQuotient_minimal D s hfix hH) = ⊥ := by
  have hk : (QuotientGroup.mk' (omegaKernel T H)).ker ≤
      minimalParabolicCore (T.subtype hH.1.1.2) (hstar_minimal D s hH) := by
    rw [QuotientGroup.ker_mk']
    exact omegaKernel_le_parabolicCore D s hfix hH
  rw [← minimalParabolicCore_map_core (T.subtype hH.1.1.2) (hstar_minimal D s hH)
    (QuotientGroup.mk' (omegaKernel T H)) (QuotientGroup.mk'_surjective _) hk,
    ← omegaKernel_eq_parabolicCore D hfaith hmany s hfix hH]
  exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])

/-- E.2.2 applies to the literal centralizer quotient with the full catalogue. -/
theorem omegaQuotient_sqtk
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    IsSQTK KnownSimple.IsKnownSimple (OmegaQuotient T H) := by
  change IsSQTK KnownSimple.IsKnownSimple (H ⧸ omegaKernel T H)
  apply (IsSQTK.equiv (QuotientGroup.quotientMulEquivOfEq
    (omegaKernel_eq_parabolicCore D hfaith hmany s hfix hH))).mpr
  apply Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) (T.subtype hH.1.1.2)
    (hstar_minimal D s hH)
  intro hs
  let := hs
  have hb : generationParameter H ≤ 1 := generationParameter_le_one_of_solvable
  rw [s.generation H hH] at hb
  omega

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
