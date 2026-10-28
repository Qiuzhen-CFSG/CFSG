module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Qrc.Configuration
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement

/-!
# Supplement uniqueness implies Thompson movement

The multiple-overgroup guard supplies the actual HStar comparison group.
The canonical qrc configuration and (+) exclude the central omega
alternative. Source 3.1.7, through its proved noncentral movement theorem,
then excludes J₀(T)≤R whenever the canonical supplement has a unique
maximal two-local overgroup. The source commutator dichotomy gives
L=[L,J₀(T)] with the repository's elementary Thompson convention.

This is the implication 13.1.9(1)→(2). The FF contradiction must still
establish uniqueness; qt-d-1317-supplements retains that final assembly.
Canonical starred membership remains with qt-d-1317-source for discharge.
Source: Aschbacher--Smith 13.1.9, printed p.869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

theorem thompson_movement_of_canonical_uniqueness
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      canonicalSupplement T L ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G)) :
    L = ⁅L,ChapterB.thompsonJ (T : Subgroup G) 0⁆ := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hM := (Escape.nonquasisimple_centralizer_unique_of_stars h hmany hs hL hn).1
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany _ hM hTL)
  have hq := canonical_qrc_hypotheses h hmany hs hL hn hH
  have hm := hq.thompson_moves_of_noncentral_omega h.simpleQTKE hM hu
    (canonicalReducedModule_ne_bot h hmany hL hn)
    (comparison_omegaCenter_not_central h hmany hs hL hn hH)
  apply (thompson_movement_or_le_radicalSylowCentralizer hL.1.1 hTL).resolve_right
  intro hJ
  apply hm
  rw [← ChapterB.thompsonJ_zero]
  exact thompson_centralizes_canonicalReducedModule h hmany hL hn hJ

/-- The literal uniqueness assertion for every radical supplement implies
source 13.1.9(2); the canonical supplement is constructed, not assumed. -/
theorem thompson_movement_of_supplement_uniqueness
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hu : ∀ B ∈ radicalSupplements T L, ∀ N : Subgroup G, IsMaximalTwoLocal N →
      B ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G)) :
    L = ⁅L,ChapterB.thompsonJ (T : Subgroup G) 0⁆ :=
  thompson_movement_of_canonical_uniqueness h hmany hs hL hn
    (hu _ (canonical_frattini_geometry h hmany hL hn).1)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
