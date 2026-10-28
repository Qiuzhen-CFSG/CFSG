module
public import CFSG.Quasithin.Chapter10.SourceThompsonControl
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import CFSG.Quasithin.Chapter3.Section02.LocalModule
public import Theory.GroupTheory.UniqueMaximalNormalExtension

/-!
# Common-normal control in the original Chapter 10 parabolic

For the original L₀T, a nonzero T-invariant two-subgroup R which is Sylow
in L₀R has its full ambient normalizer in M. The source common-normal
theorem supplies a nonzero subgroup of R normal in the join with N_G(R);
uniqueness of M then gives the desired containment. No common-normal or
normalizer-control callback is retained.

The Baumann specialization is the linear branch of 10.2.1. The separate
minimal-parabolic and relative-Sylow facts are the precise earlier inputs
from 10.1.2(6) and E.2.3(2). This does not assert either the seven-row module
classification or the final component-normalization theorem 10.0.1.
Source: Aschbacher–Smith, 10.1.2(6) and 10.2.1, printed pp.742–743,
using Theorem 3.1.1, printed pp.571–572.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3 Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D

/-- The original orbit is the actual ambient image of the local two-residual. -/
theorem source_join_residual :
    (pResidual 2 (localJoin T L)).map (localJoin T L).subtype = localOrbit T L :=
  embedded_pResidual_join_pGroup (localOrbit T L) (T : Subgroup G)
    ((pResidual_eq_top_iff 2 _).mp D.orbit_residual) T.isPGroup'
    (le_normalizer_componentOrbit L T)

/-- The original local-parabolic Sylow condition controls the full ambient
normalizer, with both 3.1.1 and the earlier uniqueness theorem discharged. -/
theorem source_normalizer_le_of_orbit_sylow
    (hP : Order.HasUniqueMaximalOver (T : Subgroup G) (localJoin T L))
    (R : Subgroup G) (hne : R ≠ ⊥) (hRT : R ≤ (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hs : Chapter1.IsSylowIn 2 R (localOrbit T L ⊔ R)) :
    normalizer (R : Set G) ≤ D.maximalLocal := by
  have hp : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hN : normalizer (R : Set G) ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, hn⟩
    have hc := le_pCoreIn_of_normalizes hp R.le_normalizer (le_refl (normalizer (R : Set G)))
    exact fun he => hne (bot_unique (hc.trans_eq he))
  have hH : localJoin T L ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, show (T : Subgroup G) ≤ localJoin T L from le_sup_right⟩
    exact fun he => D.module_ne_bot (bot_unique (D.module_le_core.trans_eq he))
  have hs' : Chapter1.IsSylowIn 2 R
      ((pResidual 2 (localJoin T L)).map (localJoin T L).subtype ⊔ R) := by
    rwa [source_join_residual D]
  obtain ⟨N, hNR, hneN, hnormal⟩ := Chapter3.source_common_normal_knownSimple
    D.simpleQTKE T (normalizer (R : Set G)) (localJoin T L) R
    hN hH hP hne hRT hs' le_rfl
  have hnN := (normalIn_iff_le_normalizer.mp hnormal).2
  rw [generated_eq_sup] at hnN
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact (le_sup_left.trans hnN).trans
    (normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness hu).2.2
      (hp.to_le hNR) hneN (le_sup_right.trans hnN))

/-- The relative-Sylow conclusion of E.2.3(2) is sufficient for the linear
branch of 10.2.1, on the literal Baumann subgroup of the original T. -/
theorem source_baumann_normalizer_le_of_orbit_sylow
    (hP : Order.HasUniqueMaximalOver (T : Subgroup G) (localJoin T L))
    (hs : Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (localOrbit T L ⊔ ChapterB.baumann (T : Subgroup G))) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  have hT : (T : Subgroup G) ≠ ⊥ :=
    fun he => D.module_ne_bot (bot_unique (D.module_le_sylow.trans_eq he))
  have hJ := elementaryAbelianMaxJ_ne_bot_of_finite_pGroup (T : Subgroup G) T.isPGroup' hT
  apply source_normalizer_le_of_orbit_sylow D hP _
    (fun he => hJ (bot_unique ((ChapterB.elementaryAbelianMaxJ_le_baumann _).trans_eq he)))
    inf_le_left _ hs
  exact (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)

end CFSG.Quasithin.Chapter10
