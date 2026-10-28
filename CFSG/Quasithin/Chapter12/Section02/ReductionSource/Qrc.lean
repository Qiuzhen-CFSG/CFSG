module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.Chapter3.Section02.FundamentalModule
/-!
# The original qrc configuration for a Section 12.2 chosen module

The exact chosen subgroup is embedded into its Fundamental Setup. The
source A and C uniqueness theorem and the genuine FSU actor construction
discharge maximality, residual, normality and internal-actor requirements
of 3.2.2(9). For every original comparison overgroup Y, this gives the actual
D.1.1 configuration on LT and the T-orbit of V.

This supplies the input to the independent source 3.1.8 ratio theorem. It
neither assumes nor claims a cubic-ratio bound or the later module list.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
3.2.2(9) and 3.2.5, pp.579--580, applied in 12.2.2 and 13.1.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hA : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
  (hC : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
include D h hA hC

/-- All qrc data use the same L, T, V and comparison subgroup Y. -/
theorem qrc_configuration {Y : Subgroup G}
    (hY : Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ChapterD.QRCConfiguration (L ⊔ (T : Subgroup G)) Y (T : Subgroup G)
      (componentOrbit V (T : Subgroup G)) := by
  let F := D.fundamentalSetup h
  have hu := F.lemma_3_2_3_uniqueness
    (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC hA hC
      h.simpleQTKE T h.maximal_faithful.1)
  have hY' : Y ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := by
    change Y ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (Chapter3.Section02.localOrbit T L : Set G))
    rwa [D.localOrbit_eq]
  have hq := Chapter3.Section02.source_reduced_seed_qrc_configuration T
    (Chapter3.Section02.localOrbit T L) F.maximalLocal
    (Chapter3.Section02.localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    F.simpleQTKE hu.1 F.internal_actor_residual F.internal_actor_cases
    F.seedSpace F.homogeneous.isIrrPlus hu.2.2 hY'
  change ChapterD.QRCConfiguration
    (Chapter3.Section02.localOrbit T L ⊔ (T : Subgroup G)) Y (T : Subgroup G)
    (componentOrbit F.seed (T : Subgroup G)) at hq
  rw [D.localOrbit_eq, D.fundamentalSetup_seed h] at hq
  exact hq
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
