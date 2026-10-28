module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Setup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Consequences
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic
public import Theory.GroupTheory.TwoLocalCharacteristicControl

/-!
# Placement and reducedness of the doubled chosen orbit

The original Irr⁺ choice gives the elementary nonzero T-normal orbit W.
Uniqueness for LT controls N_G(W). When W equals the full normalizer
orbit, this proves N_G(W) = N_G(L). The proved source A and C theorems
also make that same W reduced in N_G(L). The multiple-overgroup
hypothesis supplies the actual outside H* witness.

These are the setup inputs to 12.1.11 in the proof of 12.2.2, not the
missing weak-closure exclusion. Source: Aschbacher--Smith, pp.579,794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
include D h

include D in
theorem doubledOrbit_elementary : IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G)) := by
  have he := (D.fundamentalSetup h.toHypothesis1221).module_elementary
  rwa [D.fundamentalSetup_module] at he

include D in
theorem doubledOrbit_E322 :
    letI := D.doubledOrbit_elementary h
    ChapterE.HypothesisE322 (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  let F := D.fundamentalSetup h.toHypothesis1221
  refine ⟨?_, ?_, le_normalizer_componentOrbit _ _⟩
  · simpa only [F, D.fundamentalSetup_module] using F.module_ne_bot
  · simpa only [F, D.fundamentalSetup_module] using F.module_le_sylow

include D in
theorem doubledOrbit_normalizer_eq
    (he : componentOrbit V (T : Subgroup G) = componentOrbit V (normalizer (L : Set G))) :
    normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G) := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have hn := D.normal_subgroup_normalizer_le h.toHypothesis1221
    (F.module_le_sylow.trans le_sup_right) F.module_ne_bot
    (by simpa only [Chapter3.Section02.localJoin, D.localOrbit_eq] using F.join_normalizes_module)
  rw [D.fundamentalSetup_module] at hn
  refine le_antisymm hn ?_
  rw [he]
  exact le_normalizer_componentOrbit _ _

include D in
theorem doubledOrbit_reduced
    (he : componentOrbit V (T : Subgroup G) = componentOrbit V (normalizer (L : Set G))) :
    IsPReduced 2 ((componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (L : Set G))) := by
  rw [he]
  exact D.normalizerOrbit_reduced h.toHypothesis1221
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))

include D in
theorem doubledNormalizer_unique :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
        N = normalizer (L : Set G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hr := (D.fundamentalSetup h.toHypothesis1221).lemma_3_2_3_uniqueness hu
  simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal,
    Chapter3.Section02.localJoin, D.localOrbit_eq] using And.intro hr.1 hr.2.2

/-- The sole ambient guard is the actual multiple-overgroup branch. -/
theorem doubledOrbit_outside_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
  have hout := Chapter3.hasMaximalOutside_of_many T hmany _
    (D.doubledNormalizer_unique h).1 D.sylow_normalizes_component
  exact Chapter3.exists_HStar_of_hasMaximalOutside hout

/-- The earlier source 3.2.2(8) identifies C_T(W) with the original two-core. -/
theorem doubledOrbit_sylow_centralizer :
    (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hc := (D.fundamentalSetup h.toHypothesis1221).sylow_centralizer_module hu
  simpa only [D.fundamentalSetup_module, Chapter3.Section02.localJoin, D.localOrbit_eq] using hc

/-- The literal uniqueness premise of E.3.35, without a core equality premise. -/
theorem doubledOrbit_centralizer_unique :
    maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) :
        Subgroup G) : Set G)) = {normalizer (L : Set G)} := by
  rw [D.doubledOrbit_sylow_centralizer h]
  exact unique_twoLocal_overgroup_normalizer (isPGroup_pCoreIn 2 _)
    h.maximal_faithful.1.1.2.2
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    (D.doubledNormalizer_unique h).1 (D.doubledNormalizer_unique h).2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
