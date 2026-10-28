module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.SourceConfigurations

/-!
# The degree-four second-stage core contradiction

E.3.28 makes the actual offender image have rank at least four. E.3.32 puts
its corank-three core inside the reverse normalizer, which has corank at
least two. Hence the finite H.9.3 bound that the same core has corank at
most one rules out the offender.

The finite action-geometry bound is explicit and remains to be proved;
this module supplies its exact original chosen-orbit consumer.
Source: Aschbacher--Smith, 12.1.10, printed p.794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
include h D

/-- The remaining finite core estimate has this literal second-stage application. -/
theorem doubledFour_globalW_gt_two_of_many_of_core_bound
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hcore : ∀ I : Subgroup (Automizer (componentOrbit V (T : Subgroup G))),
      IsElementaryAbelian 2 I → 4 ≤ rank I →
      subgroupCorank (componentOrbit V (T : Subgroup G))
        (automizerDualCore (componentOrbit V (T : Subgroup G)) I 3) ≤ 1)
    (hw : 1 < globalW (componentOrbit V (T : Subgroup G)) T)
    (hr : (6 : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G))) :
    2 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  by_contra hf
  obtain ⟨g, _, _, hc⟩ := D.doubled_second_configuration_of_many h hmany B hw hr hf
  have hlow := hc.corank_core_ge (by decide : 2 + 3 < 4 + 2)
  have hupp := hcore _ (offender_inducedAutomizer_elementary _ g) hc.rank_lower
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
