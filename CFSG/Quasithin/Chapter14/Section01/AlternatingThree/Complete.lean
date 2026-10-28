module
public import CFSG.Quasithin.Chapter14.Section01.AlternatingThree.Source
public import CFSG.Quasithin.Chapter13.Section09.Source

/-!
# Applying the proved wreath exclusion at the original source boundary

The genuine 13.9.1 theorem is applied to the literal original configuration.
Its callback is therefore discharged; the earlier public theorem and its
original subgroup, Sylow and module hypotheses are preserved.

Source: Aschbacher--Smith 13.9.1, 14.1.10 and 15.3--15.4.25.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.AlternatingThree
open AlternatingFourPair
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_lemma_14_1_10_complete
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (X R : Subgroup M) (hb : ChapterC.IsBlock X) (ha : ChapterC.IsAlternatingBlock X 3)
    (hQR : pCore 2 M ≤ R) (_hRT : R ≤ (T.subtype hM.2 : Subgroup M))
    (hm : X = ⁅X,elementaryAbelianMaxJ R⁆) :
    M = Mc ∧ 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G)) := by
  exact source_lemma_14_1_10 (fun _ _ _ h d => Chapter13.Section09.source13_9_1 h d) hG T hM hu hmany X R hb ha hQR _hRT hm

end CFSG.Quasithin.Chapter14.AlternatingThree
