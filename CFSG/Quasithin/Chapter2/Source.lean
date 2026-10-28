module
public import CFSG.Quasithin.Chapter2.AlternatingFiveRemaining
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSingleSource

/-!
# The original unique-overgroup classification

The source exclusion of the final single alternating-five case discharges
the last input to the original Chapter 2 reduction. All statements concern
the original ambient group and its unique maximal two-local overgroup.

Source: Aschbacher–Smith, Theorem 2.1.1, printed p.518; the final
alternating-five exclusion is 2.4.29, printed pp.545–546.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G]

theorem theorem_2_1_1
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) :
    ClassificationModels.IsTheorem211Model G := by
  apply theorem_2_1_1_of_remaining_single_alternating_five hG ?_ T M hM hTM hu
  intro N d P hN hPN hPu hdelta hSP hcounter hsingle hA hD
  exact d.single_alternating_trivial_centralizer_false
    hG P hN hPN hPu hdelta hcounter hSP hsingle hA hD

end CFSG.Quasithin.Chapter2
