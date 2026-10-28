module
public import CFSG.Quasithin.MainForward.Chapter2Source
public import CFSG.Quasithin.Chapter2.SourceReduction

/-!
# The selected-block source obligation in the forward classification

The complete Section 2.5 contradiction and the original minimal-block
selection remove the earlier Chapter 2 premises from the forward caller.
Its remaining Chapter 2 input is the classification of the actual selected
block under the original unique maximal-local hypotheses. Theorem E remains
an independent source input.

Source: Aschbacher–Smith, Theorem 2.1.1 and the Main Theorem, printed
pp.518–570 and 1166.
-/
public section
namespace CFSG.Quasithin.MainForward
open Subgroup Theory.GroupTheory ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- The actual forward consumer with every earlier Chapter 2 source premise
discharged, leaving precisely its selected-block classification. -/
theorem forward_to_theoremD_of_selected_block_classification
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hblock : ∀ (M : Subgroup G) (d : Chapter2.MinimalBlockSetup M) (P : Sylow 2 G),
      IsMaximalTwoLocal M → (P : Subgroup G) ≤ M →
      (∀ N : Subgroup G, IsMaximalTwoLocal N → (P : Subgroup G) ≤ N → N = M) →
      (Chapter2.delta (Chapter1.He G) M).Nonempty →
      (d.S : Subgroup d.H).map d.H.subtype < (P : Subgroup G) →
      Chapter2.IsTheorem241Model G)
    (hE : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      faithfulLocalComponents T = ∅ → IsTheoremEModel G) :
    IsQTKEModelWithoutReeF4 G ∨
      ∃ T : Sylow 2 G,
        1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard ∧
        (faithfulLocalComponents T).Nonempty := by
  apply forward_to_theoremD_of_nonempty_delta h ?_ hE
  intro T M hM hTM hu _hd
  exact Chapter2.theorem_2_1_1_of_selected_block_classification h hblock T M hM hTM hu

end CFSG.Quasithin.MainForward
