module
public import CFSG.Quasithin.Chapter2.Source
public import CFSG.Quasithin.MainForward

/-!
# The forward classification after the complete Chapter 2 source proof

The unique-overgroup case is discharged by the original Theorem 2.1.1.
Only the genuine multiple-overgroup source theorems D and E remain as
inputs to the full forward classification, with its complete output list.

Source: Aschbacher–Smith, Main Theorem, printed p.1166.
-/
public section
namespace CFSG.Quasithin.MainForward
open Subgroup Theory.GroupTheory ClassificationModels
variable {G : Type*} [Group G] [Finite G]

theorem forward_of_theoremsD_and_E
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hD : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      (faithfulLocalComponents T).Nonempty → IsTheoremDModel G)
    (hE : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      faithfulLocalComponents T = ∅ → IsTheoremEModel G) : IsQTKEModel G := by
  have h211 (T : Sylow 2 G)
      (hu : ∃! M : Subgroup G, IsMaximalTwoLocal M ∧ (T : Subgroup G) ≤ M) :
      IsTheorem211Model G := by
    obtain ⟨M,⟨hM,hTM⟩,hunique⟩ := hu
    exact Chapter2.theorem_2_1_1 h T M hM hTM (fun N hN hTN => hunique N ⟨hN,hTN⟩)
  rcases forward_to_theoremD h h211 hE with hmodel | ⟨T,hmany,hnonempty⟩
  · exact hmodel.toQTKEModel
  · exact (hD T hmany hnonempty).toQTKEModel

end CFSG.Quasithin.MainForward
