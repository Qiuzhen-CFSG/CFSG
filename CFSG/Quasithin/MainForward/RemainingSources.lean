module
public import CFSG.Quasithin.MainForward
public import CFSG.Quasithin.Chapter2.AlternatingFiveRemaining
public import CFSG.Quasithin.Chapter2.AlternatingFiveComplete

/-!
# The remaining source inputs in the forward Main Theorem

The unique-overgroup case now needs only the original single alternating-five
exclusion with trivial Sylow centralizer. The other two cases are exactly the
nonempty faithful-component family of Theorem D and the empty family of
Theorem E. Their conclusions are transported into the complete Main Theorem
list, including the Ree family.

This final composition keeps those unproved source inputs explicit. Source:
Aschbacher--Smith, the proof of the Main Theorem on printed p.1166.
-/

public section
namespace CFSG.Quasithin.MainForward
open Subgroup Theory.GroupTheory ClassificationModels
variable {G : Type*} [Group G] [Finite G]

theorem forward_of_remaining_sources
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hzero : ∀ (N : Subgroup G) (d : Chapter2.MinimalBlockSetup N) (P : Sylow 2 G),
      IsMaximalTwoLocal N → (P : Subgroup G) ≤ N →
      (∀ J : Subgroup G, IsMaximalTwoLocal J → (P : Subgroup G) ≤ J → J = N) →
      (Chapter2.delta (Chapter1.He G) N).Nonempty →
      (d.S : Subgroup d.H).map d.H.subtype < (P : Subgroup G) →
      ¬ Chapter2.IsTheorem241Model G → d.L0 = d.block →
      ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5 →
      (P : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥ → False)
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
    exact Chapter2.theorem_2_1_1_of_remaining_single_alternating_five h hzero T M hM hTM
      (fun N hN hTN => hunique N ⟨hN,hTN⟩)
  rcases forward_to_theoremD h h211 hE with hmodel | ⟨T,hmany,hnonempty⟩
  · exact hmodel.toQTKEModel
  · exact (hD T hmany hnonempty).toQTKEModel

/-- Forward classification with the single alternating-five source discharged.

The legacy dispatcher above keeps its explicit `hzero` argument for clients
that assemble source branches independently.  This route uses the complete
2.4.29 source adapter, so callers only provide the genuine multiple-overgroup
Theorem D and E branches.
-/
theorem forward_of_complete_alternating_five_source
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hD : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      (faithfulLocalComponents T).Nonempty → IsTheoremDModel G)
    (hE : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      faithfulLocalComponents T = ∅ → IsTheoremEModel G) : IsQTKEModel G := by
  apply forward_of_remaining_sources h ?_ hD hE
  exact Chapter2.single_alternating_five_exclusion_complete h

end CFSG.Quasithin.MainForward
