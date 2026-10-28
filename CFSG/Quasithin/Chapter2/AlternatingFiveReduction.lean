module
public import CFSG.Quasithin.Chapter2.SelectedAlternatingReduction
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.FullSource

/-!
# The original Chapter 2 reduction to alternating-five blocks

The complete paired-cubic source argument now supplies the last callback
besides alternating-five blocks in the selected-block dispatcher. Its
reselection calls use the original linear exclusion and the same
alternating-five exclusion at the reselected minimal block. Thus the
original 2.1.1 consumer retains only this genuine source case, with no
component, model, action or fusion hypothesis.

Source: Aschbacher–Smith 2.4.25–37 and Theorem 2.1.1, printed pp.518,541–550.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem selected_block_classification_of_alternating_five
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hfive : ¬ IsTheorem241Model G → ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (e.block.map e.H.subtype) 5) :
    IsTheorem241Model G := by
  apply selected_block_classification_of_alternating_cases d hG T hM hTM hu hdelta hST
  · intro hn
    exact hfive hn d hST
  · intro hn hpair hL
    exact d.paired_cubic_source_false hG T hM hTM hu hdelta hn
      (fun e he _ hLe => e.linear_source_false hG T hM hTM hu hdelta he hn hLe)
      (hfive hn) hST hpair hL

/-- Every Chapter 2 source premise other than the original alternating-five
case is discharged in this application of the original 2.1.1 reduction. -/
theorem theorem_2_1_1_of_alternating_five_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfive : ∀ (M : Subgroup G) (d : MinimalBlockSetup M) (P : Sylow 2 G),
      IsMaximalTwoLocal M → (P : Subgroup G) ≤ M →
      (∀ N : Subgroup G, IsMaximalTwoLocal N → (P : Subgroup G) ≤ N → N = M) →
      (delta (Chapter1.He G) M).Nonempty →
      (d.S : Subgroup d.H).map d.H.subtype < (P : Subgroup G) →
      ¬ IsTheorem241Model G →
      ¬ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) :
    ClassificationModels.IsTheorem211Model G := by
  apply theorem_2_1_1_of_selected_block_classification hG ?_ T M hM hTM hu
  intro N d P hN hPN hPunique hdelta hSP
  exact selected_block_classification_of_alternating_five d hG P hN hPN hPunique hdelta hSP
    (fun hn e he => hfive N e P hN hPN hPunique hdelta he hn)

end CFSG.Quasithin.Chapter2
