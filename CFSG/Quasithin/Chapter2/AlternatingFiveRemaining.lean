module
public import CFSG.Quasithin.Chapter2.AlternatingFiveReduction
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingNontrivialSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPairSource

/-!
# The remaining single alternating-five input to Theorem 2.1.1

The single alternating-five case with nontrivial Sylow centralizer is impossible.
The paired case is also impossible by the original 2.4.25 source proof. Thus the
classification follows from precisely the remaining single-case exclusion with
trivial Sylow centralizer.

The proof applies both reductions to the actual minimal block and its selected
Sylow subgroup. Source: Aschbacher--Smith, Theorems 2.1.1 and 2.4.1, with the
alternating-five cases in 2.4.25 and 2.4.29.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem theorem_2_1_1_of_remaining_single_alternating_five
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hzero : ∀ (N : Subgroup G) (d : MinimalBlockSetup N) (P : Sylow 2 G),
      IsMaximalTwoLocal N → (P : Subgroup G) ≤ N →
      (∀ J : Subgroup G, IsMaximalTwoLocal J → (P : Subgroup G) ≤ J → J = N) →
      (delta (Chapter1.He G) N).Nonempty →
      (d.S : Subgroup d.H).map d.H.subtype < (P : Subgroup G) →
      ¬ IsTheorem241Model G → d.L0 = d.block →
      IsAlternatingBlock (d.block.map d.H.subtype) 5 →
      (P : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥ → False)
    (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) :
    ClassificationModels.IsTheorem211Model G := by
  apply theorem_2_1_1_of_alternating_five_exclusion hG ?_ T M hM hTM hu
  intro N d P hN hPN hPu hdelta hSP hcounter hA
  have hsingle := d.alternating_five_single_source hG P hN hPN hPu hSP hA
  by_cases hD : (P : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥
  · exact hzero N d P hN hPN hPu hdelta hSP hcounter hsingle hA hD
  · exact d.single_alternating_nontrivial_centralizer_false hG P hN hPN hPu hSP hsingle hA hD

end CFSG.Quasithin.Chapter2
