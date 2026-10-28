module
public import CFSG.Quasithin.Chapter2.SourceReduction
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.LinearSource
/-!
# Selected-block reduction after the original linear exclusions

The complete source argument for both linear block configurations removes
the linear callback from the actual 2.4.1 selected-block consumer. Only the
independent alternating-five and paired-cubic source cases remain.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem selected_block_classification_of_alternating_cases
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hfive : ¬ IsTheorem241Model G →
      ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5 → False)
    (hpair : ¬ IsTheorem241Model G → d.L0 ≠ d.block →
      ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3 → False) :
    IsTheorem241Model G := by
  apply selected_block_classification_of_terminal_cases d hG T hM hTM hu hdelta hST
  · intro hn n hL
    exact d.linear_source_false hG T hM hTM hu hdelta hST hn hL
  · exact hfive
  · exact hpair
end CFSG.Quasithin.Chapter2
