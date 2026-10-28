module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.SecondReduction
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LargeSporadic.JankoFour.SecondLocal
/-! Source 2.4.25: the selected alternating-five block has a single Sylow
conjugate. The paired case is reduced using its original half-Sylow actor,
ordinary component, and faithful two-core quotient. Native J4 five-action
movement discharges the last involution-centralizer obstruction.
Source: Aschbacher--Smith, printed pp.541--543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.alternating_five_single_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) : d.L0 = d.block := by
  exact d.alternating_five_single_of_second hG T hM hTM hu hST hA
    (fun A hA _ S => AlternatingTerminal.JankoFour.second_not_local_alternating_five A hA S)
end CFSG.Quasithin.Chapter2
