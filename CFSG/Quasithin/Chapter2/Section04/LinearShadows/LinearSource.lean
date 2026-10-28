module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Source
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.Source
/-!
# The original linear-block source exclusion

The single and paired source arguments exclude every original even linear
block in the selected minimal setup. This is the literal prior-case input
used by the paired-cubic reselection and the final Section 2.4 dispatcher.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem MinimalBlockSetup.linear_source_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hcounter : ¬IsTheorem241Model G)
    {n:ℕ} (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) : False := by
  by_cases hsingle : d.L0=d.block
  · exact d.single_linear_source_false hG T hM hTM hu hdelta hST hcounter hsingle hL
  · exact d.double_linear_source_false hG T hM hTM hu hdelta hST hcounter hsingle hL
end CFSG.Quasithin.Chapter2
