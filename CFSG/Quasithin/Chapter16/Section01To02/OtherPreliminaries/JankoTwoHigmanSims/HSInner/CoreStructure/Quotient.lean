module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient

/-!
# The S₅ quotient in the central HS involution extension

The fixed-pair action gives an actual surjection from `localGroup 0` onto S₅,
with kernel exactly `CentralInvolutionCore.core`. The first isomorphism theorem
therefore proves the quotient clause of the extension in Aschbacher–Smith
16.1.5(10), printed p.1172, and GLS3 Table 5.3m. Normality is inside this exact
local group. No local order, kernel order, or splitting is assumed.

The kernel's internal central-product structure is assembled separately in
`CoreStructure`; this module supplies its unconditional quotient input.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
open Sporadic.LeechRelated.HS.EvenLocalCandidates
open CentralInvolutionCore

attribute [local instance] core_normal

/-- The exact pair-kernel quotient of the full first HS local is S₅. -/
theorem core_quotient_equiv_s5 : Nonempty ((localGroup 0) ⧸ core ≃* S5) :=
  ⟨CentralNormalizerThreePart.PairQuotient.quotientEquiv⟩

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
