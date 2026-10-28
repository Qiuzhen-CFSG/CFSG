module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralNormalizer.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer.CoreCentralizer

/-!
# Centralizer control for the literal max1 two-core

The shared reduction identifies the embedded local kernel with the whole
literal two-core. Transporting the ambient kernel centralizer calculation
along that equality proves the requested max1 containment and, more strongly,
self-centralization of this core in J₄.

Source: GLS3, Table 5.3i, printed p.270. The ambient proof uses the certified
max1 seed-centralizer bound, as explained in the imported Theory leaf.
-/

public section

open Subgroup Janko4
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry

/-- The centralizer of the whole literal two-core lies in the literal max1 subgroup. -/
theorem literalCoreCentralizerControl : LiteralCoreCentralizerControl := by
  change centralizer (certifiedMathieuSubgroup.pCoreIn 2 : Set Model) ≤
    certifiedMathieuSubgroup
  rw [literalCore_eq_embedded_localKernel]
  exact LocalStructure.centralizer_embedded_localKernel_le_max1

/-- The whole literal two-core is self-centralizing in the ambient matrix group. -/
theorem literalCore_centralizer_eq :
    centralizer (certifiedMathieuSubgroup.pCoreIn 2 : Set Model) =
      certifiedMathieuSubgroup.pCoreIn 2 := by
  rw [literalCore_eq_embedded_localKernel]
  exact LocalStructure.centralizer_embedded_localKernel

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry
