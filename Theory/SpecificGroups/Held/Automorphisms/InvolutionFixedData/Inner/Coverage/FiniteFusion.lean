module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.Forest
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.FiniteFusion.Edges
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.FiniteFusion.Roots

/-!
# Finite conjugacy fusion of Held binary involutions

The 25 root conjugations and 166 forest edges are kernel-certified in the
actual degree-2058 Held carrier. Forest induction, followed by the existing
exhaustive index selection, covers every binary word of order two by the two
literal representatives `a` and `max5First ^ 4`.

This is finite word coverage. Ambient Sylow placement and surjectivity of the
binary words remain separate inputs to the ambient coverage theorem.
Source: GLS3 Table 5.3p and its interpretation on pp.260–261.
-/

namespace Held.InvolutionFixedData.Coverage
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

/-- Every involution among the 1024 binary words belongs to one of the two
specified Held conjugacy classes, with no additional premise. -/
public theorem normalForm_isCovered (n : Fin 1024)
    (hn : orderOf (normalForm n).val = 2) : IsCovered (normalForm n).val :=
  normalForm_fusion_of_forest_identities root_conjugation_identity forest_edge_identity n hn

end Held.InvolutionFixedData.Coverage
