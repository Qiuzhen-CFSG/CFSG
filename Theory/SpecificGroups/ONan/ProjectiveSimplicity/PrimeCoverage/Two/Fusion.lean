module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.FusionReduction
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.Certificate
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.Tree

/-!
# Assembly of the O'Nan involution fusion matrix certificate

The 512 specified words are indexed by their binary digits. Off-diagonal
square witnesses restrict involutions to 87 candidates. Eighty conjugating
products connect these candidates to seven roots, where odd-product powers
construct conjugators to the standard involution. The argument needs neither
closure nor distinctness of the normal forms, nor an ambient group order.

All finite numerical claims remain explicit premises until their matrix
certificates are supplied. `Fusion/Certificate.lean` states the exact
obligations, and `Two/source/` preserves their reproducible discovery data and
ATLAS attribution. This module retains assembly of the unconditional theorem.
-/

namespace ONan.Simplicity.TwoCertificate

/-- Assemble word evaluations, scalar-square exclusions and the fusion trees. -/
public theorem normalForms_involution_fusion_of_matrix_certificates
    (hv : Fusion.MatrixWordValues) (hs : Fusion.MatrixSquareExclusions)
    (ht : Fusion.MatrixTreeProducts) (hr : Fusion.MatrixRootPowers) :
    ∀ v : Fin 9 → Bool, orderOf (normalForm v) = 2 →
      ∃ g : Model, generatorA = g * normalForm v * g⁻¹ :=
  Fusion.normalForms_involution_fusion_of_tree
    (Fusion.candidates_of_matrix_certificates hv hs)
    (Fusion.tree_products_of_matrix_certificates hv ht)
    (Fusion.root_powers_of_matrix_certificates hv hr)

end ONan.Simplicity.TwoCertificate
