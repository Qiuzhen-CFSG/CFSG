module
public import Theory.Mathieu.M22.ChapterHLocalClassification
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.StabilizerRecovery
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.Centralizer
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Annihilator

/-!
# The quintet code four-space and its five-point action

Dualizing the existing geometric cocode quotient gives the actual deleted
five-point action on the code annihilator. Its pointwise kernel is the
intrinsic quintet two-core. At fixed dimension four, inclusion identifies
this geometric space with the full code fixed space. The Chapter 12 original
M22-code pair supplies that dimension and uses these coordinates.

Source: Aschbacher--Smith H.16.3(2,4) and 8.2.6(2), printed pp.403,717,
refs/quasithin.pdf. The geometric Golay constructions are the existing
licensed ATLAS ports; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Sporadic.Mathieu Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.M22CodeFourSpace
open M22Quintet M22Quintet.CocodeTransfer

@[expose] def naturalMarking : V4 ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
  DualAction.naturalEquiv NaturalQuotient.marking

theorem naturalMarking_equivariant (g : Q) (v : V4) :
    naturalMarking (V4Subrepresentation.toRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (NaturalQuotient.q g) (naturalMarking v) :=
  DualAction.naturalEquiv_equivariant NaturalQuotient.q NaturalQuotient.marking
    NaturalQuotient.marking_equivariant g v

theorem pointwise_kernel : subspaceKernel m22OuterCodeRepresentation V4 ⊤ = K :=
  V4_centralizer_eq_of_natural_quotient NaturalQuotient.q NaturalQuotient.marking
    NaturalQuotient.marking_equivariant V4_stabilizer_eq_native M22ChapterH.quintet_relative_kernel

theorem le_fixed : V4 ≤ fixedSpace m22OuterCodeRepresentation K := by
  intro v hv g
  have hg : g.val ∈ subspaceKernel m22OuterCodeRepresentation V4 ⊤ :=
    pointwise_kernel.symm ▸ g.property
  exact hg.2 v hv

theorem finrank_four : Module.finrank (ZMod 2) V4 = 4 :=
  naturalMarking.finrank_eq.trans (BinaryPermutation.finrank_natural_odd (Fin 5) (by decide))

theorem fixed_eq_of_finrank
    (hd : Module.finrank (ZMod 2) (fixedSpace m22OuterCodeRepresentation K) = 4) :
    fixedSpace m22OuterCodeRepresentation K = V4 :=
  (Submodule.eq_of_le_of_finrank_eq le_fixed (finrank_four.trans hd.symm)).symm

end MathieuCode.NormalizedShadowRows.M22CodeFourSpace
