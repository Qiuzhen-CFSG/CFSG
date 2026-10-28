module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFourSpace
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeSection
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Geometry
public import Theory.Mathieu.M22.Properties.OuterHexadRadical
public import Theory.GroupTheory.PCoreImage
/-!
# Compatible arbitrary M22 hexads and the quintet hyperplane

A Golay representative in the quintet code four-space is constant on
each tetrad. A hexad word in that space therefore contains the whole
distinguished tetrad. Its pointwise kernel fixes the associated cocode
pair class, so code--cocode duality puts its commutator in the original
quintet hyperplane. This preserves both geometries on the same code.

Source: Aschbacher--Smith H.16.4(4), printed p.403, and the crossing
argument in 8.2.12, printed p.722, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode.NormalizedShadowRows.M22CodePointCrossing
open MathieuCode.Hexad MathieuCode.Hexad.ChiefFlag
set_option backward.isDefEq.respectTransparency false

/-- The selected intrinsic nine-space is the hyperplane from the same
literal quintet cocode line. -/
theorem quintet_hyperplane_eq : M22Quintet.V9 = quintetHyperplane := by
  apply Submodule.eq_of_le_of_finrank_eq ?_
    (M22CodeSection.nine_dim.trans quintetHyperplane_finrank.symm)
  exact Submodule.comap_mono
    (Subspace.dualAnnihilator_le_dualAnnihilator_iff.mpr quintetLine_le_quintet_fixed)

/-- A marked hexad in the original quintet four-space contains the entire
distinguished tetrad, by the actual coordinate-constancy criterion. -/
theorem tetrad_le_hexad {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hU : m22HexadVector hB ∈ M22Quintet.V4) :
    m22SourceTetrad 0 ⊆ (m22Octad hB).val := by
  have hc := (M22Quintet.V4_mk_iff_constant _ _).mp hU
  intro x hx
  have he := hc _ m22SourceTetrad_mem x hx 0 (by decide +kernel)
  have h0 : (0 : Fin 24) ∈ (m22Octad hB).val :=
    (mem_m22AugmentedOctad B 0).mpr (Or.inl rfl)
  change wordOfSet (m22Octad hB).val x = wordOfSet (m22Octad hB).val 0 at he
  by_contra hn
  simp [wordOfSet,h0,hn] at he

/-- For every hexad in the selected four-space, its literal pointwise
kernel fixes the original quintet cocode line. -/
theorem quintet_line_le_fixed {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hU : m22HexadVector hB ∈ M22Quintet.V4) :
    quintetLine ≤ fixedSpace m22OuterCocodeRepresentation
      ((m22HexadPointwiseKernel B).map m22ToPairStabilizer) := by
  apply Submodule.span_le.mpr
  rw [Set.singleton_subset_iff,quintetVector_eq_pair]
  have hO := tetrad_le_hexad hB hU
  have hK : ((m22HexadPointwiseKernel B).map m22ToPairStabilizer).map
      (m22PairStabilizer.subtype.comp (MonoidHom.id m22PairStabilizer)) =
        octadPointwiseKernel (m22Octad hB) := by
    rw [MonoidHom.comp_id,Subgroup.map_map]
    exact m22HexadPointwiseKernel_map hB
  exact cocodePair_mem_fixedSpace (MonoidHom.id m22PairStabilizer)
    ((m22HexadPointwiseKernel B).map m22ToPairStabilizer) (m22Octad hB)
    2 14 (hO (by decide +kernel)) (hO (by decide +kernel)) hK

/-- The source hexad and quintet compatibility, for the actual arbitrary
hexad vector in the selected four-space. -/
theorem commutator_le_hyperplane {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hU : m22HexadVector hB ∈ M22Quintet.V4) :
    codeCommutator ((m22HexadPointwiseKernel B).map m22ToPairStabilizer) ≤ quintetHyperplane := by
  rw [codeCommutator_eq_annihilator]
  exact Submodule.comap_mono
    ((Subspace.dualAnnihilator_le_dualAnnihilator_iff).mpr (quintet_line_le_fixed hB hU))

/-- The intrinsic core of the actual inner hexad stabilizer is its literal
pointwise kernel, with the original M22 inclusion retained. -/
theorem inner_hexad_core {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (MulAction.stabilizer M22 B).pCoreIn 2 = m22HexadPointwiseKernel B := by
  let j := M22ValueBound.Concrete.inclusion
  have hj := M22ValueBound.Concrete.inclusion_injective
  apply Subgroup.map_injective hj
  rw [map_pCoreIn_of_ker_isPGroup j (IsPGroup.ker_isPGroup_of_injective hj)]
  apply M22OuterHexad.radical_eq hB _ le_rfl
  rintro _ ⟨g,hg,rfl⟩
  exact hg

end MathieuCode.NormalizedShadowRows.M22CodePointCrossing
