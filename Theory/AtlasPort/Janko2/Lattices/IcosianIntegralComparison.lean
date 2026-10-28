/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianIntegralComparison.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonLattice
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechFullIsometries
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechRank

/-!
# Icosian Integral Comparison

The rational comparison restricts to an integral linear equivalence
with the Golay Leech lattice. Its explicit agreement with the rational
map proves isometry and transports freeness, finite generation, and rank 24.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianIntegralComparison.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

abbrev IcosianLattice := icosianLeechModule

theorem icosianCoordinateEmbedding_injective : Function.Injective icosianCoordinateEmbedding := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

def icosianIntegralEmbeddingEquiv : IcosianLattice ≃ₗ[ℤ] rationalIcosianLattice :=
  Submodule.equivMapOfInjective icosianCoordinateEmbedding
    icosianCoordinateEmbedding_injective (icosianLeechModule.restrictScalars ℤ)

def icosianRationalLatticeEquiv : rationalIcosianLattice ≃ₗ[ℤ] rationalLeech where
  toFun z := ⟨icosianComparison z.val, icosianComparison_forward z.val z.property⟩
  invFun x := ⟨icosianComparison.symm x.val, icosianComparison_reverse x.val x.property⟩
  left_inv z := Subtype.ext (icosianComparison.symm_apply_apply z.val)
  right_inv x := Subtype.ext (icosianComparison.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add icosianComparison x.val y.val)
  map_smul' r z := Subtype.ext (map_zsmul icosianComparison r z.val)

/-- The integral linear equivalence onto the retained Golay Leech lattice. -/
def icosianLeechEquiv : IcosianLattice ≃ₗ[ℤ] leech :=
  icosianIntegralEmbeddingEquiv.trans (icosianRationalLatticeEquiv.trans latticeEmbeddingEquiv.symm)

theorem icosianLeechEquiv_agrees (z : IcosianLattice) :
    rationalEmbedding (icosianLeechEquiv z).val =
      icosianComparison (icosianCoordinateEmbedding z.val) := by
  have h := latticeEmbeddingEquiv.apply_symm_apply (icosianRationalLatticeEquiv
    (icosianIntegralEmbeddingEquiv z))
  exact congrArg Subtype.val h

theorem icosianLeechEquiv_isometry (x y : IcosianLattice) :
    rationalForm (rationalEmbedding (icosianLeechEquiv x).val)
      (rationalEmbedding (icosianLeechEquiv y).val) =
    icosianBilinear (icosianCoordinateEmbedding x.val) (icosianCoordinateEmbedding y.val) := by
  rw [icosianLeechEquiv_agrees,icosianLeechEquiv_agrees,icosianComparison_isometry]

instance icosianLeech_free : Module.Free ℤ IcosianLattice :=
  Module.Free.of_equiv icosianLeechEquiv.symm

instance icosianLeech_finite : Module.Finite ℤ IcosianLattice :=
  Module.Finite.equiv icosianLeechEquiv.symm

theorem icosianLeech_rank : Module.finrank ℤ IcosianLattice = 24 := by
  rw [icosianLeechEquiv.finrank_eq]
  exact leech_rank

end Atlas.Lattices
