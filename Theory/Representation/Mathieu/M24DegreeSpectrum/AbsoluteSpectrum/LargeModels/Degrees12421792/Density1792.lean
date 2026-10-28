module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.CoordinateDensity
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RowOrbit
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.Projector
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne

/-!
# Full matrix-algebra generation by the literal degree-1792 pair

The checked rank-one element `Density1792.rankOne` belongs to every subalgebra
containing the two generators. Its column and row orbits span both coordinate
spaces, so their outer products span all matrices. The theorem `density1792`
assembles these certificates without additional premises. The conditional
criteria remain available separately.

The projector route and reproducible candidate data are documented in
`Density1792/source/README.md`. The matrices retain the original ATLAS row
convention; this module imports no native-action or spectrum assembly.
Source: ATLAS M24G1-f2r1792B0.m1/.m2; mathematical application: James,
J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
open Matrix Density1792

/-- Exact assembly from the independent rank-one and column-orbit certificates.
The zeroth-row spanning premise is discharged by the checked literal data. -/
theorem density1792_of_rankOne_and_columnOrbit
    (hrank : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)),
      Data1792.first ∈ Q → Data1792.second ∈ Q → rankOne ∈ Q)
    (hcolumn : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)),
      Data1792.first ∈ Q → Data1792.second ∈ Q →
      Submodule.span (ZMod 2) (Set.range (fun L : Q => L.val.mulVec nucleus)) = ⊤) :
    Representation.MatrixDensity.DensePair Data1792.first Data1792.second := by
  intro Q hA hB
  exact G2DerivedPermutationFiltration.CycleMatrixCriterion.algebra_eq_top_of_rank_one
    Q nucleus (Pi.single 0 1) (fun L : Q => L.val) (fun R : Q => R.val)
    (fun L => L.property) (fun R => R.property) (hrank Q hA hB)
    (hcolumn Q hA hB) (rowOrbit_eq_top Q hA hB)

/-- Invertible completion is one concrete route to the rank-one premise.
The numerical kernel, unit and column-span certificates remain explicit. -/
theorem density1792_of_completion_unit_and_columnOrbit
    (hkernel : singular.mulVec nucleus = 0)
    (hrow : vecMul (Pi.single 0 1) singular = 0)
    (hunit : IsUnit (singular + rankOne))
    (hcolumn : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)),
      Data1792.first ∈ Q → Data1792.second ∈ Q →
      Submodule.span (ZMod 2) (Set.range (fun L : Q => L.val.mulVec nucleus)) = ⊤) :
    Representation.MatrixDensity.DensePair Data1792.first Data1792.second :=
  density1792_of_rankOne_and_columnOrbit
    (rankOne_mem_of_completion_unit hkernel hrow hunit) hcolumn

/-- The literal, untransposed degree-1792 binary ATLAS pair generates the full
matrix algebra. This supplies the degree-1792 density premise of
`models12421792_of_matrix_certificates`. -/
theorem density1792 :
    Representation.MatrixDensity.DensePair Data1792.first Data1792.second :=
  density1792_of_rankOne_and_columnOrbit rankOne_mem columnOrbit_eq_top

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
