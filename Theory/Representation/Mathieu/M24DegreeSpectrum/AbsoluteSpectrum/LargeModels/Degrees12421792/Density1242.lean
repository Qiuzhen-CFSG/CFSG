module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.CoordinateDensity
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1242
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.Seed
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.FiniteProjector
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion

/-!
# Full matrix-algebra generation for the literal binary degree-1242 pair

The fixed algebra element `1 + A + B + BAB` has checked paired left and right
kernels. An inverse certificate for its rank-one completion places the projection
in every algebra containing the two ATLAS matrices. Two spanning orbit
certificates then give all matrix units. No group realization is used.

The final theorem discharges all six premises of the conditional assembly using
`KernelCompletion` and `OrbitBases`. The fixed definitions and external witness
search are in `Density1242/Seed.lean` and its source folder; only the checked
Lean certificates supply proof evidence.
Source application: James, J. Algebra 27 (1973), 57–111, and ATLAS
`M24G1-f2r1242B0.m1/.m2`, in their original row convention.
-/

public section
open Matrix (vecMul vecMulVec)

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792

open Density1242

/-- The concrete assembly from the six kernel, completion and spanning identities. -/
theorem density1242_of_certificates
    (hcol : algebraElement.mulVec column = 0)
    (hrow : vecMul row algebraElement = 0)
    (hpair : dotProduct row column = 1)
    (hunit : IsUnit (algebraElement + vecMulVec column row))
    (hcolumns : Submodule.span (ZMod 2) (Set.range columnOrbit) = ⊤)
    (hrows : Submodule.span (ZMod 2) (Set.range rowOrbit) = ⊤) :
    MatrixDensity.DensePair Data1242.first Data1242.second := by
  intro Q ha hb
  have hP := MatrixDensity.rankOne_mem_of_isUnit_add Q algebraElement column row
    (algebraElement_mem Q ha hb) hcol hrow hpair hunit
  exact G2DerivedPermutationFiltration.CycleMatrixCriterion.algebra_eq_top_of_rank_one
    Q column row (wordValue Data1242.first Data1242.second)
    (wordValue Data1242.first Data1242.second)
    (wordValue_mem Q _ _ ha hb) (wordValue_mem Q _ _ ha hb) hP hcolumns hrows

/-- The two literal ATLAS matrices generate the full degree-1242 binary matrix algebra. -/
theorem density1242 : MatrixDensity.DensePair Data1242.first Data1242.second := by
  exact density1242_of_certificates
    KernelCompletion.kernel_column KernelCompletion.kernel_row KernelCompletion.pairing
    KernelCompletion.completion_isUnit OrbitBases.column_span OrbitBases.row_span

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
