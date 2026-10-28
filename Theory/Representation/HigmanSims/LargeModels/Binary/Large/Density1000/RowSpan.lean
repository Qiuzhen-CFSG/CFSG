module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Orbit
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Inverse
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Packed

/-!
# The degree-1000 Higman–Sims row orbit spans

Every candidate row is the original functional multiplied on the right by its
literal source word. The unchanged proposed inverse is a left inverse of the
matrix of these rows, so they span all 1000 coordinates over `ZMod 2`.
The proof has no polynomial, column-span or carrier-action hypothesis.

This supplies the row-span premise of `Density1000.matrixAlgebraFull_of_certificates`.
Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0, and `Binary/source/density1000.json`.
See `RowSpan/source/README.md` for attribution and kernel-check measurements.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000

/-- The actual source-word orbit of the supplied functional spans all coordinates. -/
theorem rowOrbit_span_eq_top :
    Submodule.span (ZMod 2) (Set.range rowOrbit) = ⊤ := by
  rw [show rowOrbit = (fun i : Fin 1000 => RowArithmetic.vector 1000 Data.rowRows[i.val]!)
    from funext RowSpan.rowOrbit_eq]
  exact Small.Packed.span_rows_of_inverse Data.rowRows Data.rowInverseRows RowSpan.row_inverse

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000
