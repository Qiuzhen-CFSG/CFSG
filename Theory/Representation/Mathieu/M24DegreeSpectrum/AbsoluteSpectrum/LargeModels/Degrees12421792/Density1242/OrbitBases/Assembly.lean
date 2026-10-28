module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Realizations

/-!
# Assembly of the degree-1242 orbit bases from arithmetic certificates

A left inverse makes the stored vectors span, and the checked predecessor
recurrences realize each stored vector by a word in the original generators.
For the column tree the two explicit transpose identities identify its packed
row arithmetic with the original column action. No kernel or rank-one completion
hypothesis is involved. All arithmetic premises below remain to be certified;
these are conditional assembly theorems, not unconditional cyclicity assertions.

Source: `../source/README.md`; literal ATLAS M24G1-f2r1242B0 matrices;
application: James, J. Algebra 27 (1973), 57–111.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases

/-- Consumer of both inverse and recurrence certificates and the two transpose comparisons. -/
theorem column_span_of_checks
    (hinverse : ∀ i : Fin 1242,
      packedRow (entry columnInverse i.val) columnVectors 0 = 2 ^ i.val)
    (hsteps : ∀ i : Fin 1242, columnStepCheck i.val = true)
    (hfirst : matrix (n := 1242) firstTranspose = Data1242.first.transpose)
    (hsecond : matrix (n := 1242) secondTranspose = Data1242.second.transpose) :
    Submodule.span (ZMod 2) (Set.range columnOrbit) = ⊤ := by
  have hs := span_rows_of_inverse columnVectors columnInverse columnVectors_length hinverse
  apply top_unique
  rw [← hs]
  exact Submodule.span_mono (column_basis_in_orbit hsteps
    firstTranspose_length secondTranspose_length hfirst hsecond columnVectors_seed)

/-- Consumer of the row inverse and recurrence certificates in the original ATLAS convention. -/
theorem row_span_of_checks
    (hinverse : ∀ i : Fin 1242,
      packedRow (entry rowInverse i.val) rowVectors 0 = 2 ^ i.val)
    (hsteps : ∀ i : Fin 1242, rowStepCheck i.val = true) :
    Submodule.span (ZMod 2) (Set.range rowOrbit) = ⊤ := by
  have hs := span_rows_of_inverse rowVectors rowInverse rowVectors_length hinverse
  apply top_unique
  rw [← hs]
  exact Submodule.span_mono (row_basis_in_orbit hsteps
    firstRows_length secondRows_length rowVectors_seed)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases
