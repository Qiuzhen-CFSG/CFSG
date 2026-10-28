module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C07
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C08
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C09
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C10
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C11
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C12
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C13
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C14
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C15
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C16
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C17
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C18
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Certificates.SecondTranspose.Checks.C19
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Realizations

/-!
# Exact transpose of the original degree-1242 generator

The interval certificates cover every column and reproduce the entire
fixed candidate table. Their soundness identifies all packed columns
with the original untransposed ATLAS array; `transpose_sound` then
gives the matrix equality consumed by `column_span_of_checks`.

Original ATLAS attribution and unchanged license:
`Degrees12421792/source/README.md`. Application: James,
J. Algebra 27 (1973), 57–111. Generated inputs are untrusted;
all numerical proofs use `decide +kernel`.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.SecondTranspose
open FirstTranspose

-- These symbolic interfaces prevent rewriting from unfolding the certificate data.
private theorem map_append_checked (f : Record → ℕ)
    {xs ys : List Record} {as bs : List ℕ}
    (hx : xs.map f = as) (hy : ys.map f = bs) :
    (xs ++ ys).map f = as ++ bs :=
  List.map_append.trans (congrArg₂ List.append hx hy)

private theorem all_append_checked (t : RowTree) {xs ys : List Record}
    (hx : xs.all (rowCheck t) = true) (hy : ys.all (rowCheck t) = true) :
    (xs ++ ys).all (rowCheck t) = true :=
  List.all_append.trans (congrArg₂ Bool.and hx hy)

private def records : List Record := Checks.C00.records ++ Checks.C01.records ++ Checks.C02.records ++ Checks.C03.records ++ Checks.C04.records ++ Checks.C05.records ++ Checks.C06.records ++ Checks.C07.records ++ Checks.C08.records ++ Checks.C09.records ++ Checks.C10.records ++ Checks.C11.records ++ Checks.C12.records ++ Checks.C13.records ++ Checks.C14.records ++ Checks.C15.records ++ Checks.C16.records ++ Checks.C17.records ++ Checks.C18.records ++ Checks.C19.records

set_option maxRecDepth 8192 in
private theorem covers : records.map Record.column = List.range 1242 := by
  calc
    records.map Record.column = List.range' 0 64 ++ List.range' 64 64 ++ List.range' 128 64 ++ List.range' 192 64 ++ List.range' 256 64 ++ List.range' 320 64 ++ List.range' 384 64 ++ List.range' 448 64 ++ List.range' 512 64 ++ List.range' 576 64 ++ List.range' 640 64 ++ List.range' 704 64 ++ List.range' 768 64 ++ List.range' 832 64 ++ List.range' 896 64 ++ List.range' 960 64 ++ List.range' 1024 64 ++ List.range' 1088 64 ++ List.range' 1152 64 ++ List.range' 1216 26 := by
      exact (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column (map_append_checked Record.column Checks.C00.columns Checks.C01.columns) Checks.C02.columns) Checks.C03.columns) Checks.C04.columns) Checks.C05.columns) Checks.C06.columns) Checks.C07.columns) Checks.C08.columns) Checks.C09.columns) Checks.C10.columns) Checks.C11.columns) Checks.C12.columns) Checks.C13.columns) Checks.C14.columns) Checks.C15.columns) Checks.C16.columns) Checks.C17.columns) Checks.C18.columns) Checks.C19.columns)
    _ = _ := by decide +kernel

set_option maxRecDepth 8192 in
private theorem values : records.map Record.value = secondTranspose := by
  calc
    records.map Record.value = (secondTranspose.drop 0).take 64 ++ (secondTranspose.drop 64).take 64 ++ (secondTranspose.drop 128).take 64 ++ (secondTranspose.drop 192).take 64 ++ (secondTranspose.drop 256).take 64 ++ (secondTranspose.drop 320).take 64 ++ (secondTranspose.drop 384).take 64 ++ (secondTranspose.drop 448).take 64 ++ (secondTranspose.drop 512).take 64 ++ (secondTranspose.drop 576).take 64 ++ (secondTranspose.drop 640).take 64 ++ (secondTranspose.drop 704).take 64 ++ (secondTranspose.drop 768).take 64 ++ (secondTranspose.drop 832).take 64 ++ (secondTranspose.drop 896).take 64 ++ (secondTranspose.drop 960).take 64 ++ (secondTranspose.drop 1024).take 64 ++ (secondTranspose.drop 1088).take 64 ++ (secondTranspose.drop 1152).take 64 ++ (secondTranspose.drop 1216).take 26 := by
      exact (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value (map_append_checked Record.value Checks.C00.values Checks.C01.values) Checks.C02.values) Checks.C03.values) Checks.C04.values) Checks.C05.values) Checks.C06.values) Checks.C07.values) Checks.C08.values) Checks.C09.values) Checks.C10.values) Checks.C11.values) Checks.C12.values) Checks.C13.values) Checks.C14.values) Checks.C15.values) Checks.C16.values) Checks.C17.values) Checks.C18.values) Checks.C19.values)
    _ = _ := by decide +kernel

private theorem checked_records : records.all (rowCheck rowsTree) = true :=
  (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree (all_append_checked rowsTree Checks.C00.checked Checks.C01.checked) Checks.C02.checked) Checks.C03.checked) Checks.C04.checked) Checks.C05.checked) Checks.C06.checked) Checks.C07.checked) Checks.C08.checked) Checks.C09.checked) Checks.C10.checked) Checks.C11.checked) Checks.C12.checked) Checks.C13.checked) Checks.C14.checked) Checks.C15.checked) Checks.C16.checked) Checks.C17.checked) Checks.C18.checked) Checks.C19.checked)

theorem checked (i : Fin 1242) :
    transposeRow Data1242.secondRows.toList i.val = entry secondTranspose i.val := by
  have h := checked_of_records 1242 rowsTree secondTranspose records
    rowsTree_valid covers values checked_records i
  simpa only [rowsTree_eq] using h

/-- Every coordinate agrees with the transpose of the original ATLAS generator. -/
theorem matrix_eq : matrix (n := 1242) secondTranspose = Data1242.second.transpose := by
  have h := transpose_sound Data1242.secondRows.toList secondTranspose secondRows_length checked
  rw [matrix_array] at h
  exact h.symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.SecondTranspose
