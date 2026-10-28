module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.CertificateData
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices

/-!
# Saved columns agree with the native adjoint correction blocks

Kernel reduction checks the sixteen binary columns of each of the 44 actual
correction matrices. A second family of certificates checks each full saved
column as a shifted local column, at the native inverse-permutation source
point. This identifies the literal sparse action without choosing a new marking.

The five-transvection representative took 4.84 s of kernel checking; its
process used about 4 GB including imports. A sixteen-column sparse certificate
took 0.31 s. Closed checks are sequential; Lean's thread count is unchanged.
The witnesses are the existing `CertificateData` and `LocalBlocks` definitions.
See `CertificateData/source/README.md` for their provenance and orientation.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

@[expose] public section
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration
namespace NativeFlag
set_option Elab.async false
private def sourcePoint : Fin 2 → Fin 22 → Fin 22 := ![
  ![6, 13, 8, 16, 12, 5, 0, 17, 2, 10, 9, 14, 4, 1, 11, 15, 3, 7, 18, 19, 20, 21],
  ![1, 21, 13, 0, 18, 12, 15, 11, 10, 9, 20, 6, 5, 4, 8, 7, 16, 19, 2, 17, 14, 3]]
private theorem sourcePoint_eq : ∀ k i, sourcePoint k i = GeneratorMatrices.generatorPoint k i := by
  decide +kernel

private def columnCertificate (k : Fin 2) (i : Fin 22) : Prop :=
  ∀ y : Fin 16,
    (generatorColumns k)[16 * (sourcePoint k i).val + y.val]! =
      localColumns k i y <<< (16 * i.val)

/-- Every saved local column fits in sixteen binary coordinates. -/
theorem local_bound : ∀ (k : Fin 2) (i : Fin 22) (y : Fin 16),
    localColumns k i y < 2^16 := by decide +kernel

private theorem nativeBlock0_0 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 0 x y).val = (bit (localColumns 0 0 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_0 : columnCertificate 0 0 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_1 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 1 x y).val = (bit (localColumns 0 1 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_1 : columnCertificate 0 1 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_2 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 2 x y).val = (bit (localColumns 0 2 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_2 : columnCertificate 0 2 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_3 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 3 x y).val = (bit (localColumns 0 3 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_3 : columnCertificate 0 3 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_4 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 4 x y).val = (bit (localColumns 0 4 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_4 : columnCertificate 0 4 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_5 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 5 x y).val = (bit (localColumns 0 5 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_5 : columnCertificate 0 5 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_6 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 6 x y).val = (bit (localColumns 0 6 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_6 : columnCertificate 0 6 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_7 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 7 x y).val = (bit (localColumns 0 7 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_7 : columnCertificate 0 7 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_8 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 8 x y).val = (bit (localColumns 0 8 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_8 : columnCertificate 0 8 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_9 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 9 x y).val = (bit (localColumns 0 9 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_9 : columnCertificate 0 9 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_10 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 10 x y).val = (bit (localColumns 0 10 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_10 : columnCertificate 0 10 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_11 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 11 x y).val = (bit (localColumns 0 11 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_11 : columnCertificate 0 11 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_12 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 12 x y).val = (bit (localColumns 0 12 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_12 : columnCertificate 0 12 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_13 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 13 x y).val = (bit (localColumns 0 13 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_13 : columnCertificate 0 13 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_14 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 14 x y).val = (bit (localColumns 0 14 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_14 : columnCertificate 0 14 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_15 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 15 x y).val = (bit (localColumns 0 15 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_15 : columnCertificate 0 15 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_16 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 16 x y).val = (bit (localColumns 0 16 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_16 : columnCertificate 0 16 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_17 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 17 x y).val = (bit (localColumns 0 17 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_17 : columnCertificate 0 17 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_18 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 18 x y).val = (bit (localColumns 0 18 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_18 : columnCertificate 0 18 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_19 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 19 x y).val = (bit (localColumns 0 19 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_19 : columnCertificate 0 19 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_20 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 20 x y).val = (bit (localColumns 0 20 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_20 : columnCertificate 0 20 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock0_21 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 0 21 x y).val = (bit (localColumns 0 21 y) x.val).val := by
  decide +kernel

private theorem savedColumn0_21 : columnCertificate 0 21 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_0 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 0 x y).val = (bit (localColumns 1 0 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_0 : columnCertificate 1 0 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_1 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 1 x y).val = (bit (localColumns 1 1 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_1 : columnCertificate 1 1 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_2 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 2 x y).val = (bit (localColumns 1 2 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_2 : columnCertificate 1 2 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_3 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 3 x y).val = (bit (localColumns 1 3 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_3 : columnCertificate 1 3 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_4 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 4 x y).val = (bit (localColumns 1 4 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_4 : columnCertificate 1 4 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_5 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 5 x y).val = (bit (localColumns 1 5 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_5 : columnCertificate 1 5 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_6 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 6 x y).val = (bit (localColumns 1 6 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_6 : columnCertificate 1 6 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_7 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 7 x y).val = (bit (localColumns 1 7 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_7 : columnCertificate 1 7 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_8 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 8 x y).val = (bit (localColumns 1 8 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_8 : columnCertificate 1 8 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_9 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 9 x y).val = (bit (localColumns 1 9 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_9 : columnCertificate 1 9 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_10 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 10 x y).val = (bit (localColumns 1 10 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_10 : columnCertificate 1 10 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_11 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 11 x y).val = (bit (localColumns 1 11 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_11 : columnCertificate 1 11 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_12 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 12 x y).val = (bit (localColumns 1 12 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_12 : columnCertificate 1 12 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_13 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 13 x y).val = (bit (localColumns 1 13 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_13 : columnCertificate 1 13 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_14 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 14 x y).val = (bit (localColumns 1 14 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_14 : columnCertificate 1 14 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_15 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 15 x y).val = (bit (localColumns 1 15 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_15 : columnCertificate 1 15 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_16 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 16 x y).val = (bit (localColumns 1 16 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_16 : columnCertificate 1 16 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_17 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 17 x y).val = (bit (localColumns 1 17 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_17 : columnCertificate 1 17 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_18 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 18 x y).val = (bit (localColumns 1 18 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_18 : columnCertificate 1 18 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_19 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 19 x y).val = (bit (localColumns 1 19 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_19 : columnCertificate 1 19 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_20 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 20 x y).val = (bit (localColumns 1 20 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_20 : columnCertificate 1 20 := by
  unfold columnCertificate
  decide +kernel

private theorem nativeBlock1_21 : ∀ x y : Fin 16,
    (LocalBlocks.blocks 1 21 x y).val = (bit (localColumns 1 21 y) x.val).val := by
  decide +kernel

private theorem savedColumn1_21 : columnCertificate 1 21 := by
  unfold columnCertificate
  decide +kernel

/-- The saved local columns are the actual native correction matrices. -/
theorem local_blocks (k : Fin 2) (i : Fin 22) (x y : Fin 16) :
    LocalBlocks.blocks k i x y = bit (localColumns k i y) x.val := by
  apply ZMod.val_injective 2
  fin_cases k
  · fin_cases i
    · exact nativeBlock0_0 x y
    · exact nativeBlock0_1 x y
    · exact nativeBlock0_2 x y
    · exact nativeBlock0_3 x y
    · exact nativeBlock0_4 x y
    · exact nativeBlock0_5 x y
    · exact nativeBlock0_6 x y
    · exact nativeBlock0_7 x y
    · exact nativeBlock0_8 x y
    · exact nativeBlock0_9 x y
    · exact nativeBlock0_10 x y
    · exact nativeBlock0_11 x y
    · exact nativeBlock0_12 x y
    · exact nativeBlock0_13 x y
    · exact nativeBlock0_14 x y
    · exact nativeBlock0_15 x y
    · exact nativeBlock0_16 x y
    · exact nativeBlock0_17 x y
    · exact nativeBlock0_18 x y
    · exact nativeBlock0_19 x y
    · exact nativeBlock0_20 x y
    · exact nativeBlock0_21 x y
  · fin_cases i
    · exact nativeBlock1_0 x y
    · exact nativeBlock1_1 x y
    · exact nativeBlock1_2 x y
    · exact nativeBlock1_3 x y
    · exact nativeBlock1_4 x y
    · exact nativeBlock1_5 x y
    · exact nativeBlock1_6 x y
    · exact nativeBlock1_7 x y
    · exact nativeBlock1_8 x y
    · exact nativeBlock1_9 x y
    · exact nativeBlock1_10 x y
    · exact nativeBlock1_11 x y
    · exact nativeBlock1_12 x y
    · exact nativeBlock1_13 x y
    · exact nativeBlock1_14 x y
    · exact nativeBlock1_15 x y
    · exact nativeBlock1_16 x y
    · exact nativeBlock1_17 x y
    · exact nativeBlock1_18 x y
    · exact nativeBlock1_19 x y
    · exact nativeBlock1_20 x y
    · exact nativeBlock1_21 x y

private theorem checked_columns (k : Fin 2) (i : Fin 22) : columnCertificate k i := by
  fin_cases k
  · fin_cases i
    · exact savedColumn0_0
    · exact savedColumn0_1
    · exact savedColumn0_2
    · exact savedColumn0_3
    · exact savedColumn0_4
    · exact savedColumn0_5
    · exact savedColumn0_6
    · exact savedColumn0_7
    · exact savedColumn0_8
    · exact savedColumn0_9
    · exact savedColumn0_10
    · exact savedColumn0_11
    · exact savedColumn0_12
    · exact savedColumn0_13
    · exact savedColumn0_14
    · exact savedColumn0_15
    · exact savedColumn0_16
    · exact savedColumn0_17
    · exact savedColumn0_18
    · exact savedColumn0_19
    · exact savedColumn0_20
    · exact savedColumn0_21
  · fin_cases i
    · exact savedColumn1_0
    · exact savedColumn1_1
    · exact savedColumn1_2
    · exact savedColumn1_3
    · exact savedColumn1_4
    · exact savedColumn1_5
    · exact savedColumn1_6
    · exact savedColumn1_7
    · exact savedColumn1_8
    · exact savedColumn1_9
    · exact savedColumn1_10
    · exact savedColumn1_11
    · exact savedColumn1_12
    · exact savedColumn1_13
    · exact savedColumn1_14
    · exact savedColumn1_15
    · exact savedColumn1_16
    · exact savedColumn1_17
    · exact savedColumn1_18
    · exact savedColumn1_19
    · exact savedColumn1_20
    · exact savedColumn1_21
/-- Each full saved column is the native local column in its unique block row.
The column block is indexed by the inverse native generator permutation. -/
theorem saved_columns (k : Fin 2) (i : Fin 22) (y : Fin 16) :
    (generatorColumns k)[16 * (GeneratorMatrices.generatorPoint k i).val + y.val]! =
      localColumns k i y <<< (16 * i.val) := by
  have h := checked_columns k i y
  simpa only [sourcePoint_eq] using h

end NativeFlag
end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration
