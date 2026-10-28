module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison.Assembly
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison.BinaryCoordinates
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks.CorrectionLifts
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison.SavedComparison.Tables

/-!
# Certified similarity of native and saved Hermitian generators

The native blocks are the executable Hermitian action of the 44 certified
SL(3,4) corrections. Twelve distinct local words suffice. A packed column
certificate identifies their sparse induced matrices, with block support proved
structurally. Packed XOR certificates, decoded using the existing `MatrixChecks`
lemmas, establish both inverse identities and intertwining with saved orientation
zero. Rectangular reindexing preserves the literal native point/fiber convention.

The discovered change is a permutation of 22 blocks followed by one common
nine-dimensional coordinate change. The adjacent `SavedComparison/source`
files reproduce the witnesses; every equality used here is kernel-checked.
This discharges the numerical premises of
`generator_coordinates_of_block_certificates`. The marking and action assembly
is retained by the `NativeComparison` consumer.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, printed pp.451--452,457.
-/

open Representation.MathieuSmall.M22Recognition.DegreeThirty
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison

/-- Executable Hermitian blocks of the certified native SL corrections. -/
@[expose] public def nativeBlocks (j : Fin 2) (p : Fin 22) :
    Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  HermitianCoordinates.binaryMatrix (SixteenSubmodule.LocalBlocks.correctionMatrix j p)

namespace SavedComparison
open MatrixChecks

/-- Native point followed by fiber coordinate, with fiber coordinate varying fastest. -/
@[expose] public def index : BinaryIndex ≃ Fin 198 := finProdFinEquiv

/-- The saved GAP orientation identified by the numerical certificates. -/
@[expose] public def orientation : Fin 2 := 0

/-- An executable change from native Hermitian block coordinates to saved coordinates. -/
@[expose] public def C : Matrix (Fin 198) BinaryIndex (ZMod 2) :=
  fun x y => bit (forwardColumns[(index y).val]?.getD 0) x.val

/-- Its executable inverse. -/
@[expose] public def D : Matrix BinaryIndex (Fin 198) (ZMod 2) :=
  fun x y => bit (backwardColumns[y.val]?.getD 0) (index x).val

private def packedMatrix (l : List ℕ) : Matrix (Fin 198) (Fin 198) (ZMod 2) :=
  fun x y => bit (l[y.val]?.getD 0) x.val

private theorem word_certificate : ∀ (j : Fin 2) (p : Fin 22),
    SixteenSubmodule.LocalBlocks.CorrectionCertificates.correctionWord j p =
      words (wordIndex j p) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block_certificate : ∀ (t : Fin 12) (a b : Fin 9),
    HermitianCoordinates.binaryMatrix
      (SixteenSubmodule.LocalBlocks.CorrectionCertificates.wordMatrix (words t)) a b =
        bit (blockColumns t b) a.val := by
  unfold HermitianCoordinates.binaryMatrix
  decide +kernel

private theorem nativeBlocks_entry (j : Fin 2) (p : Fin 22) (a b : Fin 9) :
    nativeBlocks j p a b = bit (blockColumns (wordIndex j p) b) a.val := by
  unfold nativeBlocks SixteenSubmodule.LocalBlocks.correctionMatrix
  rw [word_certificate]
  exact block_certificate _ _ _

private theorem point_certificate : ∀ (j : Fin 2) (p : Fin 22),
    SixteenSubmodule.GeneratorMatrices.generatorPoint j p = sourcePoint j p := by
  decide +kernel

private def targetPoint : Fin 2 → Fin 22 → Fin 22 := ![
  ![6, 13, 8, 16, 12, 5, 0, 17, 2, 10, 9, 14, 4, 1, 11, 15, 3, 7, 18, 19, 20, 21],
  ![3, 0, 18, 21, 13, 12, 11, 15, 14, 9, 8, 7, 5, 2, 20, 6, 16, 19, 4, 17, 10, 1]]

private theorem point_inverse : ∀ (j : Fin 2) (p q : Fin 22),
    p = targetPoint j q ↔ q = sourcePoint j p := by decide +kernel

private theorem block_bound : ∀ (t : Fin 12) (b : Fin 9), blockColumns t b < 2^9 := by
  decide +kernel

/-- A packed nine-bit column occupies only its specified point block. -/
private theorem bit_shift_block (c : ℕ) (hc : c < 2^9) (p q : Fin 22) (a : Fin 9) :
    bit (c <<< (9*q.val)) (a.val + 9*p.val) = if p = q then bit c a.val else 0 := by
  unfold bit
  rw [Nat.testBit_shiftLeft]
  by_cases hp : p = q
  · subst p
    simp
  · have hne : p.val ≠ q.val := fun h => hp (Fin.ext h)
    by_cases hl : p.val < q.val
    · have hlt : ¬ 9*q.val ≤ a.val + 9*p.val := by omega
      simp [hp, hlt]
    · have hbound : 9 ≤ a.val + 9*p.val - 9*q.val := by omega
      have hc' : c < 2^(a.val + 9*p.val - 9*q.val) :=
        hc.trans_le (Nat.pow_le_pow_right (by decide) hbound)
      simp [hp, Nat.testBit_lt_two_pow hc']

set_option maxRecDepth 8192 in
private theorem column_certificate : ∀ (j : Fin 2) (q : BinaryIndex),
    (nativeColumns j)[(index q).val]?.getD 0 =
      blockColumns (wordIndex j (targetPoint j q.1)) q.2 <<< (9*(targetPoint j q.1).val) := by
  decide +kernel

private theorem sparse_eq (j : Fin 2) :
    sparseMatrix j (nativeBlocks j) = (packedMatrix (nativeColumns j)).submatrix index index := by
  ext p q
  change (if q.1 = SixteenSubmodule.GeneratorMatrices.generatorPoint j p.1 then
      nativeBlocks j p.1 p.2 q.2 else 0) =
    bit ((nativeColumns j)[(index q).val]?.getD 0) (index p).val
  rw [column_certificate]
  change _ = bit (blockColumns (wordIndex j (targetPoint j q.1)) q.2 <<<
    (9*(targetPoint j q.1).val)) (p.2.val + 9*p.1.val)
  rw [bit_shift_block _ (block_bound _ _), point_certificate]
  by_cases h : p.1 = targetPoint j q.1
  · rw [if_pos h, if_pos ((point_inverse j p.1 q.1).mp h), nativeBlocks_entry, h]
  · rw [if_neg h, if_neg (fun hq => h ((point_inverse j p.1 q.1).mpr hq))]

private theorem forward_length : forwardColumns.length = 198 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_inverse : ∀ y : Fin 198,
    combineList forwardColumns (backwardColumns[y.val]?.getD 0) = 2 ^ y.val := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_action : ∀ (j : Fin 2) (y : Fin 198),
    combineList forwardColumns ((nativeColumns j)[y.val]?.getD 0) =
      combineList (generatorColumnList orientation j) (forwardColumns[y.val]?.getD 0) := by
  decide +kernel

private theorem forward_backward : packedMatrix forwardColumns * packedMatrix backwardColumns = 1 := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_inverse y)
  rw [bit_combineList _ 198 forward_length, bit_power] at h
  simpa only [packedMatrix, Matrix.mul_apply, Matrix.one_apply, Fin.val_inj, eq_comm] using h

private theorem backward_forward : packedMatrix backwardColumns * packedMatrix forwardColumns = 1 :=
  (mul_eq_one_comm (a := packedMatrix forwardColumns) (b := packedMatrix backwardColumns)).mp
    forward_backward

private theorem flat_action (j : Fin 2) :
    packedMatrix forwardColumns * packedMatrix (nativeColumns j) =
      generatorMatrix orientation j * packedMatrix forwardColumns := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_action j y)
  rw [bit_combineList _ 198 forward_length,
    bit_combineList _ 198 (generatorColumnList_length orientation j)] at h
  exact h

/-- The numerical matrices are inverse on the native binary indexing. -/
public theorem D_mul_C : D * C = 1 := by
  change (packedMatrix backwardColumns).submatrix index (_root_.Equiv.refl _) *
    (packedMatrix forwardColumns).submatrix (_root_.Equiv.refl _) index = 1
  rw [Matrix.submatrix_mul_equiv, backward_forward, Matrix.submatrix_one_equiv]

/-- The numerical matrices are inverse on the saved indexing. -/
public theorem C_mul_D : C * D = 1 := by
  change (packedMatrix forwardColumns).submatrix id index *
    (packedMatrix backwardColumns).submatrix index id = 1
  rw [Matrix.submatrix_mul_equiv, forward_backward, Matrix.submatrix_id_id]

/-- Exact similarity for both literal generators; no marking or invertibility premise remains. -/
public theorem generators (j : Fin 2) :
    C * sparseMatrix j (nativeBlocks j) = generatorMatrix orientation j * C := by
  rw [sparse_eq]
  change (packedMatrix forwardColumns).submatrix id index *
    (packedMatrix (nativeColumns j)).submatrix index index =
      (generatorMatrix orientation j).submatrix id (_root_.Equiv.refl _) *
        (packedMatrix forwardColumns).submatrix (_root_.Equiv.refl _) index
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, flat_action]

end SavedComparison
end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison
