module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.CertificateData
public import Theory.LinearAlgebra.PackedBinaryRows
/-!
# Checked adapted basis and triangular action

Recursive XOR decodes to binary matrix multiplication. Eight-column kernel
batches check both the inverse and the full generator intertwining identities,
including all extension blocks. Bounds on the resulting columns prove the
upper block triangular shape for the eight proposed factors.

The saved generator matrices still require the separate comparison with the
native sparse block rule. These theorems certify the saved finite linear
algebra; they make no simplicity assertion. See `CertificateData/source`.
Source application: Guralnick--Malle I, Proposition 5.1, pp.15--16.
-/

-- The representative batch uses 2.37 GB RSS; serialize closed reductions.
set_option Elab.async false

@[expose] public section
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.MatrixChecks
open InducedFiltration

theorem bit_xor (a b r : ℕ) : bit (a ^^^ b) r = bit a r + bit b r := by
  simp only [bit, Nat.testBit_xor]
  cases a.testBit r <;> cases b.testBit r <;> decide

theorem bit_listProduct (n : ℕ) (c : Fin n → ℕ) (v start r : ℕ) :
    bit (PackedBinaryRows.listProduct v start (List.ofFn c)) r =
      ∑ j, bit (c j) r * bit v (start + j.val) := by
  induction n generalizing start with
  | zero => simp [List.ofFn_zero, PackedBinaryRows.listProduct, bit]
  | succ n ih =>
    rw [List.ofFn_succ, PackedBinaryRows.listProduct, bit_xor, ih, Fin.sum_univ_succ]
    congr 1
    · cases h : v.testBit start <;> simp [bit, h]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

theorem bit_product (cs : List ℕ) (n : ℕ) (hc : cs.length = n) (v r : ℕ) :
    bit (PackedBinaryRows.listProduct v 0 cs) r =
      ∑ j : Fin n, bit cs[j.val]! r * bit v j.val := by
  have h : List.ofFn (fun j : Fin n => cs[j.val]!) = cs := by
    subst n
    simp
  rw [← h, bit_listProduct]
  simp

/-- Packed inverse, intertwining, and upper triangularity for one stored column.
The saved native matrices still need comparison with `GeneratorMatrices`. -/
def columnCertificate (j : ℕ) : Prop :=
  PackedBinaryRows.listProduct inverseColumns[j]! 0 basisColumns = 2 ^ j ∧
  (∀ k : Fin 2,
    PackedBinaryRows.listProduct (actionColumns k)[j]! 0 basisColumns =
      PackedBinaryRows.listProduct basisColumns[j]! 0 (generatorColumns k)) ∧
  (∀ (k : Fin 2) (m : Fin 9), j < cut m.val → (actionColumns k)[j]! < 2 ^ cut m.val)

set_option maxRecDepth 8192 in
private theorem batch0 : ∀ k : Fin 8, columnCertificate (0 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch1 : ∀ k : Fin 8, columnCertificate (8 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch2 : ∀ k : Fin 8, columnCertificate (16 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch3 : ∀ k : Fin 8, columnCertificate (24 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch4 : ∀ k : Fin 8, columnCertificate (32 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch5 : ∀ k : Fin 8, columnCertificate (40 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch6 : ∀ k : Fin 8, columnCertificate (48 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch7 : ∀ k : Fin 8, columnCertificate (56 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch8 : ∀ k : Fin 8, columnCertificate (64 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch9 : ∀ k : Fin 8, columnCertificate (72 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch10 : ∀ k : Fin 8, columnCertificate (80 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch11 : ∀ k : Fin 8, columnCertificate (88 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch12 : ∀ k : Fin 8, columnCertificate (96 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch13 : ∀ k : Fin 8, columnCertificate (104 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch14 : ∀ k : Fin 8, columnCertificate (112 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch15 : ∀ k : Fin 8, columnCertificate (120 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch16 : ∀ k : Fin 8, columnCertificate (128 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch17 : ∀ k : Fin 8, columnCertificate (136 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch18 : ∀ k : Fin 8, columnCertificate (144 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch19 : ∀ k : Fin 8, columnCertificate (152 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch20 : ∀ k : Fin 8, columnCertificate (160 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch21 : ∀ k : Fin 8, columnCertificate (168 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch22 : ∀ k : Fin 8, columnCertificate (176 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch23 : ∀ k : Fin 8, columnCertificate (184 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch24 : ∀ k : Fin 8, columnCertificate (192 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch25 : ∀ k : Fin 8, columnCertificate (200 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch26 : ∀ k : Fin 8, columnCertificate (208 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch27 : ∀ k : Fin 8, columnCertificate (216 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch28 : ∀ k : Fin 8, columnCertificate (224 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch29 : ∀ k : Fin 8, columnCertificate (232 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch30 : ∀ k : Fin 8, columnCertificate (240 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch31 : ∀ k : Fin 8, columnCertificate (248 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch32 : ∀ k : Fin 8, columnCertificate (256 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch33 : ∀ k : Fin 8, columnCertificate (264 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch34 : ∀ k : Fin 8, columnCertificate (272 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch35 : ∀ k : Fin 8, columnCertificate (280 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch36 : ∀ k : Fin 8, columnCertificate (288 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch37 : ∀ k : Fin 8, columnCertificate (296 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch38 : ∀ k : Fin 8, columnCertificate (304 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch39 : ∀ k : Fin 8, columnCertificate (312 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch40 : ∀ k : Fin 8, columnCertificate (320 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch41 : ∀ k : Fin 8, columnCertificate (328 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch42 : ∀ k : Fin 8, columnCertificate (336 + k.val) := by
  unfold columnCertificate
  decide +kernel

set_option maxRecDepth 8192 in
private theorem batch43 : ∀ k : Fin 8, columnCertificate (344 + k.val) := by
  unfold columnCertificate
  decide +kernel

theorem all_columns (j : Fin 352) : columnCertificate j.val := by
  have hj := j.isLt
  by_cases h0 : j.val < 8
  · have he : 0 + (j.val - 0) = j.val := by omega
    simpa only [he] using batch0 ⟨j.val - 0, by omega⟩
  by_cases h1 : j.val < 16
  · have he : 8 + (j.val - 8) = j.val := by omega
    simpa only [he] using batch1 ⟨j.val - 8, by omega⟩
  by_cases h2 : j.val < 24
  · have he : 16 + (j.val - 16) = j.val := by omega
    simpa only [he] using batch2 ⟨j.val - 16, by omega⟩
  by_cases h3 : j.val < 32
  · have he : 24 + (j.val - 24) = j.val := by omega
    simpa only [he] using batch3 ⟨j.val - 24, by omega⟩
  by_cases h4 : j.val < 40
  · have he : 32 + (j.val - 32) = j.val := by omega
    simpa only [he] using batch4 ⟨j.val - 32, by omega⟩
  by_cases h5 : j.val < 48
  · have he : 40 + (j.val - 40) = j.val := by omega
    simpa only [he] using batch5 ⟨j.val - 40, by omega⟩
  by_cases h6 : j.val < 56
  · have he : 48 + (j.val - 48) = j.val := by omega
    simpa only [he] using batch6 ⟨j.val - 48, by omega⟩
  by_cases h7 : j.val < 64
  · have he : 56 + (j.val - 56) = j.val := by omega
    simpa only [he] using batch7 ⟨j.val - 56, by omega⟩
  by_cases h8 : j.val < 72
  · have he : 64 + (j.val - 64) = j.val := by omega
    simpa only [he] using batch8 ⟨j.val - 64, by omega⟩
  by_cases h9 : j.val < 80
  · have he : 72 + (j.val - 72) = j.val := by omega
    simpa only [he] using batch9 ⟨j.val - 72, by omega⟩
  by_cases h10 : j.val < 88
  · have he : 80 + (j.val - 80) = j.val := by omega
    simpa only [he] using batch10 ⟨j.val - 80, by omega⟩
  by_cases h11 : j.val < 96
  · have he : 88 + (j.val - 88) = j.val := by omega
    simpa only [he] using batch11 ⟨j.val - 88, by omega⟩
  by_cases h12 : j.val < 104
  · have he : 96 + (j.val - 96) = j.val := by omega
    simpa only [he] using batch12 ⟨j.val - 96, by omega⟩
  by_cases h13 : j.val < 112
  · have he : 104 + (j.val - 104) = j.val := by omega
    simpa only [he] using batch13 ⟨j.val - 104, by omega⟩
  by_cases h14 : j.val < 120
  · have he : 112 + (j.val - 112) = j.val := by omega
    simpa only [he] using batch14 ⟨j.val - 112, by omega⟩
  by_cases h15 : j.val < 128
  · have he : 120 + (j.val - 120) = j.val := by omega
    simpa only [he] using batch15 ⟨j.val - 120, by omega⟩
  by_cases h16 : j.val < 136
  · have he : 128 + (j.val - 128) = j.val := by omega
    simpa only [he] using batch16 ⟨j.val - 128, by omega⟩
  by_cases h17 : j.val < 144
  · have he : 136 + (j.val - 136) = j.val := by omega
    simpa only [he] using batch17 ⟨j.val - 136, by omega⟩
  by_cases h18 : j.val < 152
  · have he : 144 + (j.val - 144) = j.val := by omega
    simpa only [he] using batch18 ⟨j.val - 144, by omega⟩
  by_cases h19 : j.val < 160
  · have he : 152 + (j.val - 152) = j.val := by omega
    simpa only [he] using batch19 ⟨j.val - 152, by omega⟩
  by_cases h20 : j.val < 168
  · have he : 160 + (j.val - 160) = j.val := by omega
    simpa only [he] using batch20 ⟨j.val - 160, by omega⟩
  by_cases h21 : j.val < 176
  · have he : 168 + (j.val - 168) = j.val := by omega
    simpa only [he] using batch21 ⟨j.val - 168, by omega⟩
  by_cases h22 : j.val < 184
  · have he : 176 + (j.val - 176) = j.val := by omega
    simpa only [he] using batch22 ⟨j.val - 176, by omega⟩
  by_cases h23 : j.val < 192
  · have he : 184 + (j.val - 184) = j.val := by omega
    simpa only [he] using batch23 ⟨j.val - 184, by omega⟩
  by_cases h24 : j.val < 200
  · have he : 192 + (j.val - 192) = j.val := by omega
    simpa only [he] using batch24 ⟨j.val - 192, by omega⟩
  by_cases h25 : j.val < 208
  · have he : 200 + (j.val - 200) = j.val := by omega
    simpa only [he] using batch25 ⟨j.val - 200, by omega⟩
  by_cases h26 : j.val < 216
  · have he : 208 + (j.val - 208) = j.val := by omega
    simpa only [he] using batch26 ⟨j.val - 208, by omega⟩
  by_cases h27 : j.val < 224
  · have he : 216 + (j.val - 216) = j.val := by omega
    simpa only [he] using batch27 ⟨j.val - 216, by omega⟩
  by_cases h28 : j.val < 232
  · have he : 224 + (j.val - 224) = j.val := by omega
    simpa only [he] using batch28 ⟨j.val - 224, by omega⟩
  by_cases h29 : j.val < 240
  · have he : 232 + (j.val - 232) = j.val := by omega
    simpa only [he] using batch29 ⟨j.val - 232, by omega⟩
  by_cases h30 : j.val < 248
  · have he : 240 + (j.val - 240) = j.val := by omega
    simpa only [he] using batch30 ⟨j.val - 240, by omega⟩
  by_cases h31 : j.val < 256
  · have he : 248 + (j.val - 248) = j.val := by omega
    simpa only [he] using batch31 ⟨j.val - 248, by omega⟩
  by_cases h32 : j.val < 264
  · have he : 256 + (j.val - 256) = j.val := by omega
    simpa only [he] using batch32 ⟨j.val - 256, by omega⟩
  by_cases h33 : j.val < 272
  · have he : 264 + (j.val - 264) = j.val := by omega
    simpa only [he] using batch33 ⟨j.val - 264, by omega⟩
  by_cases h34 : j.val < 280
  · have he : 272 + (j.val - 272) = j.val := by omega
    simpa only [he] using batch34 ⟨j.val - 272, by omega⟩
  by_cases h35 : j.val < 288
  · have he : 280 + (j.val - 280) = j.val := by omega
    simpa only [he] using batch35 ⟨j.val - 280, by omega⟩
  by_cases h36 : j.val < 296
  · have he : 288 + (j.val - 288) = j.val := by omega
    simpa only [he] using batch36 ⟨j.val - 288, by omega⟩
  by_cases h37 : j.val < 304
  · have he : 296 + (j.val - 296) = j.val := by omega
    simpa only [he] using batch37 ⟨j.val - 296, by omega⟩
  by_cases h38 : j.val < 312
  · have he : 304 + (j.val - 304) = j.val := by omega
    simpa only [he] using batch38 ⟨j.val - 304, by omega⟩
  by_cases h39 : j.val < 320
  · have he : 312 + (j.val - 312) = j.val := by omega
    simpa only [he] using batch39 ⟨j.val - 312, by omega⟩
  by_cases h40 : j.val < 328
  · have he : 320 + (j.val - 320) = j.val := by omega
    simpa only [he] using batch40 ⟨j.val - 320, by omega⟩
  by_cases h41 : j.val < 336
  · have he : 328 + (j.val - 328) = j.val := by omega
    simpa only [he] using batch41 ⟨j.val - 328, by omega⟩
  by_cases h42 : j.val < 344
  · have he : 336 + (j.val - 336) = j.val := by omega
    simpa only [he] using batch42 ⟨j.val - 336, by omega⟩
  have he : 344 + (j.val - 344) = j.val := by omega
  simpa only [he] using batch43 ⟨j.val - 344, by omega⟩


end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.MatrixChecks
