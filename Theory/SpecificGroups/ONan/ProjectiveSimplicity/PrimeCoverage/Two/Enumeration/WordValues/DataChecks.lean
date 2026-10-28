module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.WordValues.Data

/-!
# Decoding the O'Nan intermediate matrices

Kernel checks identify packed rows with the published generators, identity,
and nine target matrices, and verify the columns used by multiplication.
-/

@[expose] public section

namespace ONan.Simplicity.TwoCertificate.Enumeration.WordValues

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_a : (decode aT).transpose = decode a := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((aT j / 7^i.val : ℕ) : ZMod 7) = ((a i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_b : (decode bT).transpose = decode b := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((bT j / 7^i.val : ℕ) : ZMod 7) = ((b i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_c : (decode cT).transpose = decode c := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((cT j / 7^i.val : ℕ) : ZMod 7) = ((c i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_c2 : (decode c2T).transpose = decode c2 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((c2T j / 7^i.val : ℕ) : ZMod 7) = ((c2 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_c4 : (decode c4T).transpose = decode c4 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((c4T j / 7^i.val : ℕ) : ZMod 7) = ((c4 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_d : (decode dT).transpose = decode d := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((dT j / 7^i.val : ℕ) : ZMod 7) = ((d i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_d2 : (decode d2T).transpose = decode d2 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((d2T j / 7^i.val : ℕ) : ZMod 7) = ((d2 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_d4 : (decode d4T).transpose = decode d4 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((d4T j / 7^i.val : ℕ) : ZMod 7) = ((d4 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_e : (decode eT).transpose = decode e := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((eT j / 7^i.val : ℕ) : ZMod 7) = ((e i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_fe : (decode feT).transpose = decode fe := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((feT j / 7^i.val : ℕ) : ZMod 7) = ((fe i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_h : (decode hT).transpose = decode h := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((hT j / 7^i.val : ℕ) : ZMod 7) = ((h i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_h2 : (decode h2T).transpose = decode h2 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((h2T j / 7^i.val : ℕ) : ZMod 7) = ((h2 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_h4 : (decode h4T).transpose = decode h4 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((h4T j / 7^i.val : ℕ) : ZMod 7) = ((h4 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_u : (decode uT).transpose = decode u := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((uT j / 7^i.val : ℕ) : ZMod 7) = ((u i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_v : (decode vT).transpose = decode v := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((vT j / 7^i.val : ℕ) : ZMod 7) = ((v i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_w0 : (decode w0T).transpose = decode w0 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w0T j / 7^i.val : ℕ) : ZMod 7) = ((w0 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_w1 : (decode w1T).transpose = decode w1 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w1T j / 7^i.val : ℕ) : ZMod 7) = ((w1 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_w2 : (decode w2T).transpose = decode w2 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w2T j / 7^i.val : ℕ) : ZMod 7) = ((w2 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_w3 : (decode w3T).transpose = decode w3 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w3T j / 7^i.val : ℕ) : ZMod 7) = ((w3 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_w4 : (decode w4T).transpose = decode w4 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w4T j / 7^i.val : ℕ) : ZMod 7) = ((w4 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_w5 : (decode w5T).transpose = decode w5 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w5T j / 7^i.val : ℕ) : ZMod 7) = ((w5 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_w6 : (decode w6T).transpose = decode w6 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w6T j / 7^i.val : ℕ) : ZMod 7) = ((w6 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem transpose_w7 : (decode w7T).transpose = decode w7 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w7T j / 7^i.val : ℕ) : ZMod 7) = ((w7 i / 7^j.val : ℕ) : ZMod 7)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_a : decode a = matrixA := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((a i / 7^j.val : ℕ) : ZMod 7) = matrixA i j
  unfold matrixA
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_b : decode b = matrixB := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((b i / 7^j.val : ℕ) : ZMod 7) = matrixB i j
  unfold matrixB
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_one : decode one = 1 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((one i / 7^j.val : ℕ) : ZMod 7) = (if i = j then 1 else 0)
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_w3 : decode w3 = basisMatrix0 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w3 i / 7^j.val : ℕ) : ZMod 7) = basisMatrix0 i j
  unfold basisMatrix0
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_w9 : decode w9 = basisMatrix1 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w9 i / 7^j.val : ℕ) : ZMod 7) = basisMatrix1 i j
  unfold basisMatrix1
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_w11 : decode w11 = basisMatrix2 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w11 i / 7^j.val : ℕ) : ZMod 7) = basisMatrix2 i j
  unfold basisMatrix2
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_w14 : decode w14 = basisMatrix3 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w14 i / 7^j.val : ℕ) : ZMod 7) = basisMatrix3 i j
  unfold basisMatrix3
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_w19 : decode w19 = basisMatrix4 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w19 i / 7^j.val : ℕ) : ZMod 7) = basisMatrix4 i j
  unfold basisMatrix4
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_w21 : decode w21 = basisMatrix5 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w21 i / 7^j.val : ℕ) : ZMod 7) = basisMatrix5 i j
  unfold basisMatrix5
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_w24 : decode w24 = basisMatrix6 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w24 i / 7^j.val : ℕ) : ZMod 7) = basisMatrix6 i j
  unfold basisMatrix6
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_w27 : decode w27 = basisMatrix7 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w27 i / 7^j.val : ℕ) : ZMod 7) = basisMatrix7 i j
  unfold basisMatrix7
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem decode_w28 : decode w28 = basisMatrix8 := by
  apply Matrix.ext
  change ∀ i j : Fin 45, ((w28 i / 7^j.val : ℕ) : ZMod 7) = basisMatrix8 i j
  unfold basisMatrix8
  decide +kernel


end ONan.Simplicity.TwoCertificate.Enumeration.WordValues
