module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Density.Fourteen
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Density.Six

/-!
# Transport of density to the remaining diagonal factors

For each nontrivial factor an explicit matrix X and its inverse Y are checked,
along with B_j X = X A_j for the appropriate representative A. Conjugation
therefore transports the full matrix algebra. One-dimensional factors have
full scalar algebra automatically. All identities use the literal published
factor matrices; quotient identification remains a separate obligation.
Source context: Aschbacher–Smith G.7.2(3), printed pp.347–348.
-/

@[expose] public section
namespace G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.Density
open Thompson.BinaryMatrix

local instance : NeZero (length 0) := ⟨by decide⟩
local instance : NeZero (length 1) := ⟨by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_0_3_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 0 3)) (Fin (degree 0 3)) (ZMod 2)))
    (h : ∀ j, factorMatrix 0 3 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[18, 9, 41, 46, 55, 8]
  let y : Array ℕ := #[34, 27, 53, 32, 26, 6]
  let a : Fin 2 → Array ℕ := ![#[10, 33, 50, 54, 62, 15], #[3, 29, 47, 19, 23, 36]]
  let b : Fin 2 → Array ℕ := ![#[54, 9, 37, 61, 38, 50], #[59, 26, 41, 23, 27, 35]]
  have ha : ∀ j, decode 6 (a j) = factorMatrix 0 1 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 1 s)) (blockIndex 0 1 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 6 (b j) = factorMatrix 0 3 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 3 s)) (blockIndex 0 3 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 6) (factorMatrix 0 1) (factorMatrix 0 3)
      (decode 6 x) (decode 6 y) ?_ ?_ ?_
      Six.algebra_eq_top Q h
  · exact decode_mul_one 6 x y (by decide +kernel)
  · exact decode_mul_one 6 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_0_4_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 0 4)) (Fin (degree 0 4)) (ZMod 2)))
    (h : ∀ j, factorMatrix 0 4 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[3949, 6048, 3557, 5659, 9903, 15727, 9919, 15939, 858, 1063, 507, 649, 1338, 335]
  let y : Array ℕ := #[2053, 13914, 15158, 1430, 80, 2198, 1034, 6128, 9461, 4707, 4095, 849, 9741, 533]
  let a : Fin 2 → Array ℕ := ![#[15383, 8781, 7695, 21, 8720, 6763, 1024, 8448, 1344, 2927, 15, 4, 847, 14845], #[15549, 4247, 7920, 4226, 8450, 16, 32, 2667, 14355, 1788, 463, 15511, 6396, 15379]]
  let b : Fin 2 → Array ℕ := ![#[1067, 690, 10252, 10027, 13822, 784, 9688, 7810, 6343, 14332, 10854, 424, 11785, 9461], #[369, 12353, 6321, 11724, 11972, 7116, 15998, 7809, 2569, 8637, 5403, 6373, 3391, 106]]
  have ha : ∀ j, decode 14 (a j) = factorMatrix 0 0 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 0 s)) (blockIndex 0 0 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 14 (b j) = factorMatrix 0 4 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 4 s)) (blockIndex 0 4 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 14) (factorMatrix 0 0) (factorMatrix 0 4)
      (decode 14 x) (decode 14 y) ?_ ?_ ?_
      Fourteen.algebra_eq_top Q h
  · exact decode_mul_one 14 x y (by decide +kernel)
  · exact decode_mul_one 14 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_0_6_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 0 6)) (Fin (degree 0 6)) (ZMod 2)))
    (h : ∀ j, factorMatrix 0 6 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[43, 40, 27, 25, 46, 21]
  let y : Array ℕ := #[15, 12, 30, 54, 49, 52]
  let a : Fin 2 → Array ℕ := ![#[10, 33, 50, 54, 62, 15], #[3, 29, 47, 19, 23, 36]]
  let b : Fin 2 → Array ℕ := ![#[61, 60, 55, 12, 14, 18], #[13, 24, 11, 29, 17, 48]]
  have ha : ∀ j, decode 6 (a j) = factorMatrix 0 1 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 1 s)) (blockIndex 0 1 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 6 (b j) = factorMatrix 0 6 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 6 s)) (blockIndex 0 6 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 6) (factorMatrix 0 1) (factorMatrix 0 6)
      (decode 6 x) (decode 6 y) ?_ ?_ ?_
      Six.algebra_eq_top Q h
  · exact decode_mul_one 6 x y (by decide +kernel)
  · exact decode_mul_one 6 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_0_7_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 0 7)) (Fin (degree 0 7)) (ZMod 2)))
    (h : ∀ j, factorMatrix 0 7 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[3669, 16382, 15907, 2242, 12851, 13238, 1483, 11754, 12002, 11063, 11719, 1935, 54, 1974]
  let y : Array ℕ := #[2133, 12714, 8085, 7786, 13077, 3370, 11593, 12934, 9590, 15004, 7532, 11885, 5790, 11218]
  let a : Fin 2 → Array ℕ := ![#[15383, 8781, 7695, 21, 8720, 6763, 1024, 8448, 1344, 2927, 15, 4, 847, 14845], #[15549, 4247, 7920, 4226, 8450, 16, 32, 2667, 14355, 1788, 463, 15511, 6396, 15379]]
  let b : Fin 2 → Array ℕ := ![#[3447, 3581, 12761, 14832, 13335, 5073, 13521, 11234, 13184, 4977, 13983, 10074, 13676, 16255], #[11131, 8562, 14725, 1790, 11654, 4839, 10964, 16268, 13322, 15350, 11398, 7922, 911, 3077]]
  have ha : ∀ j, decode 14 (a j) = factorMatrix 0 0 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 0 s)) (blockIndex 0 0 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 14 (b j) = factorMatrix 0 7 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 7 s)) (blockIndex 0 7 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 14) (factorMatrix 0 0) (factorMatrix 0 7)
      (decode 14 x) (decode 14 y) ?_ ?_ ?_
      Fourteen.algebra_eq_top Q h
  · exact decode_mul_one 14 x y (by decide +kernel)
  · exact decode_mul_one 14 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_1_0_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 1 0)) (Fin (degree 1 0)) (ZMod 2)))
    (h : ∀ j, factorMatrix 1 0 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[1, 20, 57, 46, 31, 32]
  let y : Array ℕ := #[1, 15, 59, 28, 57, 32]
  let a : Fin 2 → Array ℕ := ![#[10, 33, 50, 54, 62, 15], #[3, 29, 47, 19, 23, 36]]
  let b : Fin 2 → Array ℕ := ![#[19, 39, 38, 51, 56, 41], #[14, 5, 46, 58, 35, 27]]
  have ha : ∀ j, decode 6 (a j) = factorMatrix 0 1 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 1 s)) (blockIndex 0 1 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 6 (b j) = factorMatrix 1 0 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 1 j (blockIndex 1 0 s)) (blockIndex 1 0 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 6) (factorMatrix 0 1) (factorMatrix 1 0)
      (decode 6 x) (decode 6 y) ?_ ?_ ?_
      Six.algebra_eq_top Q h
  · exact decode_mul_one 6 x y (by decide +kernel)
  · exact decode_mul_one 6 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_1_1_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 1 1)) (Fin (degree 1 1)) (ZMod 2)))
    (h : ∀ j, factorMatrix 1 1 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[2593, 14540, 9092, 12118, 4037, 12710, 13190, 1509, 4442, 7604, 15661, 8192, 4771, 9094]
  let y : Array ℕ := #[145, 8196, 1154, 9756, 14392, 6570, 6809, 4277, 1529, 6602, 4844, 240, 8256, 2048]
  let a : Fin 2 → Array ℕ := ![#[15383, 8781, 7695, 21, 8720, 6763, 1024, 8448, 1344, 2927, 15, 4, 847, 14845], #[15549, 4247, 7920, 4226, 8450, 16, 32, 2667, 14355, 1788, 463, 15511, 6396, 15379]]
  let b : Fin 2 → Array ℕ := ![#[970, 11896, 4331, 2521, 1541, 7213, 15638, 9148, 10052, 16114, 9305, 9464, 10060, 14775], #[9612, 10324, 3138, 13143, 9589, 13110, 2312, 10637, 4593, 11256, 497, 8945, 2688, 8344]]
  have ha : ∀ j, decode 14 (a j) = factorMatrix 0 0 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 0 s)) (blockIndex 0 0 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 14 (b j) = factorMatrix 1 1 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 1 j (blockIndex 1 1 s)) (blockIndex 1 1 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 14) (factorMatrix 0 0) (factorMatrix 1 1)
      (decode 14 x) (decode 14 y) ?_ ?_ ?_
      Fourteen.algebra_eq_top Q h
  · exact decode_mul_one 14 x y (by decide +kernel)
  · exact decode_mul_one 14 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_1_3_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 1 3)) (Fin (degree 1 3)) (ZMod 2)))
    (h : ∀ j, factorMatrix 1 3 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[4, 13, 15, 53, 47, 16]
  let y : Array ℕ := #[61, 6, 1, 62, 32, 20]
  let a : Fin 2 → Array ℕ := ![#[10, 33, 50, 54, 62, 15], #[3, 29, 47, 19, 23, 36]]
  let b : Fin 2 → Array ℕ := ![#[50, 57, 16, 3, 20, 13], #[16, 48, 18, 36, 7, 26]]
  have ha : ∀ j, decode 6 (a j) = factorMatrix 0 1 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 1 s)) (blockIndex 0 1 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 6 (b j) = factorMatrix 1 3 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 1 j (blockIndex 1 3 s)) (blockIndex 1 3 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 6) (factorMatrix 0 1) (factorMatrix 1 3)
      (decode 6 x) (decode 6 y) ?_ ?_ ?_
      Six.algebra_eq_top Q h
  · exact decode_mul_one 6 x y (by decide +kernel)
  · exact decode_mul_one 6 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_1_5_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 1 5)) (Fin (degree 1 5)) (ZMod 2)))
    (h : ∀ j, factorMatrix 1 5 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[13, 1, 58, 25, 22, 18]
  let y : Array ℕ := #[2, 25, 48, 51, 57, 23]
  let a : Fin 2 → Array ℕ := ![#[10, 33, 50, 54, 62, 15], #[3, 29, 47, 19, 23, 36]]
  let b : Fin 2 → Array ℕ := ![#[26, 42, 62, 25, 22, 33], #[54, 27, 47, 43, 37, 42]]
  have ha : ∀ j, decode 6 (a j) = factorMatrix 0 1 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 1 s)) (blockIndex 0 1 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 6 (b j) = factorMatrix 1 5 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 1 j (blockIndex 1 5 s)) (blockIndex 1 5 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 6) (factorMatrix 0 1) (factorMatrix 1 5)
      (decode 6 x) (decode 6 y) ?_ ?_ ?_
      Six.algebra_eq_top Q h
  · exact decode_mul_one 6 x y (by decide +kernel)
  · exact decode_mul_one 6 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_1_6_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 1 6)) (Fin (degree 1 6)) (ZMod 2)))
    (h : ∀ j, factorMatrix 1 6 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[12715, 11891, 3565, 5897, 13072, 1972, 4398, 10296, 10894, 4715, 12021, 12182, 6652, 7390]
  let y : Array ℕ := #[755, 4792, 14511, 15309, 8661, 12704, 12808, 11797, 8163, 5623, 3323, 16176, 16345, 5128]
  let a : Fin 2 → Array ℕ := ![#[15383, 8781, 7695, 21, 8720, 6763, 1024, 8448, 1344, 2927, 15, 4, 847, 14845], #[15549, 4247, 7920, 4226, 8450, 16, 32, 2667, 14355, 1788, 463, 15511, 6396, 15379]]
  let b : Fin 2 → Array ℕ := ![#[705, 14964, 12504, 13835, 2385, 2977, 5174, 14535, 13113, 1951, 2357, 15011, 14789, 1194], #[7238, 9819, 10520, 2258, 3149, 3148, 1357, 11592, 3153, 13810, 10690, 9182, 2196, 1044]]
  have ha : ∀ j, decode 14 (a j) = factorMatrix 0 0 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 0 s)) (blockIndex 0 0 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 14 (b j) = factorMatrix 1 6 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 1 j (blockIndex 1 6 s)) (blockIndex 1 6 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 14) (factorMatrix 0 0) (factorMatrix 1 6)
      (decode 14 x) (decode 14 y) ?_ ?_ ?_
      Fourteen.algebra_eq_top Q h
  · exact decode_mul_one 14 x y (by decide +kernel)
  · exact decode_mul_one 14 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_1_8_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 1 8)) (Fin (degree 1 8)) (ZMod 2)))
    (h : ∀ j, factorMatrix 1 8 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[46, 4, 6, 63, 16, 37]
  let y : Array ℕ := #[25, 6, 2, 62, 16, 59]
  let a : Fin 2 → Array ℕ := ![#[10, 33, 50, 54, 62, 15], #[3, 29, 47, 19, 23, 36]]
  let b : Fin 2 → Array ℕ := ![#[3, 45, 15, 42, 17, 54], #[27, 24, 45, 9, 13, 62]]
  have ha : ∀ j, decode 6 (a j) = factorMatrix 0 1 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 1 s)) (blockIndex 0 1 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 6 (b j) = factorMatrix 1 8 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 1 j (blockIndex 1 8 s)) (blockIndex 1 8 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 6) (factorMatrix 0 1) (factorMatrix 1 8)
      (decode 6 x) (decode 6 y) ?_ ?_ ?_
      Six.algebra_eq_top Q h
  · exact decode_mul_one 6 x y (by decide +kernel)
  · exact decode_mul_one 6 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_1_10_algebra_eq_top
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree 1 10)) (Fin (degree 1 10)) (ZMod 2)))
    (h : ∀ j, factorMatrix 1 10 j ∈ Q) : Q = ⊤ := by
  let x : Array ℕ := #[19, 14, 49, 46, 56, 21]
  let y : Array ℕ := #[55, 15, 46, 35, 57, 10]
  let a : Fin 2 → Array ℕ := ![#[10, 33, 50, 54, 62, 15], #[3, 29, 47, 19, 23, 36]]
  let b : Fin 2 → Array ℕ := ![#[32, 19, 40, 38, 22, 33], #[20, 61, 51, 25, 10, 40]]
  have ha : ∀ j, decode 6 (a j) = factorMatrix 0 1 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (a j)[r.val]! s.val =
      bit (actionColumns 0 j (blockIndex 0 1 s)) (blockIndex 0 1 r).val
    revert j r s
    decide +kernel
  have hb : ∀ j, decode 6 (b j) = factorMatrix 1 10 j := by
    intro j
    apply Matrix.ext
    intro r s
    change Thompson.BinaryMatrix.bit (b j)[r.val]! s.val =
      bit (actionColumns 1 j (blockIndex 1 10 s)) (blockIndex 1 10 r).val
    revert j r s
    decide +kernel
  apply density_of_intertwiner (n := 6) (factorMatrix 0 1) (factorMatrix 1 10)
      (decode 6 x) (decode 6 y) ?_ ?_ ?_
      Six.algebra_eq_top Q h
  · exact decode_mul_one 6 x y (by decide +kernel)
  · exact decode_mul_one 6 y x (by decide +kernel)
  · intro j
    rw [← ha, ← hb]
    apply decode_mul_eq
    revert j
    decide +kernel

end G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.Density
