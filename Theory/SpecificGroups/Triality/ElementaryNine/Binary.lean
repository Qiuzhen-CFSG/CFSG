module
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.Constants


/-!
# Two independent cubic words on the binary D₄ lattice

The four input matrices are the signed central root and signed three-arm root
products at parameter one. Write these as `c₊`, `c₋`, `a₊`, `a₋`, and put
`n_c = c₊ c₋ c₊`, `n_a = a₊ a₋ a₊`. The words
`x = n_c n_a (c₊ c₋) n_a n_c` and `y = a₊ a₋` commute and have cube one.
Their nine coordinate products are distinct: entries (0,1) and (4,7) detect
whether both exponents vanish. The main module transports this certificate
to actual elementary fixed points and then to the genuine central quotient.

All 28 Cartan-plus-root coordinates are retained. Natural-number row encodings
make the fourteen product checks small; decoding is proved to preserve matrix
multiplication. The four initial rows are checked against the existing pinned
root matrices, so the certificate is tied to the genuine D₄ construction.
The row encoding follows the repository's
`RadicalCoordinates/Centers/Unipotent/LeviAction.lean`.

Source: GLS3 §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`), especially the fixed
root parametrizations and subsystem construction in Proposition 2.6.2.
-/

@[expose] public section
namespace Triality.Standard.ElementaryNine.Binary
open ElementaryCentralKernel.FixedRootCommutant
local infixl:70 " ⊙ " => Mul.mul

/-- Evaluate the highest-root word using the two folded simple Weyl words. -/
def firstWord {M : Type*} [Mul M] (g : Fin 4 → M) : M :=
  let c := g 0 * g 1 * g 0
  let a := g 2 * g 3 * g 2
  (c * a) * (g 0 * g 1) * (a * c)

def secondWord {M : Type*} [Mul M] (g : Fin 4 → M) : M := g 2 * g 3

abbrev Rows := Fin 28 → ℕ

def bitEntry (a : ℕ) (j : Fin 28) : ZMod 2 := if a.testBit j.val then 1 else 0

def decode (a : Rows) : Matrix (Fin 28) (Fin 28) (ZMod 2) := fun i j => bitEntry (a i) j

def multiply (a b : Rows) : Rows := fun i =>
  ((List.finRange 28).map (fun j => if (a i).testBit j.val then b j else 0)).foldr Nat.xor 0

private theorem bitEntry_xor (a b : ℕ) (j : Fin 28) :
    bitEntry (Nat.xor a b) j = bitEntry a j + bitEntry b j := by
  simp only [bitEntry, Nat.xor_eq, Nat.testBit_xor]
  cases a.testBit j.val <;> cases b.testBit j.val <;> decide

private theorem bitEntry_fold (l : List ℕ) (j : Fin 28) :
    bitEntry (l.foldr Nat.xor 0) j = (l.map (fun a => bitEntry a j)).sum := by
  induction l with
  | nil => simp [bitEntry]
  | cons a l ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, bitEntry_xor, ih]

theorem decode_multiply (a b : Rows) : decode (multiply a b) = Mul.mul (decode a) (decode b) := by
  ext i j
  change bitEntry (((List.finRange 28).map (fun k =>
    if (a i).testBit k.val then b k else 0)).foldr Nat.xor 0) j =
      ∑ k : Fin 28, bitEntry (a i) k * bitEntry (b k) j
  rw [bitEntry_fold]
  simp only [List.map_map]
  have h (k : Fin 28) : bitEntry (if (a i).testBit k.val then b k else 0) j =
      bitEntry (a i) k * bitEntry (b k) j := by
    unfold bitEntry
    split <;> simp_all
  simp only [Function.comp_apply, h, ← List.ofFn_id, List.map_ofFn, List.sum_ofFn, id_eq]

/-- Intermediate binary rows, checked against the four pinned root matrices. -/
def rows : Fin 16 → Rows :=
  ![![1, 262146, 4, 8, 272, 32, 1088, 128, 256, 544, 1024, 2176, 4096, 8192, 16384, 32768, 65536, 393229, 262144, 524288, 17825792, 35651584, 4194304, 8388608, 16777216, 33554432, 71303168, 142606336],
    ![1, 131074, 4, 8, 16, 544, 64, 2176, 272, 512, 1088, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 393229, 524288, 1048576, 2097152, 71303168, 142606336, 17825792, 35651584, 67108864, 134217728],
    ![65, 2, 67108868, 134217736, 16, 98, 64, 128, 3355392, 131584, 52224, 2048, 1184256, 2236928, 18432, 34816, 3342336, 131072, 13421568, 526336, 1179648, 2228224, 4737024, 8947712, 150994946, 100663298, 67108864, 134217728],
    ![33, 2, 33554436, 16777224, 16, 32, 98, 128, 256, 13056, 263168, 13421568, 4352, 8448, 4473856, 8684544, 65792, 3355392, 262144, 13369344, 1118464, 2171136, 4456448, 8650752, 16777216, 33554432, 100663298, 150994946],
    ![1, 15, 4, 8, 256, 512, 1024, 2048, 16, 32, 64, 128, 4096, 8192, 16384, 32768, 65536, 262144, 131072, 524288, 16777216, 33554432, 67108864, 134217728, 1048576, 2097152, 4194304, 8388608],
    ![3, 2, 6, 10, 16, 64, 32, 128, 131072, 65536, 524288, 262144, 2097152, 1048576, 8388608, 4194304, 512, 256, 2048, 1024, 8192, 4096, 32768, 16384, 134217728, 67108864, 33554432, 16777216],
    ![3, 13, 6, 10, 131072, 65536, 524288, 262144, 16, 64, 32, 128, 2097152, 1048576, 8388608, 4194304, 512, 2048, 256, 1024, 134217728, 67108864, 33554432, 16777216, 8192, 4096, 32768, 16384],
    ![1, 262159, 4, 8, 256, 544, 1024, 2176, 272, 32, 1088, 128, 4096, 8192, 16384, 32768, 65536, 262144, 393229, 524288, 16777216, 33554432, 71303168, 142606336, 17825792, 35651584, 4194304, 8388608],
    ![14, 15, 11, 7, 256, 1024, 512, 2048, 262144, 65536, 524288, 131072, 33554432, 16777216, 134217728, 67108864, 32, 16, 128, 64, 8192, 4096, 32768, 16384, 8388608, 4194304, 2097152, 1048576],
    ![262158, 13, 262155, 262151, 262144, 65536, 524288, 393229, 256, 1024, 544, 2176, 33554432, 16777216, 142606336, 71303168, 32, 128, 272, 1088, 8388608, 4194304, 35651584, 17825792, 8192, 4096, 32768, 16384],
    ![131, 2, 134, 138, 128, 32, 64, 146, 262144, 524288, 66560, 133120, 4194304, 8388608, 1064960, 2129920, 1024, 2048, 262400, 524800, 16384, 32768, 4198400, 8396800, 16777216, 33554432, 67108864, 134217728],
    ![67, 2, 67108870, 134217738, 16, 64, 98, 128, 131072, 3342336, 526336, 13421568, 2228224, 1179648, 8947712, 4737024, 131584, 3355392, 2048, 52224, 2236928, 1184256, 34816, 18432, 134217728, 67108864, 100663298, 150994946],
    ![19, 2, 22, 26, 146, 32, 64, 16, 262400, 524800, 65536, 131072, 4198400, 8396800, 1048576, 2097152, 66560, 133120, 256, 512, 1064960, 2129920, 4096, 8192, 16777216, 33554432, 67108864, 134217728],
    ![35, 2, 33554438, 16777226, 16, 98, 32, 128, 3355392, 65792, 13369344, 262144, 2171136, 1118464, 8650752, 4456448, 13056, 256, 13421568, 263168, 8448, 4352, 8684544, 4473856, 150994946, 100663298, 33554432, 16777216],
    ![193, 2, 67108996, 134217864, 128, 64, 98, 146, 2048, 52224, 657920, 16776960, 34816, 18432, 11184640, 5921280, 526336, 13421568, 133120, 3394560, 8947712, 4737024, 2263040, 1198080, 134217728, 67108864, 100663298, 150994946],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728]]

def products : List (Fin 16 × Fin 16 × Fin 16) :=
  [(0, 1, 7), (7, 0, 4), (2, 3, 11), (11, 2, 5), (4, 5, 6),
    (5, 4, 8), (6, 7, 9), (9, 8, 10), (10, 10, 12), (11, 11, 13),
    (10, 11, 14), (11, 10, 14), (12, 10, 15), (13, 11, 15)]

set_option maxRecDepth 4096 in
theorem seed_check (k : Fin 4) : decode (rows (k.castLE (by decide))) =
    constantMatrix (F := ZMod 2) k := by
  revert k
  decide +kernel

set_option maxRecDepth 4096 in
theorem products_check : ∀ t ∈ products, multiply (rows t.1) (rows t.2.1) = rows t.2.2 := by
  have h : products.all (fun t => decide (multiply (rows t.1) (rows t.2.1) = rows t.2.2)) = true := by
    decide +kernel
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

theorem identity_check : decode (rows 15) = 1 := by decide +kernel

theorem product_eq (i j k : Fin 16) (h : (i,j,k) ∈ products) :
    Mul.mul (decode (rows i)) (decode (rows j)) = decode (rows k) :=
  (decode_multiply _ _).symm.trans (congrArg decode (products_check _ h))

def firstMatrix : Matrix (Fin 28) (Fin 28) (ZMod 2) := decode (rows 10)
def secondMatrix : Matrix (Fin 28) (Fin 28) (ZMod 2) := decode (rows 11)

theorem firstWord_matrix : firstWord (constantMatrix (F := ZMod 2)) = firstMatrix := by
  unfold firstWord firstMatrix
  rw [← seed_check 0, ← seed_check 1, ← seed_check 2, ← seed_check 3]
  change ((decode (rows 0) ⊙ decode (rows 1) ⊙ decode (rows 0)) ⊙
    (decode (rows 2) ⊙ decode (rows 3) ⊙ decode (rows 2))) ⊙
    (decode (rows 0) ⊙ decode (rows 1)) ⊙
    ((decode (rows 2) ⊙ decode (rows 3) ⊙ decode (rows 2)) ⊙
    (decode (rows 0) ⊙ decode (rows 1) ⊙ decode (rows 0))) = decode (rows 10)
  rw [product_eq 0 1 7 (by decide), product_eq 7 0 4 (by decide),
    product_eq 2 3 11 (by decide), product_eq 11 2 5 (by decide),
    product_eq 4 5 6 (by decide), product_eq 5 4 8 (by decide),
    product_eq 6 7 9 (by decide), product_eq 9 8 10 (by decide)]

theorem secondWord_matrix : secondWord (constantMatrix (F := ZMod 2)) = secondMatrix := by
  unfold secondWord secondMatrix
  rw [← seed_check 2, ← seed_check 3]
  exact product_eq 2 3 11 (by decide)

theorem firstMatrix_cube : firstMatrix ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  exact ((congrArg (fun a => Mul.mul a firstMatrix) (product_eq 10 10 12 (by decide))).trans
    (product_eq 12 10 15 (by decide))).trans identity_check

theorem secondMatrix_cube : secondMatrix ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  exact ((congrArg (fun a => Mul.mul a secondMatrix) (product_eq 11 11 13 (by decide))).trans
    (product_eq 13 11 15 (by decide))).trans identity_check

theorem matrices_commute : Commute firstMatrix secondMatrix :=
  (product_eq 10 11 14 (by decide)).trans (product_eq 11 10 14 (by decide)).symm

/-- Rows for the three powers of either generator. -/
def firstPower (i : Fin 3) : Rows := rows (![15, 10, 12] i)
def secondPower (i : Fin 3) : Rows := rows (![15, 11, 13] i)

theorem firstPower_eq (i : Fin 3) : decode (firstPower i) = firstMatrix ^ i.val := by
  fin_cases i
  · exact identity_check
  · simp [firstPower, firstMatrix]
  · change decode (rows 12) = decode (rows 10) ^ 2
    rw [pow_two]
    exact (product_eq 10 10 12 (by decide)).symm

theorem secondPower_eq (i : Fin 3) : decode (secondPower i) = secondMatrix ^ i.val := by
  fin_cases i
  · exact identity_check
  · simp [secondPower, secondMatrix]
  · change decode (rows 13) = decode (rows 11) ^ 2
    rw [pow_two]
    exact (product_eq 11 11 13 (by decide)).symm

set_option maxRecDepth 4096 in
theorem separation_check (i j : Fin 3)
    (h₁ : bitEntry (multiply (firstPower i) (secondPower j) 0) 1 = 0)
    (h₂ : bitEntry (multiply (firstPower i) (secondPower j) 4) 7 = 0) :
    i = 0 ∧ j = 0 := by
  revert i j
  decide +kernel

theorem independent (i j : Fin 3) (h : Mul.mul (firstMatrix ^ i.val) (secondMatrix ^ j.val) = 1) :
    i = 0 ∧ j = 0 := by
  rw [← firstPower_eq, ← secondPower_eq, ← decode_multiply] at h
  apply separation_check i j
  · exact (congrFun₂ h 0 1).trans (by decide)
  · exact (congrFun₂ h 4 7).trans (by decide)

end Triality.Standard.ElementaryNine.Binary
