module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Data
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank certificates for the five degree-fourteen vertex quotients

Each generator is decoded from the literal diagonal block of `actionColumns`,
whose entries are columns. Packed binary multiplication computes `AB-I` and
`A-B`. Explicit invertible minors of sizes ten and twelve certify the required
lower bounds. All finite identities are checked by kernel reduction; the
witness search has no role in the proof.

These are the numerical vertex calculations used for Guralnick–Malle,
Classification of 2F-modules I, Proposition 4.3, pp.10–11. The original
ATLAS action data and attribution remain in `CoordinateFiltrations.Data`;
see LICENSES/ATLAS.txt. No new external matrix data are introduced.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.VertexCertificates
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
open Thompson.BinaryMatrix

private theorem rank_lower_of_minor {n k : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (r c : Fin k → Fin n)
    (minor inverse : Array ℕ)
    (hm : decode k minor = M.submatrix r c)
    (hi : ∀ x : Fin k, rowProduct inverse[x.val]! minor k = 2 ^ x.val) :
    k ≤ M.rank := by
  have h := Matrix.rank_mul_le_right (decode k inverse) (decode k minor)
  rw [decode_mul_one k inverse minor hi, Matrix.rank_one, Fintype.card_fin] at h
  rw [hm] at h
  exact h.trans (Matrix.rank_submatrix_le M r c)

namespace b00

private def generators : Fin 2 → Array ℕ := ![#[15383, 8781, 7695, 21, 8720, 6763, 1024, 8448, 1344, 2927, 15, 4, 847, 14845], #[15549, 4247, 7920, 4226, 8450, 16, 32, 2667, 14355, 1788, 463, 15511, 6396, 15379]]
private def product : Array ℕ := #[2671, 2048, 256, 847, 7149, 7695, 463, 1024, 14844, 8208, 8792, 7920, 7319, 14845]
private def regular : Array ℕ := #[2670, 2050, 260, 839, 7165, 7727, 399, 1152, 14588, 8720, 9816, 5872, 3223, 6653]
private def seven : Array ℕ := #[170, 13018, 255, 4247, 786, 6779, 1056, 11115, 15699, 3475, 448, 15507, 7091, 1518]
private def regularRows : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
private def regularCols : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10]
private def regularMinor : Array ℕ := #[366, 2, 4, 327, 509, 815, 143, 640, 252, 272]
private def regularInverse : Array ℕ := #[700, 2, 4, 505, 428, 844, 286, 771, 940, 899]
private def sevenRows : Fin 12 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13]
private def sevenCols : Fin 12 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12]
private def sevenMinor : Array ℕ := #[170, 2778, 255, 2199, 786, 2683, 1056, 875, 3411, 1427, 448, 1518]
private def sevenInverse : Array ℕ := #[1779, 781, 2704, 1501, 1952, 4056, 3014, 2313, 1743, 626, 3992, 463]

private theorem generators_checked : ∀ j,
    decode 14 (generators j) = factorMatrix 0 ⟨0, by decide⟩ j := by
  intro j
  apply Matrix.ext
  intro x y
  change Thompson.BinaryMatrix.bit (generators j)[x.val]! y.val =
    G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.bit (actionColumns 0 j (blockIndex 0 ⟨0, by decide⟩ y))
      (blockIndex 0 ⟨0, by decide⟩ x).val
  revert j x y
  decide +kernel

private theorem product_checked :
    decode 14 (generators 0) * decode 14 (generators 1) = decode 14 product :=
  decode_mul 14 _ _ _ (by decide +kernel)

private theorem regular_checked : decode 14 product - 1 = decode 14 regular := by
  apply Matrix.ext
  change ∀ x y : Fin 14, Thompson.BinaryMatrix.bit product[x.val]! y.val -
    (if x = y then 1 else 0) = Thompson.BinaryMatrix.bit regular[x.val]! y.val
  decide +kernel

private theorem seven_checked :
    decode 14 (generators 0) - decode 14 (generators 1) = decode 14 seven := by
  apply Matrix.ext
  change ∀ x y : Fin 14, Thompson.BinaryMatrix.bit (generators 0)[x.val]! y.val -
    Thompson.BinaryMatrix.bit (generators 1)[x.val]! y.val =
      Thompson.BinaryMatrix.bit seven[x.val]! y.val
  decide +kernel

private theorem regular_rank : 10 ≤ (decode 14 regular).rank :=
  rank_lower_of_minor _ regularRows regularCols regularMinor regularInverse
    (by
      apply Matrix.ext
      change ∀ x y : Fin 10, Thompson.BinaryMatrix.bit regularMinor[x.val]! y.val =
        Thompson.BinaryMatrix.bit regular[(regularRows x).val]! (regularCols y).val
      decide +kernel) (by decide +kernel)

private theorem seven_rank : 12 ≤ (decode 14 seven).rank :=
  rank_lower_of_minor _ sevenRows sevenCols sevenMinor sevenInverse
    (by
      apply Matrix.ext
      change ∀ x y : Fin 12, Thompson.BinaryMatrix.bit sevenMinor[x.val]! y.val =
        Thompson.BinaryMatrix.bit seven[(sevenRows x).val]! (sevenCols y).val
      decide +kernel) (by decide +kernel)

private theorem ranks_of_generators (A B : Matrix (Fin 14) (Fin 14) (ZMod 2))
    (ha : decode 14 (generators 0) = A) (hb : decode 14 (generators 1) = B) :
    10 ≤ (A * B - 1).rank ∧ 12 ≤ (A - B).rank := by
  rw [← ha, ← hb, product_checked, regular_checked, seven_checked]
  exact ⟨regular_rank, seven_rank⟩

/-- The two inverse-free rank bounds on the literal block (0, 0). -/
theorem ranks :
    10 ≤ (factorMatrix 0 ⟨0, by decide⟩ 0 * factorMatrix 0 ⟨0, by decide⟩ 1 - 1).rank ∧
    12 ≤ (factorMatrix 0 ⟨0, by decide⟩ 0 - factorMatrix 0 ⟨0, by decide⟩ 1).rank :=
  ranks_of_generators _ _ (generators_checked 0) (generators_checked 1)

end b00

namespace b04

private def generators : Fin 2 → Array ℕ := ![#[1067, 690, 10252, 10027, 13822, 784, 9688, 7810, 6343, 14332, 10854, 424, 11785, 9461], #[369, 12353, 6321, 11724, 11972, 7116, 15998, 7809, 2569, 8637, 5403, 6373, 3391, 106]]
private def product : Array ℕ := #[4651, 14965, 11762, 14837, 652, 1392, 15503, 4028, 7332, 4976, 13424, 8840, 148, 6470]
private def regular : Array ℕ := #[4650, 14967, 11766, 14845, 668, 1360, 15567, 3900, 7588, 4464, 12400, 10888, 4244, 14662]
private def seven : Array ℕ := #[1370, 13043, 12477, 2791, 6970, 6364, 7078, 3, 4814, 5697, 16253, 6477, 9014, 9375]
private def regularRows : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10]
private def regularCols : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10]
private def regularMinor : Array ℕ := #[42, 119, 1014, 509, 156, 848, 719, 828, 932, 112]
private def regularInverse : Array ℕ := #[463, 605, 400, 773, 53, 345, 876, 688, 994, 155]
private def sevenRows : Fin 12 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12]
private def sevenCols : Fin 12 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12]
private def sevenMinor : Array ℕ := #[858, 2291, 2237, 1255, 3386, 3292, 3494, 3, 2254, 2625, 3405, 310]
private def sevenInverse : Array ℕ := #[2278, 2150, 1300, 3905, 1883, 1258, 565, 3422, 1731, 1163, 3613, 3160]

private theorem generators_checked : ∀ j,
    decode 14 (generators j) = factorMatrix 0 ⟨4, by decide⟩ j := by
  intro j
  apply Matrix.ext
  intro x y
  change Thompson.BinaryMatrix.bit (generators j)[x.val]! y.val =
    G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.bit (actionColumns 0 j (blockIndex 0 ⟨4, by decide⟩ y))
      (blockIndex 0 ⟨4, by decide⟩ x).val
  revert j x y
  decide +kernel

private theorem product_checked :
    decode 14 (generators 0) * decode 14 (generators 1) = decode 14 product :=
  decode_mul 14 _ _ _ (by decide +kernel)

private theorem regular_checked : decode 14 product - 1 = decode 14 regular := by
  apply Matrix.ext
  change ∀ x y : Fin 14, Thompson.BinaryMatrix.bit product[x.val]! y.val -
    (if x = y then 1 else 0) = Thompson.BinaryMatrix.bit regular[x.val]! y.val
  decide +kernel

private theorem seven_checked :
    decode 14 (generators 0) - decode 14 (generators 1) = decode 14 seven := by
  apply Matrix.ext
  change ∀ x y : Fin 14, Thompson.BinaryMatrix.bit (generators 0)[x.val]! y.val -
    Thompson.BinaryMatrix.bit (generators 1)[x.val]! y.val =
      Thompson.BinaryMatrix.bit seven[x.val]! y.val
  decide +kernel

private theorem regular_rank : 10 ≤ (decode 14 regular).rank :=
  rank_lower_of_minor _ regularRows regularCols regularMinor regularInverse
    (by
      apply Matrix.ext
      change ∀ x y : Fin 10, Thompson.BinaryMatrix.bit regularMinor[x.val]! y.val =
        Thompson.BinaryMatrix.bit regular[(regularRows x).val]! (regularCols y).val
      decide +kernel) (by decide +kernel)

private theorem seven_rank : 12 ≤ (decode 14 seven).rank :=
  rank_lower_of_minor _ sevenRows sevenCols sevenMinor sevenInverse
    (by
      apply Matrix.ext
      change ∀ x y : Fin 12, Thompson.BinaryMatrix.bit sevenMinor[x.val]! y.val =
        Thompson.BinaryMatrix.bit seven[(sevenRows x).val]! (sevenCols y).val
      decide +kernel) (by decide +kernel)

private theorem ranks_of_generators (A B : Matrix (Fin 14) (Fin 14) (ZMod 2))
    (ha : decode 14 (generators 0) = A) (hb : decode 14 (generators 1) = B) :
    10 ≤ (A * B - 1).rank ∧ 12 ≤ (A - B).rank := by
  rw [← ha, ← hb, product_checked, regular_checked, seven_checked]
  exact ⟨regular_rank, seven_rank⟩

/-- The two inverse-free rank bounds on the literal block (0, 4). -/
theorem ranks :
    10 ≤ (factorMatrix 0 ⟨4, by decide⟩ 0 * factorMatrix 0 ⟨4, by decide⟩ 1 - 1).rank ∧
    12 ≤ (factorMatrix 0 ⟨4, by decide⟩ 0 - factorMatrix 0 ⟨4, by decide⟩ 1).rank :=
  ranks_of_generators _ _ (generators_checked 0) (generators_checked 1)

end b04

namespace b07

private def generators : Fin 2 → Array ℕ := ![#[3447, 3581, 12761, 14832, 13335, 5073, 13521, 11234, 13184, 4977, 13983, 10074, 13676, 16255], #[11131, 8562, 14725, 1790, 11654, 4839, 10964, 16268, 13322, 15350, 11398, 7922, 911, 3077]]
private def product : Array ℕ := #[8263, 14407, 11995, 3915, 15622, 8150, 12457, 15302, 16378, 12989, 16258, 4001, 4174, 4805]
private def regular : Array ℕ := #[8262, 14405, 11999, 3907, 15638, 8182, 12521, 15174, 16122, 12477, 15234, 1953, 78, 12997]
private def seven : Array ℕ := #[9740, 11407, 2140, 16142, 6545, 310, 7685, 5230, 1930, 10375, 6681, 14760, 14051, 13178]
private def regularRows : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
private def regularCols : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10]
private def regularMinor : Array ℕ := #[70, 69, 735, 835, 790, 1014, 233, 326, 762, 189]
private def regularInverse : Array ℕ := #[600, 603, 905, 552, 26, 213, 467, 310, 129, 345]
private def sevenRows : Fin 12 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13]
private def sevenCols : Fin 12 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12]
private def sevenMinor : Array ℕ := #[524, 1167, 1116, 3854, 3473, 310, 3589, 2158, 906, 1159, 3609, 2938]
private def sevenInverse : Array ℕ := #[3622, 1296, 1469, 514, 1023, 2574, 31, 2256, 2428, 1982, 1115, 2110]

private theorem generators_checked : ∀ j,
    decode 14 (generators j) = factorMatrix 0 ⟨7, by decide⟩ j := by
  intro j
  apply Matrix.ext
  intro x y
  change Thompson.BinaryMatrix.bit (generators j)[x.val]! y.val =
    G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.bit (actionColumns 0 j (blockIndex 0 ⟨7, by decide⟩ y))
      (blockIndex 0 ⟨7, by decide⟩ x).val
  revert j x y
  decide +kernel

private theorem product_checked :
    decode 14 (generators 0) * decode 14 (generators 1) = decode 14 product :=
  decode_mul 14 _ _ _ (by decide +kernel)

private theorem regular_checked : decode 14 product - 1 = decode 14 regular := by
  apply Matrix.ext
  change ∀ x y : Fin 14, Thompson.BinaryMatrix.bit product[x.val]! y.val -
    (if x = y then 1 else 0) = Thompson.BinaryMatrix.bit regular[x.val]! y.val
  decide +kernel

private theorem seven_checked :
    decode 14 (generators 0) - decode 14 (generators 1) = decode 14 seven := by
  apply Matrix.ext
  change ∀ x y : Fin 14, Thompson.BinaryMatrix.bit (generators 0)[x.val]! y.val -
    Thompson.BinaryMatrix.bit (generators 1)[x.val]! y.val =
      Thompson.BinaryMatrix.bit seven[x.val]! y.val
  decide +kernel

private theorem regular_rank : 10 ≤ (decode 14 regular).rank :=
  rank_lower_of_minor _ regularRows regularCols regularMinor regularInverse
    (by
      apply Matrix.ext
      change ∀ x y : Fin 10, Thompson.BinaryMatrix.bit regularMinor[x.val]! y.val =
        Thompson.BinaryMatrix.bit regular[(regularRows x).val]! (regularCols y).val
      decide +kernel) (by decide +kernel)

private theorem seven_rank : 12 ≤ (decode 14 seven).rank :=
  rank_lower_of_minor _ sevenRows sevenCols sevenMinor sevenInverse
    (by
      apply Matrix.ext
      change ∀ x y : Fin 12, Thompson.BinaryMatrix.bit sevenMinor[x.val]! y.val =
        Thompson.BinaryMatrix.bit seven[(sevenRows x).val]! (sevenCols y).val
      decide +kernel) (by decide +kernel)

private theorem ranks_of_generators (A B : Matrix (Fin 14) (Fin 14) (ZMod 2))
    (ha : decode 14 (generators 0) = A) (hb : decode 14 (generators 1) = B) :
    10 ≤ (A * B - 1).rank ∧ 12 ≤ (A - B).rank := by
  rw [← ha, ← hb, product_checked, regular_checked, seven_checked]
  exact ⟨regular_rank, seven_rank⟩

/-- The two inverse-free rank bounds on the literal block (0, 7). -/
theorem ranks :
    10 ≤ (factorMatrix 0 ⟨7, by decide⟩ 0 * factorMatrix 0 ⟨7, by decide⟩ 1 - 1).rank ∧
    12 ≤ (factorMatrix 0 ⟨7, by decide⟩ 0 - factorMatrix 0 ⟨7, by decide⟩ 1).rank :=
  ranks_of_generators _ _ (generators_checked 0) (generators_checked 1)

end b07

namespace b11

private def generators : Fin 2 → Array ℕ := ![#[970, 11896, 4331, 2521, 1541, 7213, 15638, 9148, 10052, 16114, 9305, 9464, 10060, 14775], #[9612, 10324, 3138, 13143, 9589, 13110, 2312, 10637, 4593, 11256, 497, 8945, 2688, 8344]]
private def product : Array ℕ := #[399, 1148, 10172, 8235, 967, 47, 6538, 6730, 7722, 15474, 7119, 9464, 11645, 10060]
private def regular : Array ℕ := #[398, 1150, 10168, 8227, 983, 15, 6602, 6858, 7978, 15986, 8143, 11512, 15741, 1868]
private def seven : Array ℕ := #[9798, 1580, 7337, 14990, 9072, 12059, 13342, 2609, 14005, 5386, 9640, 1545, 11724, 6447]
private def regularRows : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 11]
private def regularCols : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
private def regularMinor : Array ℕ := #[398, 126, 952, 35, 983, 15, 458, 714, 810, 248]
private def regularInverse : Array ℕ := #[405, 877, 645, 93, 387, 752, 708, 1002, 606, 670]
private def sevenRows : Fin 12 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
private def sevenCols : Fin 12 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
private def sevenMinor : Array ℕ := #[1606, 1580, 3241, 2702, 880, 3867, 1054, 2609, 1717, 1290, 1448, 1545]
private def sevenInverse : Array ℕ := #[1593, 4017, 3227, 2438, 1452, 672, 1172, 2833, 2935, 2303, 3904, 2378]

private theorem generators_checked : ∀ j,
    decode 14 (generators j) = factorMatrix 1 ⟨1, by decide⟩ j := by
  intro j
  apply Matrix.ext
  intro x y
  change Thompson.BinaryMatrix.bit (generators j)[x.val]! y.val =
    G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.bit (actionColumns 1 j (blockIndex 1 ⟨1, by decide⟩ y))
      (blockIndex 1 ⟨1, by decide⟩ x).val
  revert j x y
  decide +kernel

private theorem product_checked :
    decode 14 (generators 0) * decode 14 (generators 1) = decode 14 product :=
  decode_mul 14 _ _ _ (by decide +kernel)

private theorem regular_checked : decode 14 product - 1 = decode 14 regular := by
  apply Matrix.ext
  change ∀ x y : Fin 14, Thompson.BinaryMatrix.bit product[x.val]! y.val -
    (if x = y then 1 else 0) = Thompson.BinaryMatrix.bit regular[x.val]! y.val
  decide +kernel

private theorem seven_checked :
    decode 14 (generators 0) - decode 14 (generators 1) = decode 14 seven := by
  apply Matrix.ext
  change ∀ x y : Fin 14, Thompson.BinaryMatrix.bit (generators 0)[x.val]! y.val -
    Thompson.BinaryMatrix.bit (generators 1)[x.val]! y.val =
      Thompson.BinaryMatrix.bit seven[x.val]! y.val
  decide +kernel

private theorem regular_rank : 10 ≤ (decode 14 regular).rank :=
  rank_lower_of_minor _ regularRows regularCols regularMinor regularInverse
    (by
      apply Matrix.ext
      change ∀ x y : Fin 10, Thompson.BinaryMatrix.bit regularMinor[x.val]! y.val =
        Thompson.BinaryMatrix.bit regular[(regularRows x).val]! (regularCols y).val
      decide +kernel) (by decide +kernel)

private theorem seven_rank : 12 ≤ (decode 14 seven).rank :=
  rank_lower_of_minor _ sevenRows sevenCols sevenMinor sevenInverse
    (by
      apply Matrix.ext
      change ∀ x y : Fin 12, Thompson.BinaryMatrix.bit sevenMinor[x.val]! y.val =
        Thompson.BinaryMatrix.bit seven[(sevenRows x).val]! (sevenCols y).val
      decide +kernel) (by decide +kernel)

private theorem ranks_of_generators (A B : Matrix (Fin 14) (Fin 14) (ZMod 2))
    (ha : decode 14 (generators 0) = A) (hb : decode 14 (generators 1) = B) :
    10 ≤ (A * B - 1).rank ∧ 12 ≤ (A - B).rank := by
  rw [← ha, ← hb, product_checked, regular_checked, seven_checked]
  exact ⟨regular_rank, seven_rank⟩

/-- The two inverse-free rank bounds on the literal block (1, 1). -/
theorem ranks :
    10 ≤ (factorMatrix 1 ⟨1, by decide⟩ 0 * factorMatrix 1 ⟨1, by decide⟩ 1 - 1).rank ∧
    12 ≤ (factorMatrix 1 ⟨1, by decide⟩ 0 - factorMatrix 1 ⟨1, by decide⟩ 1).rank :=
  ranks_of_generators _ _ (generators_checked 0) (generators_checked 1)

end b11

namespace b16

private def generators : Fin 2 → Array ℕ := ![#[705, 14964, 12504, 13835, 2385, 2977, 5174, 14535, 13113, 1951, 2357, 15011, 14789, 1194], #[7238, 9819, 10520, 2258, 3149, 3148, 1357, 11592, 3153, 13810, 10690, 9182, 2196, 1044]]
private def product : Array ℕ := #[433, 14072, 8218, 8831, 15049, 10047, 11796, 5214, 8630, 10931, 6864, 437, 15956, 9807]
private def regular : Array ℕ := #[432, 14074, 8222, 8823, 15065, 10015, 11860, 5342, 8374, 10419, 7888, 2485, 11860, 1615]
private def seven : Array ℕ := #[7815, 7215, 6592, 16089, 1308, 2029, 4475, 5519, 16232, 12909, 8439, 6525, 12625, 190]
private def regularRows : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 7, 8, 9, 10]
private def regularCols : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 11]
private def regularMinor : Array ℕ := #[432, 250, 30, 119, 729, 287, 222, 182, 691, 720]
private def regularInverse : Array ℕ := #[204, 464, 441, 732, 689, 507, 999, 931, 232, 245]
private def sevenRows : Fin 12 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12]
private def sevenCols : Fin 12 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12]
private def sevenMinor : Array ℕ := #[3719, 3119, 2496, 3801, 1308, 2029, 2427, 3471, 2669, 247, 2429, 2385]
private def sevenInverse : Array ℕ := #[1146, 1622, 534, 410, 1051, 3980, 456, 2149, 1899, 1648, 236, 3778]

private theorem generators_checked : ∀ j,
    decode 14 (generators j) = factorMatrix 1 ⟨6, by decide⟩ j := by
  intro j
  apply Matrix.ext
  intro x y
  change Thompson.BinaryMatrix.bit (generators j)[x.val]! y.val =
    G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.bit (actionColumns 1 j (blockIndex 1 ⟨6, by decide⟩ y))
      (blockIndex 1 ⟨6, by decide⟩ x).val
  revert j x y
  decide +kernel

private theorem product_checked :
    decode 14 (generators 0) * decode 14 (generators 1) = decode 14 product :=
  decode_mul 14 _ _ _ (by decide +kernel)

private theorem regular_checked : decode 14 product - 1 = decode 14 regular := by
  apply Matrix.ext
  change ∀ x y : Fin 14, Thompson.BinaryMatrix.bit product[x.val]! y.val -
    (if x = y then 1 else 0) = Thompson.BinaryMatrix.bit regular[x.val]! y.val
  decide +kernel

private theorem seven_checked :
    decode 14 (generators 0) - decode 14 (generators 1) = decode 14 seven := by
  apply Matrix.ext
  change ∀ x y : Fin 14, Thompson.BinaryMatrix.bit (generators 0)[x.val]! y.val -
    Thompson.BinaryMatrix.bit (generators 1)[x.val]! y.val =
      Thompson.BinaryMatrix.bit seven[x.val]! y.val
  decide +kernel

private theorem regular_rank : 10 ≤ (decode 14 regular).rank :=
  rank_lower_of_minor _ regularRows regularCols regularMinor regularInverse
    (by
      apply Matrix.ext
      change ∀ x y : Fin 10, Thompson.BinaryMatrix.bit regularMinor[x.val]! y.val =
        Thompson.BinaryMatrix.bit regular[(regularRows x).val]! (regularCols y).val
      decide +kernel) (by decide +kernel)

private theorem seven_rank : 12 ≤ (decode 14 seven).rank :=
  rank_lower_of_minor _ sevenRows sevenCols sevenMinor sevenInverse
    (by
      apply Matrix.ext
      change ∀ x y : Fin 12, Thompson.BinaryMatrix.bit sevenMinor[x.val]! y.val =
        Thompson.BinaryMatrix.bit seven[(sevenRows x).val]! (sevenCols y).val
      decide +kernel) (by decide +kernel)

private theorem ranks_of_generators (A B : Matrix (Fin 14) (Fin 14) (ZMod 2))
    (ha : decode 14 (generators 0) = A) (hb : decode 14 (generators 1) = B) :
    10 ≤ (A * B - 1).rank ∧ 12 ≤ (A - B).rank := by
  rw [← ha, ← hb, product_checked, regular_checked, seven_checked]
  exact ⟨regular_rank, seven_rank⟩

/-- The two inverse-free rank bounds on the literal block (1, 6). -/
theorem ranks :
    10 ≤ (factorMatrix 1 ⟨6, by decide⟩ 0 * factorMatrix 1 ⟨6, by decide⟩ 1 - 1).rank ∧
    12 ≤ (factorMatrix 1 ⟨6, by decide⟩ 0 - factorMatrix 1 ⟨6, by decide⟩ 1).rank :=
  ranks_of_generators _ _ (generators_checked 0) (generators_checked 1)

end b16

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.VertexCertificates
