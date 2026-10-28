module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.Packed
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Small rank witnesses for the two binary G₂ cycle factors

For each of the two actual cycle-factor matrix pairs, an invertible minor of
`AB - I` has size ten and an invertible minor of `A - B` has size twelve.
The data below select rows and columns and give the minor's inverse. Packed
XOR identities are checked by the kernel, then decoded into matrix identities;
rank monotonicity gives the lower bounds without computing the full rank.

The matrices are the existing attributed `CycleData.factorRows`, decoded as
rows (least significant bit first). No additional representation is postulated.
The root-matrix provenance and ATLAS license are recorded in `MatrixData` and
`LICENSES/ATLAS.txt`. These newly calculated minors use only that existing data.

Source application: Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3, pp.10–11. The degree-32 calculation is additional to the
source's prior offender-based exclusion; transport to the literal incidence
kernel subspace and quotient is in the parent `CycleCertificates` module.
-/

public section

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CycleCertificates
open G2DerivedPermutationFiltration.CycleData
open G2DerivedPermutationFiltration.CycleData.Certificate

private def rows {m n : ℕ} (r : Fin m → ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit (r i) j.val

private theorem rows_mul {m n p : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)
    (i : Fin m) (j : Fin p) :
    (rows (n := n) a * rows b) i j =
      bit (combine b (fun k => (a i).testBit k.val)) j.val := by
  rw [bit_combine, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

private def regularRows (f : Fin 2) (i : Fin 32) : ℕ :=
  combine (factorRows f 1) (fun k => (factorRows f 0 i).testBit k.val) ^^^ 2 ^ i.val

private theorem factor_rows (f a : Fin 2) : factorMatrix f a = rows (factorRows f a) := rfl

private theorem regular_entries (f : Fin 2) (i j : Fin 32) :
    (factorMatrix f 0 * factorMatrix f 1 - 1) i j = bit (regularRows f i) j.val := by
  rw [factor_rows f 0, factor_rows f 1, Matrix.sub_apply, rows_mul,
    Matrix.one_apply, regularRows, bit_xor, bit_power]
  simpa only [Fin.val_inj] using CharTwo.sub_eq_add
    (bit (combine (factorRows f 1) (fun k => (factorRows f 0 i).testBit k.val)) j.val)
    (if i = j then (1 : ZMod 2) else 0)

private theorem rank_ge_of_minor {n d : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (ri ci : Fin d → Fin n) (mr inv : Fin d → ℕ)
    (he : ∀ i j, M (ri i) (ci j) = bit (mr i) j.val)
    (hi : ∀ i, combine inv (fun k => (mr i).testBit k.val) = 2 ^ i.val) :
    d ≤ M.rank := by
  have hmul : M.submatrix ri ci * rows (n := d) inv = 1 := by
    have hm : M.submatrix ri ci = rows mr := by ext i j; exact he i j
    rw [hm]
    ext i j
    rw [rows_mul, hi, bit_power]
    simp only [Matrix.one_apply, Fin.val_inj]
  have h := Matrix.rank_mul_le_left (M.submatrix ri ci) (rows (n := d) inv)
  rw [hmul, Matrix.rank_one, Fintype.card_fin] at h
  exact h.trans (Matrix.rank_submatrix_le M ri ci)

private def sevenRows (f : Fin 2) (i : Fin 32) : ℕ :=
  factorRows f 0 i ^^^ factorRows f 1 i

private theorem seven_entries (f : Fin 2) (i j : Fin 32) :
    (factorMatrix f 0 - factorMatrix f 1) i j = bit (sevenRows f i) j.val := by
  rw [Matrix.sub_apply, sevenRows, bit_xor]
  exact CharTwo.sub_eq_add _ _

namespace half_regular

private def ri : Fin 10 → Fin 32 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

private def ci : Fin 10 → Fin 32 :=
  ![0, 1, 2, 3, 4, 5, 7, 8, 11, 12]

private def fullRows : Fin 10 → ℕ :=
  ![3040851892, 4194306, 2544629638, 1222893662, 131088, 4128, 2369050751, 2039784171, 3019397119, 3720523665]

private def mr : Fin 10 → ℕ :=
  ![756, 2, 710, 30, 16, 544, 831, 107, 767, 465]

private def inv : Fin 10 → ℕ :=
  ![848, 2, 585, 595, 16, 23, 406, 1006, 824, 55]

set_option maxRecDepth 2048 in
private theorem calc_rows : ∀ i, regularRows 0 (ri i) = fullRows i := by decide +kernel

private theorem calc_minor : ∀ i j,
    (fullRows i).testBit (ci j).val = (mr i).testBit j.val := by decide +kernel

private theorem calc_inverse : ∀ i,
    combine inv (fun k => (mr i).testBit k.val) = 2 ^ i.val := by decide +kernel

end half_regular

/-- The ten-dimensional minor certifies the regular-three bound
on the subspace factor's actual generator matrices. -/
theorem half_regular_rank : 10 ≤ (factorMatrix 0 0 * factorMatrix 0 1 - 1).rank := by
  apply rank_ge_of_minor _ half_regular.ri half_regular.ci half_regular.mr half_regular.inv _ half_regular.calc_inverse
  intro i j
  rw [regular_entries, half_regular.calc_rows]
  unfold bit
  rw [half_regular.calc_minor]

namespace half_seven

private def ri : Fin 12 → Fin 32 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

private def ci : Fin 12 → Fin 32 :=
  ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12]

private def fullRows : Fin 12 → ℕ :=
  ![2840930193, 402654400, 399926429, 2891507866, 2242105128, 1760349990, 100669440, 33556480, 138467224, 180494281, 3863179538, 3709003245]

private def mr : Fin 12 → ℕ :=
  ![913, 576, 541, 1050, 1960, 1958, 3072, 1024, 2968, 4041, 2194, 749]

private def inv : Fin 12 → ℕ :=
  ![3490, 950, 4069, 3171, 3933, 3597, 383, 2091, 2984, 381, 128, 192]

set_option maxRecDepth 2048 in
private theorem calc_rows : ∀ i, sevenRows 0 (ri i) = fullRows i := by decide +kernel

private theorem calc_minor : ∀ i j,
    (fullRows i).testBit (ci j).val = (mr i).testBit j.val := by decide +kernel

private theorem calc_inverse : ∀ i,
    combine inv (fun k => (mr i).testBit k.val) = 2 ^ i.val := by decide +kernel

end half_seven

/-- The twelve-dimensional minor certifies the seven-word bound
on the subspace factor's actual generator matrices. -/
theorem half_seven_rank : 12 ≤ (factorMatrix 0 0 - factorMatrix 0 1).rank := by
  apply rank_ge_of_minor _ half_seven.ri half_seven.ci half_seven.mr half_seven.inv _ half_seven.calc_inverse
  intro i j
  rw [seven_entries, half_seven.calc_rows]
  unfold bit
  rw [half_seven.calc_minor]

namespace quotient_regular

private def ri : Fin 10 → Fin 32 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10]

private def ci : Fin 10 → Fin 32 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 9, 11]

private def fullRows : Fin 10 → ℕ :=
  ![441198689, 1078357442, 1555159727, 420181136, 80095392, 491410784, 25647576, 8870296, 428561257, 96742544]

private def mr : Fin 10 → ℕ :=
  ![609, 706, 943, 144, 672, 96, 728, 664, 361, 656]

private def inv : Fin 10 → ℕ :=
  ![553, 50, 262, 640, 752, 224, 192, 760, 393, 520]

set_option maxRecDepth 2048 in
private theorem calc_rows : ∀ i, regularRows 1 (ri i) = fullRows i := by decide +kernel

private theorem calc_minor : ∀ i j,
    (fullRows i).testBit (ci j).val = (mr i).testBit j.val := by decide +kernel

private theorem calc_inverse : ∀ i,
    combine inv (fun k => (mr i).testBit k.val) = 2 ^ i.val := by decide +kernel

end quotient_regular

/-- The ten-dimensional minor certifies the regular-three bound
on the quotient factor's actual generator matrices. -/
theorem quotient_regular_rank : 10 ≤ (factorMatrix 1 0 * factorMatrix 1 1 - 1).rank := by
  apply rank_ge_of_minor _ quotient_regular.ri quotient_regular.ci quotient_regular.mr quotient_regular.inv _ quotient_regular.calc_inverse
  intro i j
  rw [regular_entries, quotient_regular.calc_rows]
  unfold bit
  rw [quotient_regular.calc_minor]

namespace quotient_seven

private def ri : Fin 12 → Fin 32 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

private def ci : Fin 12 → Fin 32 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 17]

private def fullRows : Fin 12 → ℕ :=
  ![357797922, 78982075, 4218045706, 2582503823, 947820464, 2324253611, 3616503835, 1929573427, 1438195198, 3200297947, 1473025557, 1409047818]

private def mr : Fin 12 → ℕ :=
  ![2082, 1467, 2826, 399, 2992, 1451, 3099, 2611, 2046, 1499, 533, 1802]

private def inv : Fin 12 → ℕ :=
  ![211, 3244, 1153, 1049, 34, 1826, 1312, 4001, 846, 112, 907, 2959]

set_option maxRecDepth 2048 in
private theorem calc_rows : ∀ i, sevenRows 1 (ri i) = fullRows i := by decide +kernel

private theorem calc_minor : ∀ i j,
    (fullRows i).testBit (ci j).val = (mr i).testBit j.val := by decide +kernel

private theorem calc_inverse : ∀ i,
    combine inv (fun k => (mr i).testBit k.val) = 2 ^ i.val := by decide +kernel

end quotient_seven

/-- The twelve-dimensional minor certifies the seven-word bound
on the quotient factor's actual generator matrices. -/
theorem quotient_seven_rank : 12 ≤ (factorMatrix 1 0 - factorMatrix 1 1).rank := by
  apply rank_ge_of_minor _ quotient_seven.ri quotient_seven.ci quotient_seven.mr quotient_seven.inv _ quotient_seven.calc_inverse
  intro i j
  rw [seven_entries, quotient_seven.calc_rows]
  unfold bit
  rw [quotient_seven.calc_minor]

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CycleCertificates
