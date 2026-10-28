module
public import Theory.Representation.Mathieu.M22James.Uniqueness.Reduction
import Mathlib.Tactic.FinCases

/-!
# A finite rigidity certificate for the point-stabilizer extension

Two matrices S and T from the two-point stabilizer, together with the central
scalar J, have a four-dimensional binary commutant. A cyclic row basis makes
a commuting matrix determined by its first row. An annihilating polynomial
of rank eight restricts that row to the displayed four-dimensional space.
The involution relation and two entries of one braid relation then distinguish
the required matrix among the sixteen possible comparison matrices.

Every displayed identity is checked by the Lean kernel. The words defining
S, T and H in the actual triple cover, and their stabilizer membership, are
proved in `PointExtension.Words`. The ATLAS matrices and their attribution
are inherited from the LinearModel/source directory used by `Reduction`.
This is the finite extension calculation for James (1973), Lemma 8.3, as
used in Aschbacher–Smith H.12.1(1), printed pp.393–394.
-/

open scoped Matrix
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointExtension
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

@[expose] public def matrixS : Matrix12 := fromRows ![716, 3721, 31, 2666, 948, 191, 2048, 938, 8, 331, 953, 3095]

@[expose] public def matrixT : Matrix12 := fromRows ![606, 547, 1282, 3521, 983, 690, 1512, 1561, 2550, 2065, 825, 1109]

@[expose] public def matrixH : Matrix12 := fromRows ![3453, 2048, 2691, 3307, 16, 3654, 64, 922, 256, 1761, 1024, 2]

private def wordss : Matrix12 := fromRows ![148, 1513, 1412, 256, 509, 1681, 3095, 1717, 2666, 3623, 2372, 64]

private def wordst : Matrix12 := fromRows ![803, 1787, 2921, 1276, 921, 4034, 1109, 2734, 3521, 418, 2308, 452]

private def wordsj : Matrix12 := fromRows ![357, 328, 1188, 1327, 277, 3477, 1762, 77, 1094, 3392, 3147, 1902]

private def wordts : Matrix12 := fromRows ![3587, 3505, 3384, 1728, 1287, 3939, 718, 2528, 2600, 3439, 2798, 2782]

private def wordtt : Matrix12 := fromRows ![1230, 2782, 2284, 3893, 1214, 3406, 1613, 1888, 2070, 1500, 3869, 602]

private def wordtj : Matrix12 := fromRows ![152, 3278, 813, 496, 3099, 4018, 1950, 298, 330, 3481, 1100, 2120]

private def wordsst : Matrix12 := fromRows ![204, 1043, 2516, 2550, 511, 3256, 452, 2824, 1276, 2224, 3401, 1512]

private def wordssj : Matrix12 := fromRows ![2660, 610, 179, 1342, 367, 3435, 1902, 185, 1327, 1958, 385, 3769]

private def wordttt : Matrix12 := fromRows ![2600, 1666, 3541, 178, 3749, 402, 1117, 1412, 163, 554, 4033, 460]

private theorem stepss : matrixS * matrixS = wordss := by decide +kernel

private theorem stepst : matrixS * matrixT = wordst := by decide +kernel

private theorem stepsj : matrixS * matrixJ = wordsj := by decide +kernel

private theorem stepts : matrixT * matrixS = wordts := by decide +kernel

private theorem steptt : matrixT * matrixT = wordtt := by decide +kernel

private theorem steptj : matrixT * matrixJ = wordtj := by decide +kernel

private theorem stepsst : wordss * matrixT = wordsst := by decide +kernel

private theorem stepssj : wordss * matrixJ = wordssj := by decide +kernel

private theorem stepttt : wordtt * matrixT = wordttt := by decide +kernel

private def cyclicWords : Fin 12 → Matrix12 :=
  ![(1 : Matrix12), matrixS, matrixT, matrixJ, wordss, wordst, wordsj, wordts, wordtt, wordtj, wordsst, wordssj]

private def cyclicRows : Matrix12 := fromRows ![1, 716, 606, 1532, 148, 803, 357, 3587, 1230, 152, 204, 2660]

private def cyclicRowsInv : Matrix12 := fromRows ![1, 1865, 1887, 1359, 1323, 3754, 1140, 612, 3520, 1026, 585, 387]

private theorem cyclicRows_spec : ∀ i, cyclicRows i = cyclicWords i 0 := by
  have h : @Eq Matrix12 cyclicRows (fun i j => cyclicWords i 0 j) := by
    exact @of_decide_eq_true _ (Matrix.decidableEq _ _) rfl
  exact fun i => congrFun h i

private theorem cyclicRows_left_inv : cyclicRowsInv * cyclicRows = 1 := by decide +kernel

private theorem commute_cyclicWords {M : Matrix12}
    (hS : Commute M matrixS) (hT : Commute M matrixT) (hJ : Commute M matrixJ)
    (i : Fin 12) : Commute M (cyclicWords i) := by
  have hss : Commute M wordss := by
    rw [← stepss]
    exact hS.mul_right hS
  have hst : Commute M wordst := by
    rw [← stepst]
    exact hS.mul_right hT
  have hsj : Commute M wordsj := by
    rw [← stepsj]
    exact hS.mul_right hJ
  have hts : Commute M wordts := by
    rw [← stepts]
    exact hT.mul_right hS
  have htt : Commute M wordtt := by
    rw [← steptt]
    exact hT.mul_right hT
  have htj : Commute M wordtj := by
    rw [← steptj]
    exact hT.mul_right hJ
  have hsst : Commute M wordsst := by
    rw [← stepsst]
    exact hss.mul_right hT
  have hssj : Commute M wordssj := by
    rw [← stepssj]
    exact hss.mul_right hJ
  fin_cases i
  · exact Commute.one_right M
  · exact hS
  · exact hT
  · exact hJ
  · exact hss
  · exact hst
  · exact hsj
  · exact hts
  · exact htt
  · exact htj
  · exact hsst
  · exact hssj

private theorem commuting_ext_firstRow {M N : Matrix12}
    (hMS : Commute M matrixS) (hMT : Commute M matrixT) (hMJ : Commute M matrixJ)
    (hNS : Commute N matrixS) (hNT : Commute N matrixT) (hNJ : Commute N matrixJ)
    (hrow : M 0 = N 0) : M = N := by
  have h : cyclicRows * M = cyclicRows * N := by
    funext i
    rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul, cyclicRows_spec]
    change (cyclicWords i * M) 0 = (cyclicWords i * N) 0
    rw [← (commute_cyclicWords hMS hMT hMJ i).eq,
      ← (commute_cyclicWords hNS hNT hNJ i).eq,
      Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul, hrow]
  calc
    M = (cyclicRowsInv * cyclicRows) * M := by rw [cyclicRows_left_inv, one_mul]
    _ = (cyclicRowsInv * cyclicRows) * N := by rw [mul_assoc, h, ← mul_assoc]
    _ = N := by rw [cyclicRows_left_inv, one_mul]

private def basis0 : Matrix12 := fromRows ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private def basis1 : Matrix12 := fromRows ![1010, 187, 2794, 896, 2185, 310, 2231, 3593, 760, 2239, 166, 236]

private def basis2 : Matrix12 := fromRows ![1076, 371, 3372, 584, 3919, 310, 3953, 2511, 816, 2423, 1704, 1834]

private def basis3 : Matrix12 := fromRows ![456, 1550, 456, 1550, 456, 0, 456, 456, 1550, 1550, 1990, 456]

private theorem basis0_commute_S : Commute basis0 matrixS := by
  change basis0 * matrixS = matrixS * basis0
  decide +kernel

private theorem basis1_commute_S : Commute basis1 matrixS := by
  change basis1 * matrixS = matrixS * basis1
  decide +kernel

private theorem basis2_commute_S : Commute basis2 matrixS := by
  change basis2 * matrixS = matrixS * basis2
  decide +kernel

private theorem basis3_commute_S : Commute basis3 matrixS := by
  change basis3 * matrixS = matrixS * basis3
  decide +kernel

private theorem basis0_commute_T : Commute basis0 matrixT := by
  change basis0 * matrixT = matrixT * basis0
  decide +kernel

private theorem basis1_commute_T : Commute basis1 matrixT := by
  change basis1 * matrixT = matrixT * basis1
  decide +kernel

private theorem basis2_commute_T : Commute basis2 matrixT := by
  change basis2 * matrixT = matrixT * basis2
  decide +kernel

private theorem basis3_commute_T : Commute basis3 matrixT := by
  change basis3 * matrixT = matrixT * basis3
  decide +kernel

private theorem basis0_commute_J : Commute basis0 matrixJ := by
  change basis0 * matrixJ = matrixJ * basis0
  decide +kernel

private theorem basis1_commute_J : Commute basis1 matrixJ := by
  change basis1 * matrixJ = matrixJ * basis1
  decide +kernel

private theorem basis2_commute_J : Commute basis2 matrixJ := by
  change basis2 * matrixJ = matrixJ * basis2
  decide +kernel

private theorem basis3_commute_J : Commute basis3 matrixJ := by
  change basis3 * matrixJ = matrixJ * basis3
  decide +kernel

private def annihilator : Matrix12 := fromRows ![0, 2477, 3408, 408, 885, 3862, 566, 997, 75, 1110, 307, 42]

private def rightFactor : Matrix12 := fromRows ![2880, 2352, 3840, 336, 1552, 96, 544, 1664, 0, 0, 0, 0]

private def complement : Matrix12 := fromRows ![0, 1008, 1072, 448, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem annihilator_polynomial :
    wordttt + matrixT + wordst + wordsj + wordtj + wordsst + wordssj = annihilator := by decide +kernel

private theorem annihilator_firstRow : annihilator 0 = 0 := by decide +kernel

private theorem annihilator_mul : annihilator * rightFactor = complement := by decide +kernel

private theorem complement_projection :
    complement + (Matrix.vecMulVec (Pi.single 0 1) (basis0 0) +
      Matrix.vecMulVec (Pi.single 1 1) (basis1 0) +
      Matrix.vecMulVec (Pi.single 2 1) (basis2 0) +
      Matrix.vecMulVec (Pi.single 3 1) (basis3 0)) = 1 := by decide +kernel

private theorem commute_annihilator {M : Matrix12}
    (hS : Commute M matrixS) (hT : Commute M matrixT) (hJ : Commute M matrixJ) :
    Commute M annihilator := by
  rw [← annihilator_polynomial]
  have ht : Commute M wordttt := by
    rw [← stepttt, ← steptt]
    exact (hT.mul_right hT).mul_right hT
  exact (((((ht.add_right (commute_cyclicWords hS hT hJ 2)).add_right
    (commute_cyclicWords hS hT hJ 5)).add_right
    (commute_cyclicWords hS hT hJ 6)).add_right
    (commute_cyclicWords hS hT hJ 9)).add_right
    (commute_cyclicWords hS hT hJ 10)).add_right
    (commute_cyclicWords hS hT hJ 11)

private theorem firstRow_form {M : Matrix12}
    (hS : Commute M matrixS) (hT : Commute M matrixT) (hJ : Commute M matrixJ) :
    M 0 = M 0 0 • basis0 0 + M 0 1 • basis1 0 + M 0 2 • basis2 0 +
      M 0 3 • basis3 0 := by
  have hzero : Matrix.vecMul (M 0) annihilator = 0 := by
    change (M * annihilator) 0 = 0
    rw [(commute_annihilator hS hT hJ).eq, Matrix.mul_apply_eq_vecMul,
      annihilator_firstRow, Matrix.zero_vecMul]
  have hp : Matrix.vecMul (M 0) complement = 0 := by
    rw [← annihilator_mul, ← Matrix.vecMul_vecMul, hzero, Matrix.zero_vecMul]
  calc
    M 0 = Matrix.vecMul (M 0) (1 : Matrix12) := (Matrix.vecMul_one _).symm
    _ = _ := by
      conv_lhs => rw [← complement_projection]
      simp only [Matrix.vecMul_add, hp, zero_add,
        Matrix.vecMul_vecMulVec, dotProduct_single_one]

private def candidate (a b c d : ZMod 2) : Matrix12 :=
  a • basis0 + b • basis1 + c • basis2 + d • basis3

private theorem commuting_matrix_form {M : Matrix12}
    (hS : Commute M matrixS) (hT : Commute M matrixT) (hJ : Commute M matrixJ) :
    M = candidate (M 0 0) (M 0 1) (M 0 2) (M 0 3) := by
  apply commuting_ext_firstRow hS hT hJ
  · exact (((basis0_commute_S.smul_left _).add_left
      (basis1_commute_S.smul_left _)).add_left
      (basis2_commute_S.smul_left _)).add_left (basis3_commute_S.smul_left _)
  · exact (((basis0_commute_T.smul_left _).add_left
      (basis1_commute_T.smul_left _)).add_left
      (basis2_commute_T.smul_left _)).add_left (basis3_commute_T.smul_left _)
  · exact (((basis0_commute_J.smul_left _).add_left
      (basis1_commute_J.smul_left _)).add_left
      (basis2_commute_J.smul_left _)).add_left (basis3_commute_J.smul_left _)
  · exact firstRow_form hS hT hJ

private theorem finite_rigidity : ∀ a b c d : ZMod 2,
    let X := matrixB * candidate a b c d
    (X * matrixH * X) 11 11 = (matrixH * X * matrixH) 11 11 →
    (X * matrixH * X) 11 9 = (matrixH * X * matrixH) 11 9 →
    (X * X) 11 11 = 1 → X = matrixB := by
  decide +kernel

/-- The two-point commutant, the involution relation and one braid relation
force the missing generator to be the specified matrix. -/
public theorem matrix_extension_rigidity {X : Matrix12}
    (hS : Commute (matrixB * X) matrixS)
    (hT : Commute (matrixB * X) matrixT)
    (hJ : Commute (matrixB * X) matrixJ)
    (h2 : X * X = 1) (hbraid : X * matrixH * X = matrixH * X * matrixH) :
    X = matrixB := by
  have hB : matrixB * matrixB = 1 := by decide +kernel
  have hf := commuting_matrix_form hS hT hJ
  have hx : X = matrixB * candidate ((matrixB * X) 0 0)
      ((matrixB * X) 0 1) ((matrixB * X) 0 2) ((matrixB * X) 0 3) := by
    rw [← hf, ← mul_assoc, hB, one_mul]
  rw [hx] at h2 hbraid ⊢
  apply finite_rigidity
  · exact congrArg (fun M : Matrix12 => M 11 11) hbraid
  · exact congrArg (fun M : Matrix12 => M 11 9) hbraid
  · exact congrArg (fun M : Matrix12 => M 11 11) h2

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointExtension
