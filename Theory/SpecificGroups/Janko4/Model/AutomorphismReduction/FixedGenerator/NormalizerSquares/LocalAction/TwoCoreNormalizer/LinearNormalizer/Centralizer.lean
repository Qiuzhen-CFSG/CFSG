module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.Core
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.FinCases

/-!
# The matrix centralizer of the commutator subgroup

The two even words A = CD and B = D² have a two-dimensional commutant.
A cyclic row basis makes a commuting matrix determined by its first row;
an annihilating polynomial of rank ten restricts that row to a plane.
The three nonzero commuting matrices are powers of an explicit word in A,B.
Thus the ambient unit centralizer of the actual commutator subgroup lies
inside the literal generated group. No recognition or order calculation
is needed for this bound.

All packed-matrix identities below are checked by the Lean kernel. The
input matrices and ATLAS attribution are in `../LinearModel/source/`.
-/

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- A nontrivial element of the four-element commuting matrix algebra. -/
@[expose] public def matrixJ : Matrix12 := fromRows ![1532, 1917, 3300, 1094, 3719, 310, 3769, 2055, 1342, 3961, 366, 1762]

public theorem matrixJ_commute_A : Commute matrixJ matrixA := by
  change matrixJ * matrixA = matrixA * matrixJ
  decide +kernel
public theorem matrixJ_commute_B : Commute matrixJ matrixB := by
  change matrixJ * matrixB = matrixB * matrixJ
  decide +kernel

private def wordAA : Matrix12 := fromRows ![128, 28, 412, 2976, 1639, 4, 400, 2891, 2823, 1513, 1412, 1499]

private theorem stepAA : matrixA * matrixA = wordAA := by decide +kernel

private theorem commuteAA {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M wordAA := by
  have _ := hB
  rw [← stepAA]
  exact (hA).mul_right hA

private def wordBA : Matrix12 := fromRows ![256, 4, 400, 128, 8, 1513, 1412, 3659, 1559, 1681, 3095, 31]

private theorem stepBA : matrixB * matrixA = wordBA := by decide +kernel

private theorem commuteBA {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M wordBA := by
  rw [← stepBA]
  exact (hB).mul_right hA

private def wordAAA : Matrix12 := fromRows ![2976, 412, 3163, 2891, 2823, 28, 3271, 122, 249, 1362, 1499, 1108]

private theorem stepAAA : wordAA * matrixA = wordAAA := by decide +kernel

private theorem commuteAAA {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M wordAAA := by
  rw [← stepAAA]
  exact (commuteAA hA hB).mul_right hA

private def wordAAB : Matrix12 := fromRows ![938, 22, 2518, 202, 3356, 31, 2497, 2160, 103, 3721, 1412, 3456]

private theorem stepAAB : wordAA * matrixB = wordAAB := by decide +kernel

private theorem commuteAAB {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M wordAAB := by
  rw [← stepAAB]
  exact (commuteAA hA hB).mul_right hB

private def wordBAA : Matrix12 := fromRows ![1639, 28, 3271, 2976, 128, 1362, 1499, 3613, 2586, 418, 3220, 400]

private theorem stepBAA : wordBA * matrixA = wordBAA := by decide +kernel

private theorem commuteBAA {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M wordBAA := by
  rw [← stepBAA]
  exact (commuteBA hA hB).mul_right hA

private def wordBAB : Matrix12 := fromRows ![2666, 31, 2497, 938, 8, 3721, 1412, 3649, 1559, 1440, 3095, 4]

private theorem stepBAB : wordBA * matrixB = wordBAB := by decide +kernel

private theorem commuteBAB {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M wordBAB := by
  rw [← stepBAB]
  exact (commuteBA hA hB).mul_right hB

private def wordAAAA : Matrix12 := fromRows ![2891, 3163, 3095, 122, 249, 412, 1579, 409, 2613, 3964, 1108, 2307]

private theorem stepAAAA : wordAAA * matrixA = wordAAAA := by decide +kernel

private theorem commuteAAAA {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M wordAAAA := by
  rw [← stepAAAA]
  exact (commuteAAA hA hB).mul_right hA

private def wordAABA : Matrix12 := fromRows ![3659, 280, 2372, 2875, 2687, 400, 2132, 1177, 13, 1446, 1499, 67]

private theorem stepAABA : wordAAB * matrixA = wordAABA := by decide +kernel

private theorem commuteAABA {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M wordAABA := by
  rw [← stepAABA]
  exact (commuteAAB hA hB).mul_right hA

private def wordBABA : Matrix12 := fromRows ![1559, 400, 2132, 3659, 128, 1446, 1499, 3737, 2586, 1477, 3220, 28]

private theorem stepBABA : wordBAB * matrixA = wordBABA := by decide +kernel

private theorem commuteBABA {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M wordBABA := by
  rw [← stepBABA]
  exact (commuteBAB hA hB).mul_right hA

private def wordAAAAA : Matrix12 := fromRows ![122, 3095, 3220, 409, 2613, 3163, 2948, 3151, 1944, 2408, 2307, 1007]

private theorem stepAAAAA : wordAAAA * matrixA = wordAAAAA := by decide +kernel

private theorem commuteAAAAA {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M wordAAAAA := by
  rw [← stepAAAAA]
  exact (commuteAAAA hA hB).mul_right hA

private def cyclicWords : Fin 12 → Matrix12 :=
  ![(1 : Matrix12), matrixA, matrixB, wordAA, wordBA, wordAAA, wordAAB, wordBAA, wordBAB, wordAAAA, wordAABA, wordBABA]

private def cyclicRows : Matrix12 := fromRows ![1, 8, 16, 128, 256, 2976, 938, 1639, 2666, 2891, 3659, 1559]

private def cyclicRowsInv : Matrix12 := fromRows ![1, 2735, 3422, 2, 4, 785, 2965, 8, 16, 2532, 1552, 2765]

private theorem cyclicRows_spec : ∀ i, cyclicRows i = cyclicWords i 0 := by
  have h : @Eq Matrix12 cyclicRows (fun i j => cyclicWords i 0 j) := by
    exact @of_decide_eq_true _ (Matrix.decidableEq _ _) rfl
  exact fun i => congrFun h i

private theorem cyclicRows_left_inv : cyclicRowsInv * cyclicRows = 1 := by decide +kernel

private theorem commute_cyclicWords {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) (i : Fin 12) : Commute M (cyclicWords i) := by
  fin_cases i
  · exact Commute.one_right M
  · exact hA
  · exact hB
  · exact commuteAA hA hB
  · exact commuteBA hA hB
  · exact commuteAAA hA hB
  · exact commuteAAB hA hB
  · exact commuteBAA hA hB
  · exact commuteBAB hA hB
  · exact commuteAAAA hA hB
  · exact commuteAABA hA hB
  · exact commuteBABA hA hB

private theorem commuting_ext_firstRow {M N : Matrix12}
    (hMA : Commute M matrixA) (hMB : Commute M matrixB)
    (hNA : Commute N matrixA) (hNB : Commute N matrixB) (hrow : M 0 = N 0) : M = N := by
  have h : cyclicRows * M = cyclicRows * N := by
    funext i
    rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul, cyclicRows_spec]
    change (cyclicWords i * M) 0 = (cyclicWords i * N) 0
    rw [← (commute_cyclicWords hMA hMB i).eq, ← (commute_cyclicWords hNA hNB i).eq,
      Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul, hrow]
  calc
    M = (cyclicRowsInv * cyclicRows) * M := by rw [cyclicRows_left_inv, one_mul]
    _ = (cyclicRowsInv * cyclicRows) * N := by rw [mul_assoc, h, ← mul_assoc]
    _ = N := by rw [cyclicRows_left_inv, one_mul]

private def annihilator : Matrix12 := fromRows ![0, 460, 3423, 264, 1981, 3829, 2232, 1485, 3385, 3823, 1363, 803]

private def rightFactor : Matrix12 := fromRows ![3090, 1328, 1890, 8, 1816, 0, 1706, 450, 0, 290, 3216, 1682]

private def complement : Matrix12 := fromRows ![0, 2, 1528, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem annihilator_polynomial :
    wordAAAAA + (1 : Matrix12) + matrixB + wordAA + wordAAA + wordAAAA = annihilator := by decide +kernel

private theorem annihilator_firstRow : annihilator 0 = 0 := by decide +kernel

private theorem annihilator_mul : annihilator * rightFactor = complement := by decide +kernel

private theorem complement_projection :
    complement + (Matrix.vecMulVec (Pi.single 0 1) ((1 : Matrix12) 0) +
      Matrix.vecMulVec (Pi.single 2 1) (matrixJ 0)) = 1 := by decide +kernel

private theorem commute_annihilator {M : Matrix12} (hA : Commute M matrixA)
    (hB : Commute M matrixB) : Commute M annihilator := by
  rw [← annihilator_polynomial]
  exact ((((((commuteAAAAA hA hB).add_right (Commute.one_right M)).add_right hB).add_right (commuteAA hA hB)).add_right (commuteAAA hA hB)).add_right (commuteAAAA hA hB))

private theorem firstRow_in_plane {M : Matrix12}
    (hA : Commute M matrixA) (hB : Commute M matrixB) :
    M 0 = M 0 0 • (1 : Matrix12) 0 + M 0 2 • matrixJ 0 := by
  have hzero : Matrix.vecMul (M 0) annihilator = 0 := by
    change (M * annihilator) 0 = 0
    rw [(commute_annihilator hA hB).eq, Matrix.mul_apply_eq_vecMul,
      annihilator_firstRow, Matrix.zero_vecMul]
  have hp : Matrix.vecMul (M 0) complement = 0 := by
    rw [← annihilator_mul, ← Matrix.vecMul_vecMul, hzero, Matrix.zero_vecMul]
  calc
    M 0 = Matrix.vecMul (M 0) (1 : Matrix12) := (Matrix.vecMul_one _).symm
    _ = M 0 0 • (1 : Matrix12) 0 + M 0 2 • matrixJ 0 := by
      conv_lhs => rw [← complement_projection]
      rw [Matrix.vecMul_add, hp, zero_add,
        Matrix.vecMul_add, Matrix.vecMul_vecMulVec, Matrix.vecMul_vecMulVec,
        dotProduct_single_one, dotProduct_single_one]

/-- The algebra commutant of the two even words is a plane over the binary field. -/
public theorem commuting_matrix_form {M : Matrix12}
    (hA : Commute M matrixA) (hB : Commute M matrixB) :
    M = M 0 0 • (1 : Matrix12) + M 0 2 • matrixJ := by
  apply commuting_ext_firstRow hA hB
  · exact ((Commute.one_left matrixA).smul_left _).add_left
      (matrixJ_commute_A.smul_left _)
  · exact ((Commute.one_left matrixB).smul_left _).add_left
      (matrixJ_commute_B.smul_left _)
  · exact firstRow_in_plane hA hB

/-- The four literal matrices commuting with the even words. -/
public theorem commuting_matrix_cases {M : Matrix12}
    (hA : Commute M matrixA) (hB : Commute M matrixB) :
    M = 0 ∨ M = 1 ∨ M = matrixJ ∨ M = 1 + matrixJ := by
  have hb : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide +kernel
  have h := commuting_matrix_form hA hB
  rcases hb (M 0 0) with h0 | h0 <;> rcases hb (M 0 2) with h2 | h2
  · exact Or.inl (by simpa only [h0, h2, zero_smul, add_zero] using h)
  · exact Or.inr (Or.inr (Or.inl (by simpa only [h0, h2, zero_smul, one_smul, zero_add] using h)))
  · exact Or.inr (Or.inl (by simpa only [h0, h2, zero_smul, one_smul, add_zero] using h))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [h0, h2, one_smul] using h)))

/-- The order-three scalar is an actual word in the original generators. -/
@[expose] public def scalarUnit : Matrix12ˣ := (coreA * coreA * coreB) ^ 4

public theorem scalarUnit_mem_derivedGroup : scalarUnit ∈ derivedGroup :=
  derivedGroup.pow_mem
    (derivedGroup.mul_mem (derivedGroup.mul_mem coreA_mem_derivedGroup coreA_mem_derivedGroup)
      coreB_mem_derivedGroup) 4

public theorem coe_scalarUnit : (scalarUnit : Matrix12) = 1 + matrixJ := by
  let squareWord : Matrix12 := fromRows ![1629, 1244, 2186, 365, 3171, 1980, 4092, 2370, 948, 3485, 1093, 19]
  have h2 : wordAAB * wordAAB = squareWord := by decide +kernel
  have h4 : squareWord * squareWord = 1 + matrixJ := by decide +kernel
  change ((coreA : Matrix12) * (coreA : Matrix12) * (coreB : Matrix12)) ^ 4 = _
  rw [coe_coreA, coe_coreB, stepAA, stepAAB,
    show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, h2, h4]

public theorem coe_scalarUnit_sq : ((scalarUnit ^ 2 : Matrix12ˣ) : Matrix12) = matrixJ := by
  change (scalarUnit : Matrix12) ^ 2 = matrixJ
  rw [coe_scalarUnit]
  decide +kernel

/-- The explicit scalar word has order dividing three. -/
public theorem scalarUnit_pow_three : scalarUnit ^ 3 = 1 := by
  apply Units.ext
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, Units.val_mul,
    coe_scalarUnit_sq, coe_scalarUnit]
  change matrixJ * (1 + matrixJ) = 1
  decide +kernel

public theorem scalarUnit_ne_one : scalarUnit ≠ 1 := by
  intro h
  have he : (scalarUnit : Matrix12) = 1 := congrArg Units.val h
  rw [coe_scalarUnit] at he
  have hn : (1 : Matrix12) + matrixJ ≠ 1 := by decide +kernel
  exact hn he

/-- The first original generator inverts the scalar word. -/
public theorem unitC_conj_scalarUnit :
    unitC * scalarUnit * unitC⁻¹ = scalarUnit ^ 2 := by
  apply Units.ext
  change matrixC * (scalarUnit : Matrix12) * matrixC = _
  rw [coe_scalarUnit, coe_scalarUnit_sq]
  decide +kernel

/-- The second original generator also inverts the scalar word. -/
public theorem unitD_conj_scalarUnit :
    unitD * scalarUnit * unitD⁻¹ = scalarUnit ^ 2 := by
  apply Units.ext
  change matrixD * (scalarUnit : Matrix12) * matrixDInv = _
  rw [coe_scalarUnit, coe_scalarUnit_sq]
  decide +kernel

/-- Every unit centralizing the genuine derived subgroup already belongs to the group. -/
public theorem centralizer_derivedGroup_le :
    Subgroup.centralizer (derivedGroup : Set Matrix12ˣ) ≤ actionGroup := by
  intro u hu
  have hA : Commute (u : Matrix12) matrixA := by
    change (u : Matrix12) * matrixA = matrixA * (u : Matrix12)
    have he : coreA * u = u * coreA := (Subgroup.mem_centralizer_iff.mp hu) _ coreA_mem_derivedGroup
    have hv := congrArg (fun v : Matrix12ˣ => (v : Matrix12)) he
    simpa only [Units.val_mul, coe_coreA] using hv.symm
  have hB : Commute (u : Matrix12) matrixB := by
    change (u : Matrix12) * matrixB = matrixB * (u : Matrix12)
    have he : coreB * u = u * coreB := (Subgroup.mem_centralizer_iff.mp hu) _ coreB_mem_derivedGroup
    have hv := congrArg (fun v : Matrix12ˣ => (v : Matrix12)) he
    simpa only [Units.val_mul, coe_coreB] using hv.symm
  rcases commuting_matrix_cases hA hB with h | h | h | h
  · exact False.elim (Units.ne_zero u h)
  · have hu1 : u = 1 := Units.ext h
    rw [hu1]
    exact actionGroup.one_mem
  · have huz : u = scalarUnit ^ 2 := Units.ext (h.trans coe_scalarUnit_sq.symm)
    rw [huz]
    exact actionGroup.pow_mem (derivedGroup_le_actionGroup scalarUnit_mem_derivedGroup) 2
  · have huz : u = scalarUnit := Units.ext (h.trans coe_scalarUnit.symm)
    rw [huz]
    exact derivedGroup_le_actionGroup scalarUnit_mem_derivedGroup

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
