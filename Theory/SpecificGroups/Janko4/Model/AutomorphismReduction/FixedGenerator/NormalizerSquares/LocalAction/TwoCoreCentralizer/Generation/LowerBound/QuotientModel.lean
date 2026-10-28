module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.Source

/-!
# Explicit matrices for the max2 quotient lower bound

These are the two 12-dimensional matrices obtained from the original ATLAS
outputs acting on the row quotient ker(t - 1) / im(t - 1). Their entries,
inverses, and seed relation are checked here. The comparison with the
112-dimensional source subgroup and the order lower bound of their generated
subgroup are separate obligations; neither follows merely from these entries.

Bit j of each row is column j, beginning at zero. Matrix multiplication is
ordinary multiplication, so row coordinates act on the right. The witness is
`LowerBound/source/canonical_quotient.json`, copied from the retained parent
`Scratch/J4Max2Generation/`.
Source attribution: `TwoCoreCentralizer/source/J4G1-max2W1` and its README;
GLS3, Table 5.3i, printed p.270, motivates the required lower bound.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
namespace LowerBound

/-- The matrix algebra containing the candidate quotient action. -/
abbrev QuotientMatrix := Matrix (Fin 12) (Fin 12) (ZMod 2)

/-- Decode packed rows with the same right-row convention as the source witness. -/
def quotientDecode (rows : Vector ℕ 12) : QuotientMatrix :=
  fun i j => if (rows.get i).testBit j.val then 1 else 0

def matrixX : QuotientMatrix := quotientDecode #v[2533, 3688, 2585, 58, 3283, 649, 4075, 1447, 616, 3160, 2130, 2384]

def matrixY : QuotientMatrix := quotientDecode #v[895, 124, 359, 4005, 2616, 2695, 1446, 24, 2224, 645, 4013, 2327]

def matrixYInv : QuotientMatrix := quotientDecode #v[749, 3035, 1525, 1032, 1160, 2542, 3225, 1437, 2480, 133, 2989, 2555]

private def xyMatrix : QuotientMatrix := quotientDecode #v[3206, 1211, 3440, 3942, 2623, 3655, 3856, 4070, 513, 1665, 1781, 3641]

private def xyxMatrix : QuotientMatrix := quotientDecode #v[212, 1048, 731, 1569, 1788, 3877, 993, 902, 1469, 2120, 992, 2783]

private def xyxyMatrix : QuotientMatrix := quotientDecode #v[3809, 2608, 421, 1232, 1771, 1040, 1651, 2870, 2567, 788, 1292, 2517]

private def wordMatrix : QuotientMatrix := quotientDecode #v[2169, 2861, 55, 43, 3767, 1429, 2866, 646, 2550, 362, 2527, 3129]

private def word2 : QuotientMatrix := quotientDecode #v[1147, 2389, 2113, 1770, 3659, 1110, 1194, 2294, 3139, 3159, 388, 1686]

private def word3 : QuotientMatrix := quotientDecode #v[2736, 2052, 3954, 3986, 3265, 1856, 1482, 1461, 3456, 768, 2887, 3998]

private def word5 : QuotientMatrix := quotientDecode #v[2090, 3799, 228, 2286, 3893, 1338, 3620, 790, 935, 20, 1863, 1605]

private def word6 : QuotientMatrix := quotientDecode #v[682, 236, 3094, 2857, 3606, 13, 302, 3377, 3308, 3712, 2322, 3017]

theorem matrixX_mul_self : matrixX * matrixX = 1 := by decide +kernel
theorem matrixY_mul_inv : matrixY * matrixYInv = 1 := by decide +kernel
theorem matrixY_inv_mul : matrixYInv * matrixY = 1 := by decide +kernel

/-- First candidate quotient generator, with a checked inverse. -/
def quotientX : QuotientMatrixˣ where
  val := matrixX
  inv := matrixX
  val_inv := matrixX_mul_self
  inv_val := matrixX_mul_self

/-- Second candidate quotient generator, with a checked inverse. -/
def quotientY : QuotientMatrixˣ where
  val := matrixY
  inv := matrixYInv
  val_inv := matrixY_mul_inv
  inv_val := matrixY_inv_mul

@[simp] theorem coe_quotientX : (quotientX : QuotientMatrix) = matrixX := rfl
@[simp] theorem coe_quotientY : (quotientY : QuotientMatrix) = matrixY := rfl

/-- The literal generated matrix subgroup. No recognition or order is assumed. -/
def quotientSubgroup : Subgroup QuotientMatrixˣ :=
  Subgroup.closure {quotientX, quotientY}

theorem quotientX_mem : quotientX ∈ quotientSubgroup :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem quotientY_mem : quotientY ∈ quotientSubgroup :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem mul_xyMatrix : matrixX * matrixY = xyMatrix := by decide +kernel
private theorem mul_xyxMatrix : xyMatrix * matrixX = xyxMatrix := by decide +kernel
private theorem mul_xyxyMatrix : xyxMatrix * matrixY = xyxyMatrix := by decide +kernel
private theorem mul_wordMatrix : xyxyMatrix * matrixY = wordMatrix := by decide +kernel
private theorem mul_word2 : wordMatrix * wordMatrix = word2 := by decide +kernel
private theorem mul_word3 : word2 * wordMatrix = word3 := by decide +kernel
private theorem mul_word5 : word2 * word3 = word5 := by decide +kernel
private theorem mul_word6 : word3 * word3 = word6 := by decide +kernel
private theorem mul_word11 : word5 * word6 = 1 := by decide +kernel

/-- The seed is killed by these explicit quotient matrices. -/
theorem quotient_seed_eq_one :
    (quotientX * quotientY * quotientX * quotientY * quotientY) ^ 11 = 1 := by
  apply Units.ext
  change (matrixX * matrixY * matrixX * matrixY * matrixY) ^ 11 = 1
  rw [mul_xyMatrix, mul_xyxMatrix, mul_xyxyMatrix, mul_wordMatrix]
  have h2 : wordMatrix ^ 2 = word2 := by simpa only [pow_two] using mul_word2
  have h3 : wordMatrix ^ 3 = word3 := by
    rw [pow_succ, h2, mul_word3]
  have h5 : wordMatrix ^ 5 = word5 := by
    rw [show 5 = 2 + 3 from rfl, pow_add, h2, h3, mul_word5]
  have h6 : wordMatrix ^ 6 = word6 := by
    rw [show 6 = 3 + 3 from rfl, pow_add, h3, mul_word6]
  rw [show 11 = 5 + 6 from rfl, pow_add, h5, h6, mul_word11]

/-- Correct generator images suffice to kill the original subgroup seed. -/
theorem map_sourceSeed_eq_one (f : sourceSubgroup →* QuotientMatrixˣ)
    (hx : f sourceX = quotientX) (hy : f sourceY = quotientY) :
    f sourceSeed = 1 := by
  simpa only [sourceSeed, map_pow, map_mul, hx, hy] using quotient_seed_eq_one

/-- Correct generator images put the whole candidate quotient subgroup in the range. -/
theorem quotientSubgroup_le_range (f : sourceSubgroup →* QuotientMatrixˣ)
    (hx : f sourceX = quotientX) (hy : f sourceY = quotientY) :
    quotientSubgroup ≤ f.range := by
  apply (Subgroup.closure_le _).mpr
  intro z hz
  rcases hz with rfl | rfl
  · exact ⟨sourceX, hx⟩
  · exact ⟨sourceY, hy⟩

end LowerBound
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
