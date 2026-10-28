module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorSpace

/-!
# Packed arithmetic for exterior-space certificates

A natural number stores successive 112-bit matrix rows. Row products are XORs
of selected rows. The lemmas below interpret these computations as ordinary
binary matrix multiplication and addition, so only kernel reduction is needed
for the later finite certificates. Matrix provenance: Janko4/Model/Data.lean;
exterior-space construction: KernelEquations/source/README.md.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.ExteriorInvariance
open GeneratorCertificates

def flatMatrix (x : ℕ) : BinaryMatrix := fun i j => bit x (112 * i.val + j.val)
def flatRow (x i : ℕ) : ℕ := (x >>> (112 * i)) % 2^112

theorem flatRow_bit (x : ℕ) (i j : Fin 112) :
    bit (flatRow x i.val) j.val = flatMatrix x i j := by
  simp only [bit, flatRow, Nat.testBit_mod_two_pow, j.isLt, decide_true,
    Bool.true_and, Nat.testBit_shiftRight, flatMatrix]

def flatMulRow (x y : ℕ) : ℕ :=
  xorList (List.ofFn (fun k : Fin 112 => if x.testBit k.val then flatRow y k.val else 0))

theorem flatMulRow_bit (x y : ℕ) (i j : Fin 112) :
    bit (flatMulRow (flatRow x i.val) y) j.val = (flatMatrix x * flatMatrix y) i j := by
  rw [flatMulRow, bit_xorList, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← flatRow_bit x i k, ← flatRow_bit y k j]
  cases h : (flatRow x i.val).testBit k.val <;> simp [h, bit]

theorem flatMatrix_mul (x y z : ℕ)
    (h : ∀ i : Fin 112, flatMulRow (flatRow x i.val) y = flatRow z i.val) :
    flatMatrix x * flatMatrix y = flatMatrix z := by
  ext i j
  rw [← flatMulRow_bit, h, flatRow_bit]

theorem flatMatrix_zero : flatMatrix 0 = 0 := by
  ext i j
  simp [flatMatrix, bit]

theorem flatMatrix_xor (x y : ℕ) :
    flatMatrix (x ^^^ y) = flatMatrix x + flatMatrix y := by
  ext i j
  exact bit_xor _ _ _

theorem flatMatrix_xorList_mem (xs : List ℕ)
    (h : ∀ x ∈ xs, flatMatrix x ∈ exteriorFormSpace) :
    flatMatrix (xorList xs) ∈ exteriorFormSpace := by
  induction xs with
  | nil => simpa only [xorList, flatMatrix_zero] using exteriorFormSpace.zero_mem
  | cons x xs ih =>
    rw [xorList, flatMatrix_xor]
    exact exteriorFormSpace.add_mem (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.ExteriorInvariance
