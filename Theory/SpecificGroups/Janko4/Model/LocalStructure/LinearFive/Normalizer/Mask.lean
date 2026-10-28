module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Elementary

/-!
# Binary products in the native F

These mask identities apply to the actual ten native generators and will
transport the normalizer matrix certificates back to the literal subgroup.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality KernelCount
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localX localY

def fValue (m : ℕ) : Model := (binaryProduct generators (fun i => m.testBit i.val) : M)

theorem fValue_mem (m : ℕ) : fValue m ∈ F :=
  (mem_F_iff_binaryProduct _).mpr ⟨_, rfl⟩

theorem fValue_zero : fValue 0 = 1 := by
  simpa only [fValue, Nat.zero_testBit, Subgroup.coe_one] using
    congrArg (fun g : M => (g : Model)) (binaryProduct_zero generators)

theorem fValue_xor (m n : ℕ) : fValue (Nat.xor m n) = fValue m * fValue n := by
  change fValue (m ^^^ n) = _
  simpa only [fValue, Nat.testBit_xor, Subgroup.coe_mul] using
    (congrArg (fun g : M => (g : Model)) (binaryProduct_mul generators
      generators_square generators_commute (fun i => m.testBit i.val)
      (fun i => n.testBit i.val))).symm

theorem fValue_basis (i : Fin 10) : fValue (2^i.val) = (generators i : Model) := by
  unfold fValue
  congr 1
  simp only [Nat.testBit_two_pow]
  convert binaryProduct_single generators i using 2
  funext j
  simp only [Fin.ext_iff, eq_comm]

end Janko4.LocalStructure.LinearFive
