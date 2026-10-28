module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Words

/-!
# Small kernel-coordinate identities for the native construction

These identities keep multiplication and conjugation calculations in eleven
bits, using the already proved faithful coordinates of the actual max1 kernel.
In particular, no expanded native matrix word is reduced during group algebra.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis

abbrev kernelValue (m : ℕ) : M := maskValue matrixA_mul_self matrixB_pow_four m

theorem kernelValue_xor (m n : ℕ) :
    kernelValue (Nat.xor m n) = kernelValue m * kernelValue n :=
  congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four m n)

theorem kernelValue_zero : kernelValue 0 = 1 :=
  congrArg Subtype.val (maskValue_zero matrixA_mul_self matrixB_pow_four)

theorem kernelValue_square (m : ℕ) : kernelValue m * kernelValue m = 1 := by
  rw [← kernelValue_xor, show Nat.xor m m = 0 from Nat.xor_self m, kernelValue_zero]

theorem kernelValue_commute (m n : ℕ) : Commute (kernelValue m) (kernelValue n) := by
  change kernelValue m * kernelValue n = kernelValue n * kernelValue m
  rw [← kernelValue_xor, ← kernelValue_xor, show Nat.xor m n = Nat.xor n m from Nat.xor_comm m n]

theorem kernelValue_injective {m n : ℕ} (hm : m < 2048) (hn : n < 2048)
    (h : kernelValue m = kernelValue n) : m = n := by
  have hb := coordinates_injective matrixA_mul_self matrixB_pow_four
    (Subtype.ext h : maskValue matrixA_mul_self matrixB_pow_four m =
      maskValue matrixA_mul_self matrixB_pow_four n)
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 11
  · exact congrFun hb ⟨j, hj⟩
  · have hp : 2^11 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn hp)]

theorem projection_kernelValue (m : ℕ) : projection (kernelValue m) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [MathieuHallActors.projection_ker]
  exact (maskValue matrixA_mul_self matrixB_pow_four m).property

theorem kernelValue_mem_E (m : ℕ) : (kernelValue m : Model) ∈ E :=
  Subgroup.mem_map.mpr ⟨kernelValue m,
    (maskValue matrixA_mul_self matrixB_pow_four m).property, rfl⟩

end Janko4.LocalStructure.LinearFive
