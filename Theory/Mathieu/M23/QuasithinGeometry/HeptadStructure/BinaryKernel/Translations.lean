module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Explicit binary translations of the heptad complement

Four involutory degree-23 permutations fix the distinguished heptad pointwise.
Their reindexing tables certify preservation of all 253 Witt heptads, hence
membership in the actual M23. Their sixteen products act as translations on
four binary coordinates on the complement. All finite identities are checked
by the Lean kernel, using the existing block data; no group-order argument or
alternating complement is needed.

The tables were obtained by matching incidence with heptads through a triple
of the distinguished heptad and a complementary point. Source: Aschbacher,
*Sporadic Groups*, Chapter 6, Lemma 19.1 and its M23 specialization;
Aschbacher--Smith, §5.2, printed p.655.
-/

public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000

private def generatorTable : Fin 4 → Fin 23 → Fin 23 :=
  ![![6, 1, 2, 3, 4, 5, 0, 8, 7, 10, 9, 11, 18, 15, 16, 13, 14, 17, 12, 22, 21, 20, 19],
    ![7, 1, 2, 3, 4, 5, 8, 0, 6, 18, 12, 11, 10, 19, 21, 22, 20, 17, 9, 13, 16, 14, 15],
    ![9, 1, 2, 3, 4, 5, 10, 18, 12, 0, 6, 11, 8, 20, 22, 21, 19, 17, 7, 16, 13, 15, 14],
    ![13, 1, 2, 3, 4, 5, 15, 19, 22, 20, 21, 11, 14, 0, 12, 6, 18, 17, 16, 7, 9, 10, 8]]

private theorem generatorTable_involutive : ∀ i : Fin 4,
    Function.Involutive (generatorTable i) := by
  change ∀ i x, generatorTable i (generatorTable i x) = x
  decide +kernel

private def generator (i : Fin 4) : Equiv.Perm (Fin 23) where
  toFun := generatorTable i
  invFun := generatorTable i
  left_inv := generatorTable_involutive i
  right_inv := generatorTable_involutive i

private def blockIndex : Fin 4 → Fin 253 → Fin 253 :=
  ![![0, 4, 3, 2, 1, 8, 7, 6, 5, 9, 10, 11, 12, 19, 20, 18, 17, 16, 15, 13, 14, 22, 21, 24, 23, 28, 27, 26, 25, 32, 30, 31, 29, 33, 35, 34, 36, 40, 39, 38, 37, 44, 42, 43, 41, 45, 46, 48, 47, 56, 55, 53, 54, 51, 52, 50, 49, 68, 69, 70, 67, 66, 63, 62, 65, 64, 61, 60, 57, 58, 59, 74, 75, 76, 71, 72, 73, 78, 77, 80, 79, 84, 83, 82, 81, 88, 86, 87, 85, 89, 90, 92, 91, 96, 95, 94, 93, 100, 98, 99, 97, 101, 103, 102, 104, 112, 111, 109, 110, 107, 108, 106, 105, 125, 126, 122, 123, 124, 119, 118, 121, 120, 115, 116, 117, 113, 114, 130, 132, 131, 127, 129, 128, 133, 134, 135, 136, 143, 144, 142, 141, 140, 139, 137, 138, 148, 147, 146, 145, 151, 152, 149, 150, 160, 155, 154, 171, 172, 170, 169, 153, 165, 166, 167, 168, 161, 162, 163, 164, 159, 158, 156, 157, 176, 175, 174, 173, 179, 180, 177, 178, 188, 183, 182, 199, 200, 197, 198, 181, 193, 194, 196, 195, 189, 190, 192, 191, 186, 187, 184, 185, 214, 213, 212, 211, 205, 207, 206, 208, 210, 209, 204, 203, 202, 201, 216, 215, 217, 218, 220, 219, 233, 234, 226, 225, 224, 223, 247, 248, 249, 250, 252, 251, 221, 222, 245, 244, 246, 241, 242, 243, 238, 239, 240, 236, 235, 237, 227, 228, 229, 230, 232, 231],
    ![0, 3, 4, 1, 2, 7, 8, 5, 6, 9, 10, 11, 12, 17, 18, 20, 19, 13, 14, 16, 15, 22, 21, 24, 23, 27, 28, 25, 26, 29, 31, 30, 32, 36, 34, 35, 33, 39, 40, 37, 38, 41, 43, 42, 44, 46, 45, 47, 48, 53, 54, 56, 55, 49, 50, 52, 51, 70, 69, 68, 61, 60, 65, 64, 63, 62, 67, 66, 59, 58, 57, 74, 73, 72, 71, 76, 75, 77, 78, 79, 80, 83, 84, 81, 82, 88, 87, 86, 85, 90, 89, 92, 91, 95, 96, 93, 94, 100, 99, 98, 97, 104, 103, 102, 101, 110, 109, 111, 112, 106, 105, 107, 108, 126, 125, 117, 116, 115, 120, 121, 118, 119, 124, 123, 122, 114, 113, 127, 131, 132, 130, 128, 129, 134, 133, 136, 135, 141, 142, 144, 143, 137, 138, 140, 139, 148, 146, 147, 145, 151, 150, 149, 152, 155, 160, 153, 166, 165, 167, 168, 154, 172, 171, 170, 169, 157, 156, 158, 159, 164, 163, 162, 161, 176, 174, 175, 173, 177, 180, 179, 178, 183, 188, 181, 195, 196, 194, 193, 182, 198, 197, 200, 199, 187, 186, 184, 185, 190, 189, 192, 191, 213, 214, 204, 203, 208, 209, 210, 205, 206, 207, 212, 211, 201, 202, 220, 219, 218, 217, 216, 215, 225, 226, 234, 233, 221, 222, 241, 246, 245, 244, 243, 242, 224, 223, 249, 250, 248, 247, 251, 252, 227, 232, 231, 230, 229, 228, 238, 237, 235, 236, 239, 240],
    ![0, 4, 3, 2, 1, 5, 6, 7, 8, 10, 9, 12, 11, 16, 18, 20, 13, 19, 14, 17, 15, 24, 23, 22, 21, 26, 25, 28, 27, 29, 33, 36, 32, 30, 34, 35, 31, 39, 40, 37, 38, 44, 45, 46, 41, 42, 43, 48, 47, 56, 50, 53, 52, 51, 54, 55, 49, 63, 74, 65, 76, 75, 68, 57, 70, 59, 72, 73, 62, 71, 64, 69, 66, 67, 58, 61, 60, 80, 79, 78, 77, 83, 84, 81, 82, 85, 89, 90, 88, 86, 87, 91, 92, 94, 93, 96, 95, 100, 101, 104, 97, 98, 103, 102, 99, 112, 106, 107, 110, 109, 108, 111, 105, 132, 131, 119, 130, 121, 122, 115, 124, 117, 118, 127, 120, 128, 129, 123, 125, 126, 116, 114, 113, 133, 134, 135, 136, 140, 142, 144, 137, 143, 138, 141, 139, 151, 152, 150, 149, 148, 147, 145, 146, 172, 165, 161, 171, 160, 159, 158, 157, 155, 166, 164, 163, 154, 162, 168, 167, 170, 169, 156, 153, 180, 179, 177, 178, 175, 176, 174, 173, 187, 189, 193, 200, 199, 186, 181, 198, 182, 190, 195, 196, 183, 194, 191, 192, 197, 188, 185, 184, 212, 204, 214, 202, 208, 215, 216, 205, 220, 219, 213, 201, 211, 203, 206, 207, 218, 217, 210, 209, 238, 246, 248, 227, 247, 228, 224, 226, 244, 245, 239, 240, 241, 237, 250, 249, 234, 221, 231, 232, 233, 252, 251, 229, 230, 222, 225, 223, 236, 235, 243, 242],
    ![0, 2, 1, 4, 3, 8, 7, 6, 5, 11, 12, 9, 10, 13, 18, 20, 16, 17, 14, 19, 15, 24, 23, 22, 21, 27, 28, 25, 26, 35, 30, 31, 34, 33, 32, 29, 36, 37, 38, 39, 40, 48, 43, 42, 47, 46, 45, 44, 41, 56, 52, 53, 50, 51, 55, 54, 49, 61, 71, 67, 70, 57, 72, 75, 76, 73, 68, 59, 66, 74, 60, 58, 62, 65, 69, 63, 64, 77, 78, 79, 80, 84, 83, 82, 81, 92, 89, 90, 91, 86, 87, 88, 85, 94, 93, 96, 95, 103, 104, 101, 102, 99, 100, 97, 98, 105, 109, 111, 108, 106, 110, 107, 112, 119, 120, 132, 123, 129, 125, 113, 114, 126, 128, 116, 131, 118, 121, 130, 122, 117, 127, 124, 115, 135, 136, 133, 134, 143, 139, 138, 141, 140, 144, 137, 142, 145, 152, 150, 148, 149, 147, 151, 146, 170, 167, 163, 166, 159, 160, 157, 158, 164, 171, 155, 161, 168, 156, 154, 165, 172, 153, 162, 169, 176, 177, 179, 173, 174, 180, 175, 178, 192, 184, 199, 182, 193, 186, 196, 195, 200, 190, 198, 181, 185, 194, 188, 187, 197, 191, 183, 189, 220, 216, 210, 207, 217, 211, 204, 218, 212, 203, 206, 209, 215, 219, 213, 202, 205, 208, 214, 201, 245, 232, 239, 249, 229, 242, 236, 252, 225, 238, 248, 222, 235, 251, 233, 227, 243, 230, 223, 246, 250, 226, 237, 247, 221, 240, 244, 231, 224, 241, 234, 228]]

private theorem blockIndex_involutive : ∀ i : Fin 4,
    Function.Involutive (blockIndex i) := by
  change ∀ i x, blockIndex i (blockIndex i x) = x
  decide +kernel

private theorem generator_bits : ∀ k : Fin 4, ∀ i : Fin 253, ∀ x : Fin 23,
    (m23BlockMask i).testBit ((generator k).symm x).val =
      (m23BlockMask (blockIndex k i)).testBit x.val := by decide +kernel

private theorem generator_mem (k : Fin 4) : generator k ∈ M23 := by
  rw [mem_M23_iff]
  have h := m23Blocks_smul_of_reindex (generator k) (blockIndex k)
    (blockIndex_involutive k).surjective
    (fun i => m23Perm_smul_blockAt_of_bits _ _ _ (generator_bits k i))
  simpa only [Finset.coe_smul_finset] using congrArg
    (fun s : Finset (Finset (Fin 23)) => (s : Set (Finset (Fin 23)))) h

/-- The four binary digits, with the first digit least significant. -/
def heptadBinaryIndex (v : Fin 4 → ZMod 2) : Fin 16 :=
  ⟨(v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val, by
    have h0 := (v 0).val_lt
    have h1 := (v 1).val_lt
    have h2 := (v 2).val_lt
    have h3 := (v 3).val_lt
    omega⟩

/-- Binary coordinates for the sixteen points outside the distinguished heptad. -/
def heptadBinaryPoint (v : Fin 4 → ZMod 2) : Fin 23 :=
  ![0, 6, 7, 8, 9, 10, 18, 12, 13, 15, 19, 22, 20, 21, 16, 14] (heptadBinaryIndex v)

theorem heptadBinaryPoint_not_mem : ∀ v, heptadBinaryPoint v ∉ omega := by decide +kernel

theorem heptadBinaryPoint_injective : Function.Injective heptadBinaryPoint := by decide +kernel

theorem heptadBinaryPoint_surjective : ∀ a : Fin 23, a ∉ omega →
    ∃ v, heptadBinaryPoint v = a := by decide +kernel

/-- The explicit permutation implementing binary translation. -/
def heptadBinaryPermutation (v : Fin 4 → ZMod 2) : Equiv.Perm (Fin 23) :=
  (if v 0 = 1 then generator 0 else 1) *
    (if v 1 = 1 then generator 1 else 1) *
    (if v 2 = 1 then generator 2 else 1) *
    (if v 3 = 1 then generator 3 else 1)

theorem heptadBinaryPermutation_mem (v : Fin 4 → ZMod 2) :
    heptadBinaryPermutation v ∈ M23 := by
  have hm (i : Fin 4) : (if v i = 1 then generator i else 1) ∈ M23 := by
    split_ifs
    · exact generator_mem i
    · exact M23.one_mem
  exact M23.mul_mem (M23.mul_mem (M23.mul_mem (hm 0) (hm 1)) (hm 2)) (hm 3)

theorem heptadBinaryPermutation_fix : ∀ v, ∀ a ∈ omega,
    heptadBinaryPermutation v a = a := by decide +kernel

/-- Compatibility is with actual degree-23 permutations. -/
theorem heptadBinaryPermutation_translate : ∀ v w,
    heptadBinaryPermutation v (heptadBinaryPoint w) = heptadBinaryPoint (v + w) := by
  decide +kernel

theorem heptadBinaryPermutation_zero : heptadBinaryPermutation 0 = 1 := by decide +kernel

theorem heptadBinaryPermutation_add : ∀ v w,
    heptadBinaryPermutation (v + w) = heptadBinaryPermutation v * heptadBinaryPermutation w := by
  decide +kernel

end Sporadic.Mathieu.M23Geometry
