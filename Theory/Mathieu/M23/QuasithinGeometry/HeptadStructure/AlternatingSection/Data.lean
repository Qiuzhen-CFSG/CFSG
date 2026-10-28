module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Concrete generators of the alternating heptad complement

Two explicit permutations fix point 0, preserve the certified Witt blocks,
and act on the heptad as a three-cycle and a seven-cycle. Finite certificates
are checked by the Lean kernel. The tables were obtained from the action on
the fifteen Fano planes determined by the blocks through point 0.

Source: Aschbacher, *Sporadic Groups*, Chapter 6, Lemma 19.1, specialized to
M23; Aschbacher--Smith, §5.2, printed p.655.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.AlternatingSection
open scoped Pointwise
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- An explicit permutation of the ambient 23 points. -/
def cycleLift : Equiv.Perm (Fin 23) where
  toFun := ![0, 2, 3, 1, 4, 5, 18, 14, 15, 13, 16, 11, 6, 20, 21, 19, 22, 17, 12, 8, 9, 7, 10]
  invFun := ![0, 3, 1, 2, 4, 5, 12, 21, 19, 20, 22, 11, 18, 9, 7, 8, 10, 17, 6, 15, 13, 14, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- An explicit permutation of the ambient 23 points. -/
def rotationLift : Equiv.Perm (Fin 23) where
  toFun := ![0, 2, 3, 4, 5, 11, 21, 6, 20, 14, 7, 17, 8, 9, 12, 15, 19, 1, 16, 10, 22, 18, 13]
  invFun := ![0, 17, 1, 2, 3, 4, 7, 10, 12, 13, 19, 5, 14, 22, 9, 15, 18, 11, 21, 16, 8, 6, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def cycleLiftBlockIndex : Fin 253 → Fin 253 :=
  ![
    0, 3, 1, 2, 4, 79, 80, 77, 78, 84, 81, 83,
    82, 90, 85, 91, 87, 89, 92, 86, 88, 6, 8, 5,
    7, 10, 12, 11, 9, 13, 20, 18, 19, 15, 17, 16,
    14, 93, 95, 94, 96, 104, 100, 103, 98, 102, 97, 99,
    101, 107, 110, 106, 108, 109, 105, 112, 111, 131, 127, 117,
    132, 120, 118, 124, 113, 129, 122, 126, 125, 123, 119, 116,
    128, 121, 130, 114, 115, 24, 22, 23, 21, 25, 26, 27,
    28, 36, 32, 35, 30, 34, 29, 33, 31, 134, 136, 135,
    133, 137, 144, 139, 143, 142, 140, 141, 138, 150, 151, 149,
    146, 145, 152, 148, 147, 164, 165, 163, 166, 157, 172, 155,
    167, 159, 169, 171, 154, 170, 160, 162, 153, 158, 156, 168,
    161, 40, 37, 38, 39, 46, 41, 47, 45, 43, 48, 42,
    44, 53, 52, 55, 56, 49, 54, 51, 50, 72, 63, 70,
    74, 59, 65, 73, 67, 60, 58, 76, 64, 75, 71, 61,
    57, 66, 68, 69, 62, 180, 177, 175, 176, 179, 173, 174,
    178, 196, 198, 182, 195, 189, 190, 187, 199, 191, 194, 185,
    181, 184, 186, 193, 192, 197, 183, 200, 188, 219, 201, 204,
    220, 205, 213, 212, 217, 210, 216, 206, 214, 211, 207, 215,
    209, 218, 208, 202, 203, 238, 232, 234, 250, 249, 248, 241,
    231, 227, 221, 237, 246, 225, 252, 244, 235, 228, 230, 243,
    240, 229, 239, 242, 236, 245, 222, 224, 251, 233, 247, 226,
    223
  ]

private theorem cycleLift_block (i : Fin 253) :
    cycleLift • m23BlockAt i = m23BlockAt (cycleLiftBlockIndex i) := by
  have h : ∀ i : Fin 253, ∀ x : Fin 23,
      (m23BlockMask (cycleLiftBlockIndex i)).testBit (cycleLift x).val =
        (m23BlockMask i).testBit x.val := by decide +kernel
  apply Finset.ext
  intro y
  obtain ⟨x, rfl⟩ := cycleLift.surjective y
  change cycleLift • x ∈ cycleLift • m23BlockAt i ↔ _
  rw [Finset.smul_mem_smul_finset_iff]
  simp only [m23BlockAt, m23MaskBlock, Finset.mem_filter, Finset.mem_univ, true_and,
    h i x]

private def rotationLiftBlockIndex : Fin 253 → Fin 253 :=
  ![
    0, 80, 77, 79, 78, 82, 81, 83, 84, 86, 87, 89,
    90, 92, 3, 1, 85, 91, 2, 88, 4, 93, 96, 95,
    94, 102, 97, 103, 100, 99, 8, 5, 98, 6, 101, 104,
    7, 109, 106, 107, 111, 12, 112, 105, 9, 108, 110, 10,
    11, 127, 16, 116, 13, 130, 17, 19, 123, 113, 14, 115,
    128, 132, 126, 124, 117, 114, 118, 119, 122, 20, 125, 18,
    129, 131, 15, 120, 121, 135, 133, 136, 134, 141, 137, 140,
    143, 21, 144, 138, 22, 139, 142, 23, 24, 151, 145, 149,
    148, 146, 28, 25, 147, 26, 150, 152, 27, 35, 162, 156,
    29, 166, 34, 171, 32, 157, 158, 164, 33, 168, 169, 160,
    159, 153, 154, 30, 155, 170, 172, 36, 165, 167, 31, 161,
    163, 175, 174, 177, 179, 178, 39, 37, 173, 180, 38, 176,
    40, 186, 46, 42, 197, 194, 45, 190, 43, 185, 183, 200,
    47, 196, 189, 192, 182, 181, 41, 184, 187, 191, 48, 193,
    195, 198, 199, 44, 188, 49, 218, 205, 56, 217, 53, 208,
    51, 202, 207, 213, 216, 219, 52, 209, 206, 201, 50, 203,
    204, 210, 54, 215, 220, 55, 214, 211, 212, 230, 221, 244,
    236, 69, 247, 249, 58, 227, 229, 225, 224, 250, 233, 235,
    238, 71, 74, 241, 245, 231, 61, 63, 223, 252, 66, 240,
    64, 242, 246, 73, 75, 226, 62, 228, 232, 60, 222, 57,
    59, 243, 72, 76, 237, 239, 65, 234, 67, 248, 251, 68,
    70
  ]

private theorem rotationLift_block (i : Fin 253) :
    rotationLift • m23BlockAt i = m23BlockAt (rotationLiftBlockIndex i) := by
  have h : ∀ i : Fin 253, ∀ x : Fin 23,
      (m23BlockMask (rotationLiftBlockIndex i)).testBit (rotationLift x).val =
        (m23BlockMask i).testBit x.val := by decide +kernel
  apply Finset.ext
  intro y
  obtain ⟨x, rfl⟩ := rotationLift.surjective y
  change rotationLift • x ∈ rotationLift • m23BlockAt i ↔ _
  rw [Finset.smul_mem_smul_finset_iff]
  simp only [m23BlockAt, m23MaskBlock, Finset.mem_filter, Finset.mem_univ, true_and,
    h i x]

private theorem mem_of_block_reindex (g : Equiv.Perm (Fin 23))
    (f : Fin 253 → Fin 253) (h : ∀ i, g • m23BlockAt i = m23BlockAt (f i)) :
    g ∈ M23 := by
  apply (mem_M23_iff g).mpr
  have he : g • m23Blocks = m23Blocks := by
    apply Finset.eq_of_subset_of_card_le
    · intro B hB
      obtain ⟨C, hC, rfl⟩ := Finset.mem_smul_finset.mp hB
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      exact Finset.mem_image.mpr ⟨f i, Finset.mem_univ _, (h i).symm⟩
    · simp
  exact_mod_cast he

/-- The three-cycle lift is an actual automorphism of the Witt design. -/
theorem cycleLift_mem : cycleLift ∈ M23 :=
  mem_of_block_reindex cycleLift cycleLiftBlockIndex cycleLift_block

/-- The seven-cycle lift is an actual automorphism of the Witt design. -/
theorem rotationLift_mem : rotationLift ∈ M23 :=
  mem_of_block_reindex rotationLift rotationLiftBlockIndex rotationLift_block

/-- The source three-cycle, on zero-based heptad labels. -/
def labelCycle : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- The cyclic rotation of all seven heptad labels. -/
def labelRotation : Equiv.Perm (Fin 7) where
  toFun := ![1, 2, 3, 4, 5, 6, 0]
  invFun := ![6, 0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem cycleLift_label (i : Fin 7) : cycleLift (label i) = label (labelCycle i) := by
  revert i; decide +kernel

theorem rotationLift_label (i : Fin 7) :
    rotationLift (label i) = label (labelRotation i) := by
  revert i; decide +kernel

/-- The three-cycle has exactly one fixed point outside the heptad. -/
theorem cycleLift_fixed_iff (q : Fin 23) (hq : q ∈ pairComplement omega) :
    cycleLift q = q ↔ q = 0 := by
  have h : ∀ q ∈ pairComplement omega, cycleLift q = q ↔ q = 0 := by decide +kernel
  exact h q hq

end Sporadic.Mathieu.M23Geometry.AlternatingSection
