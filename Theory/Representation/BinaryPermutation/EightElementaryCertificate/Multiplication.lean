module
public import Theory.Representation.BinaryPermutation.EightElementaryCertificate.Data
/-! Multiplication and involution coverage in the actual tree-permutation model. -/
@[expose] public section
open BinaryPermutation BinaryPermutation.EightNonsingular
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace BinaryPermutation.EightElementaryCertificate
set_option maxRecDepth 4096 in
private theorem mul_block_0 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨0*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨0*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
set_option maxRecDepth 4096 in
private theorem mul_block_1 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨1*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨1*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
set_option maxRecDepth 4096 in
private theorem mul_block_2 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨2*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨2*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
set_option maxRecDepth 4096 in
private theorem mul_block_3 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨3*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨3*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
set_option maxRecDepth 4096 in
private theorem mul_block_4 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨4*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨4*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
set_option maxRecDepth 4096 in
private theorem mul_block_5 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨5*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨5*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
set_option maxRecDepth 4096 in
private theorem mul_block_6 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨6*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨6*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
set_option maxRecDepth 4096 in
private theorem mul_block_7 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨7*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨7*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
set_option maxRecDepth 4096 in
private theorem mul_block_8 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨8*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨8*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
set_option maxRecDepth 4096 in
private theorem mul_block_9 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨9*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨9*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
set_option maxRecDepth 4096 in
private theorem mul_block_10 : ∀ a : Fin 4, ∀ b : Fin 44,
    treeWord (multiply (involutions ⟨10*4+a.val, by omega⟩) (involutions b)) =
      treeWord (involutions ⟨10*4+a.val, by omega⟩) * treeWord (involutions b) := by decide +kernel
theorem multiply_correct (a b : Fin 44) :
    treeWord (multiply (involutions a) (involutions b)) = treeWord (involutions a) * treeWord (involutions b) := by
  have aux (d : Fin 11) (m : Fin 4) :
      treeWord (multiply (involutions ⟨d.val*4+m.val, by omega⟩) (involutions b)) =
        treeWord (involutions ⟨d.val*4+m.val, by omega⟩) * treeWord (involutions b) := by
    fin_cases d
    · exact mul_block_0 m b
    · exact mul_block_1 m b
    · exact mul_block_2 m b
    · exact mul_block_3 m b
    · exact mul_block_4 m b
    · exact mul_block_5 m b
    · exact mul_block_6 m b
    · exact mul_block_7 m b
    · exact mul_block_8 m b
    · exact mul_block_9 m b
    · exact mul_block_10 m b
  let d : Fin 11 := ⟨a.val / 4, by omega⟩
  let m : Fin 4 := ⟨a.val % 4, Nat.mod_lt _ (by decide)⟩
  have he : (⟨d.val*4+m.val, by omega⟩ : Fin 44) = a := by
    apply Fin.ext
    dsimp [d,m]
    omega
  exact he ▸ aux d m
theorem involution_cover : ∀ i : Fin 128, (treeWord i)^2 = 1 →
    ∃ a, involutions a = i := by decide +kernel
end BinaryPermutation.EightElementaryCertificate
