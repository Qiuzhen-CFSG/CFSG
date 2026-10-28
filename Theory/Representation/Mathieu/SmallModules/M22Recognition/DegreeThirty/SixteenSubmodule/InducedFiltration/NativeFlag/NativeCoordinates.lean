module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.NativeFlag.NativeBlocks

/-!
# Canonical flattening of the native 22-by-16 coordinates

The equivalence sends `(i,j)` to the flat coordinate `16*i+j`. The checked
packed columns decode to the exact sparse generator matrices: bits outside
their unique sixteen-coordinate block vanish. Reindexing the matrix sum then
proves the saved generator identity for the actual native M22 action.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

@[expose] public section
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration
namespace NativeFlag

/-- The canonical flattening reads coordinate `(i,j)` at `16*i+j`. -/
def e0 : GeneratorMatrices.BinaryCoordinates ≃ₗ[ZMod 2] Space :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finProdFinEquiv (m := 22) (n := 16)).symm

theorem e0_apply (v : GeneratorMatrices.BinaryCoordinates) (i : Fin 22) (j : Fin 16) :
    e0 v (finProdFinEquiv (i,j)) = v (i,j) := by
  change v (finProdFinEquiv.symm (finProdFinEquiv (i,j))) = _
  exact congrArg v ((finProdFinEquiv (m := 22) (n := 16)).symm_apply_apply (i,j))

private theorem bit_block (n : ℕ) (hn : n < 2^16) (i j : Fin 22) (x : Fin 16) :
    bit (n <<< (16*j.val)) (x.val + 16*i.val) =
      if i = j then bit n x.val else 0 := by
  by_cases h : i = j
  · subst j
    simp only [bit, Nat.testBit_shiftLeft]
    have hle : 16*i.val ≤ x.val + 16*i.val := by omega
    simp only [hle, decide_true, Bool.true_and]
    simp only [Nat.add_sub_cancel_right, ite_true]
  · rw [if_neg h]
    unfold bit
    rw [Nat.testBit_shiftLeft]
    by_cases hle : 16*j.val ≤ x.val + 16*i.val
    · simp only [hle, decide_true, Bool.true_and]
      have hij : i.val ≠ j.val := fun he => h (Fin.ext he)
      have hb : n < 2^(x.val + 16*i.val - 16*j.val) :=
        hn.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow hb]
      rfl
    · simp only [hle, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- The packed full matrices use precisely the native inverse-permutation block rule. -/
theorem savedGeneratorMatrix_eq (k : Fin 2) (p q : Fin 22 × Fin 16) :
    savedGeneratorMatrix k (finProdFinEquiv p) (finProdFinEquiv q) =
      GeneratorMatrices.generatorMatrix k p q := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  obtain ⟨l, rfl⟩ := (GeneratorMatrices.generatorPerm k).symm.surjective j
  have hc := saved_columns k l y
  change (generatorColumns k)[16 * (GeneratorMatrices.generatorPoint k l).val + y.val]! = _ at hc
  change bit (generatorColumns k)[y.val + 16 * (GeneratorMatrices.generatorPoint k l).val]!
      (x.val + 16 * i.val) =
    if GeneratorMatrices.generatorPoint k l = GeneratorMatrices.generatorPoint k i then
      LocalBlocks.blocks k i x y else 0
  rw [Nat.add_comm y.val, hc, bit_block _ (local_bound k l y)]
  by_cases h : i = l
  · subst l
    simp only [ite_true, local_blocks]
  · have h' : GeneratorMatrices.generatorPoint k l ≠ GeneratorMatrices.generatorPoint k i := by
      intro he
      exact h ((GeneratorMatrices.generatorPerm k).symm.injective he).symm
    rw [if_neg h, if_neg h']

/-- Flattening intertwines the genuine native action with the saved matrices. -/
theorem e0_generator (k : Fin 2) (v : GeneratorMatrices.BinaryCoordinates) :
    e0 (GeneratorMatrices.binaryAdjoint (GeneratorMatrices.generator k) v) =
      (savedGeneratorMatrix k).mulVec (e0 v) := by
  rw [GeneratorMatrices.binaryAdjoint_generator]
  apply funext
  intro x
  obtain ⟨p, rfl⟩ := (finProdFinEquiv (m := 22) (n := 16)).surjective x
  rw [e0_apply]
  change (∑ q, GeneratorMatrices.generatorMatrix k p q * v q) =
    ∑ y, savedGeneratorMatrix k (finProdFinEquiv p) y * e0 v y
  rw [← (finProdFinEquiv (m := 22) (n := 16)).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  rw [savedGeneratorMatrix_eq, e0_apply]

end NativeFlag
end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration
