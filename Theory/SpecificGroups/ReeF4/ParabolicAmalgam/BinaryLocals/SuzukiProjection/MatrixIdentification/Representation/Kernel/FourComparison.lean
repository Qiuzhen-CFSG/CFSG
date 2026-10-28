module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.Words
public import Theory.Alternating.theorem_5_2_1_2
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Faithfulness of the four-dimensional A₅ chain

The explicit binary matrices obtained from the five chain words satisfy the
A₅ Coxeter relations. These finite identities are checked by the Lean kernel
over `ZMod 2` and transported through the coefficient-field algebra map. The
proved type-A presentation identifies the resulting source group with S₆.
Every nontrivial normal subgroup of S₆ contains A₆, whereas the product of
the first two adjacent generators has nonidentity image. Thus the map from
S₆ to the four-dimensional matrices is injective.

No ambient F₄ relation is inferred from its four-dimensional image here.
Those relations belong to the remaining ambient comparison. Source context:
Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 (PDF pp.274–275) of
`refs/quasithin.pdf`; the type-A presentation is proved in
`Theory.Alternating.theorem_5_2_1_2`.
-/

@[expose] public section
noncomputable section
open scoped Matrix
open GLS3.Chapter5.SchurPresentation

namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof

private def binaryGenerator (i : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![!![1,0,0,0; 0,1,1,0; 0,0,1,0; 0,0,0,1],
    !![1,1,0,0; 0,1,0,0; 0,0,1,1; 0,0,0,1],
    !![1,0,0,0; 0,1,0,0; 0,1,1,0; 0,0,0,1],
    !![1,0,0,0; 1,1,0,0; 0,0,1,0; 0,0,1,1]] i

private def binaryChain (i : Fin 5) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![!![1,0,0,0; 0,1,1,0; 0,0,1,0; 0,0,0,1],
    !![1,0,0,0; 0,1,0,0; 0,1,1,0; 0,0,0,1],
    !![1,0,1,1; 0,1,1,1; 0,0,1,0; 0,0,0,1],
    !![1,0,0,0; 0,1,0,0; 0,0,1,0; 1,0,0,1],
    !![1,0,0,1; 0,1,0,0; 0,0,1,0; 0,0,0,1]] i

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private theorem binaryChain_word :
    (fun i => ((chainWord i).map binaryGenerator).prod) = binaryChain := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private theorem binaryChain_liftable : (CoxeterMatrix.A 5).IsLiftable binaryChain := by
  unfold CoxeterMatrix.IsLiftable
  decide +kernel

private theorem binaryGenerator_map (i : Fin 4) :
    (binaryGenerator i).map (algebraMap (ZMod 2) (CoefficientField 0)) =
      (matrixGenerator i).val := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [binaryGenerator, matrixGenerator, generatorMatrix]

private theorem word_matrix_map (w : List (Fin 4)) :
    ((w.map binaryGenerator).prod).map (algebraMap (ZMod 2) (CoefficientField 0)) =
      ((w.map matrixGenerator).prod).val := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.map_mul, Units.val_mul,
      binaryGenerator_map, ih]

private theorem fourChain_val (i : Fin 5) :
    (fourChain i).val =
      (binaryChain i).map (algebraMap (ZMod 2) (CoefficientField 0)) := by
  rw [← binaryChain_word]
  exact (word_matrix_map _).symm

/-- The actual four-dimensional chain satisfies the A₅ Coxeter presentation. -/
theorem fourChain_liftable : (CoxeterMatrix.A 5).IsLiftable fourChain := by
  intro i j
  apply Units.ext
  change ((fourChain i).val * (fourChain j).val) ^ (CoxeterMatrix.A 5) i j = 1
  rw [fourChain_val, fourChain_val, ← Matrix.map_mul, ← Matrix.map_pow,
    binaryChain_liftable i j]
  simp

/-- The proved type-A presentation, specialized to S₆. -/
def sixCoxeterEquiv : (CoxeterMatrix.A 5).Group ≃* Equiv.Perm (Fin 6) :=
  MulEquiv.ofBijective (typeACoxeterPermutationProjection 1)
    ⟨typeACoxeterPermutationProjection_injective 1,
      typeACoxeterPermutationProjection_surjective 1⟩

theorem sixCoxeterEquiv_simple (i : Fin 5) :
    sixCoxeterEquiv ((CoxeterMatrix.A 5).simple i) = adjacentSwap 1 i :=
  typeACoxeterPermutationProjection_simple 1 i

/-- The four-space representation of S₆ supplied by this chain. -/
def fourHom : Equiv.Perm (Fin 6) →* BinaryGL :=
  ((CoxeterMatrix.A 5).toCoxeterSystem.lift ⟨fourChain, fourChain_liftable⟩).comp
    sixCoxeterEquiv.symm.toMonoidHom

theorem fourHom_adjacent (i : Fin 5) : fourHom (adjacentSwap 1 i) = fourChain i := by
  rw [← sixCoxeterEquiv_simple i]
  change ((CoxeterMatrix.A 5).toCoxeterSystem.lift ⟨fourChain, fourChain_liftable⟩)
    (sixCoxeterEquiv.symm (sixCoxeterEquiv ((CoxeterMatrix.A 5).simple i))) = _
  rw [MulEquiv.symm_apply_apply]
  exact (CoxeterMatrix.A 5).toCoxeterSystem.lift_apply_simple fourChain_liftable i

private theorem first_pair_ne_one : fourChain 0 * fourChain 1 ≠ 1 := by
  intro h
  have he := congrArg (fun M : BinaryGL => M.val 1 2) h
  norm_num [fourChain, chainWord, matrixGenerator, generatorMatrix, Matrix.mul_apply,
    Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.one_apply] at he
  exact (by decide : (1 : Fin 4) ≠ 2) he

/-- A nontrivial normal subgroup of S₆ contains A₆. The image of the first
adjacent three-cycle is nonidentity, so the four-space map is faithful. -/
theorem fourHom_injective : Function.Injective fourHom := by
  apply (fourHom.ker_eq_bot_iff).mp
  by_contra h
  have ht := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp)
    ((Subgroup.nontrivial_iff_ne_bot fourHom.ker).mpr h)
  have hm : adjacentSwap 1 0 * adjacentSwap 1 1 ∈ alternatingGroup (Fin 6) := by
    simp [Equiv.Perm.mem_alternatingGroup, adjacentSwap]
  have hz := MonoidHom.mem_ker.mp (ht hm)
  rw [map_mul, fourHom_adjacent, fourHom_adjacent] at hz
  exact first_pair_ne_one hz

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof
