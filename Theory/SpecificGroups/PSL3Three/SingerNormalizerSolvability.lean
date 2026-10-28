module

public import Theory.SpecificGroups.PSL3Three.Subgroups
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Solvability of the Singer normalizer in PSL₃(3)

The full ambient normalizer acts on its cyclic Singer subgroup. The image
is abelian because automorphisms of a cyclic group commute. The kernel is
abelian as well: a matrix commuting with the companion matrix is determined
by its first column, and matrices of the resulting form commute pairwise.
Thus the normalizer is a solvable extension, and so is its projective image.

This is the centralizer–automorphism argument underlying GLS, volume III,
Theorem 6.5.3(c), in `refs/KGroup/GLS3/chapter6.tex`. The explicit companion
matrix calculation replaces the field-centralizer identification and controls
the entire normalizer without using a maximal-subgroup classification.
-/

namespace Matrix.PSL3Three

private def centralizerMatrix (a b c : ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![a, c, b; b, a + c, b + c; c, b, a + c]

private theorem centralizer_matrix_shape (A : SL)
    (h : singerGenerator * A = A * singerGenerator) :
    A.val = centralizerMatrix (A 0 0) (A 1 0) (A 2 0) := by
  have hm : singerGenerator.val * A.val = A.val * singerGenerator.val :=
    congrArg Subtype.val h
  have h01 := congrFun (congrFun hm 0) 0
  have h11 := congrFun (congrFun hm 1) 0
  have h21 := congrFun (congrFun hm 2) 0
  have h02 := congrFun (congrFun hm 0) 1
  have h12 := congrFun (congrFun hm 1) 1
  have h22 := congrFun (congrFun hm 2) 1
  simp [singerGenerator, Matrix.mul_apply, Fin.sum_univ_succ] at h01 h11 h21 h02 h12 h22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralizerMatrix, ← h01, ← h11, ← h21, ← h02, ← h12, ← h22, add_comm]

private theorem centralizerMatrix_comm (a b c d e f : ZMod 3) :
    centralizerMatrix a b c * centralizerMatrix d e f =
      centralizerMatrix d e f * centralizerMatrix a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralizerMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem centralizer_comm (A B : SL)
    (hA : A ∈ Subgroup.centralizer (singerSubgroupSL : Set SL))
    (hB : B ∈ Subgroup.centralizer (singerSubgroupSL : Set SL)) : A * B = B * A := by
  have hs : singerGenerator ∈ singerSubgroupSL := by
    change singerGenerator ∈ Subgroup.zpowers singerGenerator
    exact ⟨1, by simp⟩
  have ha := centralizer_matrix_shape A (Subgroup.mem_centralizer_iff.mp hA _ hs)
  have hb := centralizer_matrix_shape B (Subgroup.mem_centralizer_iff.mp hB _ hs)
  apply Subtype.ext
  change A.val * B.val = B.val * A.val
  rw [ha, hb]
  exact centralizerMatrix_comm _ _ _ _ _ _

/-- The full ambient normalizer of the Singer subgroup in SL₃(3) is solvable. -/
public theorem singerNormalizerSL_isSolvable : Group.IsSolvable singerNormalizerSL := by
  change Group.IsSolvable (Subgroup.normalizer (singerSubgroupSL : Set SL))
  let : IsCyclic singerSubgroupSL := Subgroup.isCyclic_zpowers singerGenerator
  let : Group.IsSolvable (MulAut singerSubgroupSL) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (IsCyclic.mulAutMulEquiv singerSubgroupSL).toMonoidHom)
      (IsCyclic.mulAutMulEquiv singerSubgroupSL).injective
  let f := singerSubgroupSL.normalizerMonoidHom
  have hk (a : f.ker) : a.val.val ∈ Subgroup.centralizer (singerSubgroupSL : Set SL) := by
    exact singerSubgroupSL.normalizerMonoidHom_ker.le a.property
  let : Group.IsSolvable f.ker := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subtype.ext (centralizer_comm _ _ (hk a) (hk b)))
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by
    rw [Subgroup.range_subtype])

/-- The specified Singer normalizer in PSL₃(3) is solvable. -/
public theorem singerNormalizer_isSolvable : Group.IsSolvable singerNormalizer := by
  let := singerNormalizerSL_isSolvable
  exact Group.isSolvable_of_surjective (project.subgroupMap_surjective singerNormalizerSL)

end Matrix.PSL3Three
