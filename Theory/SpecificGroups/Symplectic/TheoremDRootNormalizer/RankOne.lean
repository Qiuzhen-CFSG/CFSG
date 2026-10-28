module

public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Tactic

/-!
# The rank-one projective symplectic–linear equivalence

A two-dimensional matrix preserves the standard alternating form exactly
when its determinant is one. Reindexing `Fin 1 ⊕ Fin 1` by `Fin 2` therefore
gives a multiplicative equivalence between the actual symplectic and special
linear matrix groups. Transporting their centers gives the corresponding
PSp₂–PSL₂ equivalence for the literal central quotients, over any field.

This identifies the rank-one symplectic case with the PSL₂ case in the
Theorem D reduction, Aschbacher–Smith 14.8.2 (printed pp.1078–1079).
-/

@[expose] public section

open Matrix
namespace Theory.SpecificGroups.SymplecticRoot
variable {F : Type*} [Field F]

/-- Reindex a two-dimensional symplectic matrix as an SL₂ matrix. -/
def rankOneToSL : Sp 1 F →* SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨reindexRingEquiv F finSumFinEquiv g.val, by
    change (reindex finSumFinEquiv finSumFinEquiv g.val).det = 1
    rw [det_reindex_self]
    exact SymplecticGroup.det_eq_one g.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (reindexRingEquiv F finSumFinEquiv)
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (reindexRingEquiv F finSumFinEquiv) g.val h.val

private theorem rankOne_symplectic (A : SpecialLinearGroup (Fin 2) F) :
    reindexRingEquiv F finSumFinEquiv.symm A.val ∈ symplecticGroup (Fin 1) F := by
  have hd := A.property
  rw [det_fin_two] at hd
  rw [SymplecticGroup.mem_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [reindexRingEquiv, reindex, Matrix.mul_apply, Fintype.sum_sum_type,
      J, fromBlocks, finSumFinEquiv, Matrix.one_apply]
  · ring
  · linear_combination -hd
  · linear_combination hd
  · ring

/-- In natural dimension two, the actual symplectic group equals SL₂ up to reindexing. -/
def rankOneEquivSL : Sp 1 F ≃* SpecialLinearGroup (Fin 2) F where
  toFun := rankOneToSL
  invFun A := ⟨reindexRingEquiv F finSumFinEquiv.symm A.val, by exact rankOne_symplectic A⟩
  left_inv g := by
    apply Subtype.ext
    exact (reindexRingEquiv F finSumFinEquiv).symm_apply_apply g.val
  right_inv A := by
    apply Subtype.ext
    exact (reindexRingEquiv F (@finSumFinEquiv 1 1)).apply_symm_apply A.val
  map_mul' := rankOneToSL.map_mul

/-- The rank-one symplectic and linear equivalence descends through their actual centers. -/
def rankOneProjectiveEquiv : PSp 1 F ≃* ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.congr _ _ rankOneEquivSL (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr rankOneEquivSL ⟨x, hx⟩).property
    · intro hy
      exact ⟨rankOneEquivSL.symm y,
        (Subgroup.centerCongr rankOneEquivSL.symm ⟨y, hy⟩).property,
        rankOneEquivSL.apply_symm_apply y⟩)

end Theory.SpecificGroups.SymplecticRoot
