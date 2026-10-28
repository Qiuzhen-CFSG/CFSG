module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.CharP.Two
public import Theory.Representation.FirstCohomologySymplecticFour.Generation
import Mathlib.Tactic.FinCases

/-!
# Cubic elements in the derived groups of even classical groups

In characteristic two, the commutator of the opposite transvections with
parameter one has the block `[[1, 1], [1, 0]]`. Its cube is one and its
off-diagonal entry is nonzero. It therefore survives the scalar quotient,
giving divisibility by three for the derived group of PSL in every degree
at least two. The two long roots on a hyperbolic pair give the same element
in Sp₄. Neither argument identifies the derived group with the ambient group,
so both include the field of order two.

These elementary matrix calculations supply the classical field-derived
comparisons used in Aschbacher–Smith, *The Classification of Quasithin Groups*,
16.1.7(3a) and the proof of 16.2.6(1), printed pp.1172–1174.
-/

public section

namespace Theory.SpecificGroups.Classical.EvenDerivedThree
open Matrix Subgroup
open scoped MatrixGroups commutatorElement

section Linear
variable {F ι : Type*} [Field F] [CharP F 2] [Fintype ι] [DecidableEq ι]
variable {i j : ι} (hij : i ≠ j)

private def linearCommutator : SpecialLinearGroup ι F :=
  ⁅SpecialLinearGroup.transvection hij (1 : F),
    SpecialLinearGroup.transvection hij.symm (1 : F)⁆

private theorem linearCommutator_matrix : (linearCommutator (F := F) hij : Matrix ι ι F) =
    1 + single j j 1 + single i j 1 + single j i 1 := by
  simp only [linearCommutator, commutatorElement_def, SpecialLinearGroup.transvection_inv,
    CharTwo.neg_eq, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  simp only [mul_add, add_mul, one_mul, mul_one, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij, single_mul_single_of_ne _ _ _ _ hij.symm,
    add_zero]
  ext a b
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [single, one_apply, CharTwo.add_self_eq_zero, eq_comm]

private theorem linearCommutator_cube : linearCommutator (F := F) hij ^ 3 = 1 := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one, linearCommutator_matrix]
  simp only [pow_succ, pow_zero, mul_one, mul_add, add_mul, one_mul,
    single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij, single_mul_single_of_ne _ _ _ _ hij.symm,
    add_zero]
  ext a b
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [single, one_apply, CharTwo.add_self_eq_zero, eq_comm]

private theorem linearCommutator_not_mem_center :
    linearCommutator (F := F) hij ∉ Subgroup.center (SpecialLinearGroup ι F) := by
  intro hc
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have hh := congrArg (fun A : Matrix ι ι F => A i j) hr
  rw [linearCommutator_matrix] at hh
  simp [Matrix.scalar, Matrix.diagonal, single, one_apply, hij, hij.symm] at hh

end Linear

private theorem three_dvd_of_cubic_commutator {G : Type*} [Group G] (a b : G)
    (hc : ⁅a, b⁆ ^ 3 = 1) (hn : ⁅a, b⁆ ≠ 1) :
    3 ∣ Nat.card (commutator G) := by
  rw [← orderOf_eq_prime hc hn]
  exact (commutator G).orderOf_dvd_natCard
    (commutator_mem_commutator (mem_top _) (mem_top _))

/-- Two opposite transvections supply an element of order three in the actual
derived subgroup of the projective special linear group. -/
theorem three_dvd_card_psl_commutator {F ι : Type*} [Field F] [CharP F 2]
    [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    3 ∣ Nat.card (commutator (ProjectiveSpecialLinearGroup ι F)) := by
  let q := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup ι F))
  apply three_dvd_of_cubic_commutator
    (q (SpecialLinearGroup.transvection hij 1))
    (q (SpecialLinearGroup.transvection hij.symm 1))
  · rw [← map_commutatorElement, ← map_pow]
    change q (linearCommutator hij ^ 3) = 1
    rw [linearCommutator_cube, map_one]
  · rw [← map_commutatorElement]
    change QuotientGroup.mk (linearCommutator hij) ≠ (1 : ProjectiveSpecialLinearGroup ι F)
    exact fun h => linearCommutator_not_mem_center hij ((QuotientGroup.eq_one_iff _).mp h)

section Symplectic
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F]

private def toSL : Matrix.symplecticGroup (Fin 2) F →*
    SpecialLinearGroup (Fin 2 ⊕ Fin 2) F where
  toFun g := ⟨g.val, SymplecticGroup.det_eq_one g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem toSL_injective : Function.Injective (toSL (F := F)) := by
  intro a b h
  exact Subtype.ext (congrArg (fun g : SpecialLinearGroup (Fin 2 ⊕ Fin 2) F => g.val) h)

private theorem toSL_root0 : toSL (rootElement 0 (1 : F)) =
    SpecialLinearGroup.transvection (show (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2) ≠ .inr 0
      from Sum.inl_ne_inr) 1 := by
  apply Subtype.ext
  change rootMatrix 0 (1 : F) = 1 + single (.inl 0) (.inr 0) 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.single, Matrix.fromBlocks]

private theorem toSL_root1 : toSL (rootElement 1 (1 : F)) =
    SpecialLinearGroup.transvection (show (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2) ≠ .inl 0
      from Sum.inr_ne_inl) 1 := by
  apply Subtype.ext
  change rootMatrix 1 (1 : F) = 1 + single (.inr 0) (.inl 0) 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.single, Matrix.fromBlocks]

variable [CharP F 2]

/-- The two long roots on the first hyperbolic pair supply an element of
order three in the actual derived subgroup of the symplectic four-space group. -/
theorem three_dvd_card_sp4_commutator :
    3 ∣ Nat.card (commutator (Matrix.symplecticGroup (Fin 2) F)) := by
  have hm : toSL ⁅rootElement 0 (1 : F), rootElement 1 1⁆ =
      linearCommutator (F := F) (show (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2) ≠ .inr 0
        from Sum.inl_ne_inr) := by
    rw [map_commutatorElement, toSL_root0, toSL_root1]
    rfl
  apply three_dvd_of_cubic_commutator (rootElement 0 (1 : F)) (rootElement 1 1)
  · apply toSL_injective
    rw [map_pow, hm, linearCommutator_cube, map_one]
  · intro h
    have he : linearCommutator (F := F) (show (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2) ≠ .inr 0
        from Sum.inl_ne_inr) = 1 := by rw [← hm, h, map_one]
    exact linearCommutator_not_mem_center Sum.inl_ne_inr (he ▸ (Subgroup.center _).one_mem)

end Symplectic

end Theory.SpecificGroups.Classical.EvenDerivedThree

end
