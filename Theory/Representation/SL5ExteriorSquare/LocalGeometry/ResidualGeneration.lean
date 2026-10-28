module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.MiddleResidual
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Endpoints

/-!
# Generation by two exterior local residuals

The actual residual of the two-space parabolic and either the three-space
residual or the hyperplane residual generate SL₅(2). Their elementary
transvections supply every matrix position directly or as a commutator
through the third coordinate. Binary elimination then gives the whole group.

This is the quotient generation used in the normalizer argument of
Aschbacher--Smith, 12.5.4, printed p.819. The ambient application lifts it
through the original component actor and its two-core kernel.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

private theorem transvection_parabolic (k : ℕ) (i j : Fin 5) (hij : i ≠ j)
    (hp : j.val < k → i.val < k) : elementary i j ∈ parabolic k := by
  rw [parabolic_eq_closure_transvections]
  exact subset_closure ⟨i, j, hij, 1, hp, by simp [elementary, hij]⟩

private theorem transvection_point (i j : Fin 5) (hij : i ≠ j)
    (hj : 2 ≤ j.val) : elementary i j ∈ parabolicResidual 2 := by
  rw [parabolicResidual_two]
  have hp := transvection_parabolic 2 i j hij (by omega)
  refine ⟨⟨_, hp⟩, ?_, rfl⟩
  change parabolicTwoSmallBlock ⟨_, hp⟩ = 1
  apply Subtype.ext
  ext a b
  rw [parabolicTwoSmallBlock_entry]
  have hjb : j.val ≠ b.val := by have := b.isLt; omega
  simp [elementary, hij, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.single, Matrix.one_apply, Fin.ext_iff, hjb]

private theorem transvection_three (i j : Fin 5) (hij : i ≠ j)
    (hi : i.val < 3) : elementary i j ∈ parabolicResidual 3 := by
  rw [parabolicResidual_three]
  have hp := transvection_parabolic 3 i j hij (fun _ => hi)
  refine ⟨⟨_, hp⟩, ?_, rfl⟩
  change parabolicThreeSmallBlock ⟨_, hp⟩ = 1
  apply Subtype.ext
  ext a b
  rw [parabolicThreeSmallBlock_entry]
  have hia : i.val ≠ 3 + a.val := by omega
  simp [elementary, hij, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.single, Matrix.one_apply, Fin.ext_iff, hia]

private theorem elementary_comm (i s j : Fin 5)
    (his : i ≠ s) (hsj : s ≠ j) (hij : i ≠ j) :
    ⁅elementary i s, elementary s j⁆ = elementary i j := by
  rw [commutatorElement_def,
    inv_eq_of_mul_eq_one_left (elementary_square i s),
    inv_eq_of_mul_eq_one_left (elementary_square s j)]
  calc
    elementary i s * elementary s j * elementary i s * elementary s j =
        (elementary i s * (elementary s j * elementary i s)) * elementary s j := by
      simp only [mul_assoc]
    _ = (elementary s j * elementary i j) * elementary s j := by
      rw [elementary_steinberg i s j his hsj hij]
    _ = elementary i j := by
      rw [elementary_commute s j i j hsj hij.symm, mul_assoc,
        elementary_square, mul_one]

/-- The actual point residual and either of the other two residuals generate SL₅(2). -/
theorem pointResidual_sup_eq_top (k : ℕ) (hk : k = 3 ∨ k = 4) :
    parabolicResidual 2 ⊔ parabolicResidual k = ⊤ := by
  let H := parabolicResidual 2 ⊔ parabolicResidual k
  have hupper (i j : Fin 5) (hij : i ≠ j) (hi : i.val < 3) : elementary i j ∈ H := by
    apply mem_sup_right
    rcases hk with rfl | rfl
    · exact transvection_three i j hij hi
    · rw [parabolicResidual_four]
      exact transvection_parabolic 4 i j hij (by omega)
  have hall (i j : Fin 5) (hij : i ≠ j) : elementary i j ∈ H := by
    by_cases hj : 2 ≤ j.val
    · exact mem_sup_left (transvection_point i j hij hj)
    by_cases hi : i.val < 3
    · exact hupper i j hij hi
    have hi2 : i ≠ (2 : Fin 5) := by intro he; subst i; omega
    have h2j : (2 : Fin 5) ≠ j := by intro he; subst j; omega
    rw [← elementary_comm i 2 j hi2 h2j hij]
    exact H.commutator_le_self (commutator_mem_commutator
      (mem_sup_left (transvection_point i 2 hi2 (by decide)))
      (hupper 2 j h2j (by decide)))
  apply top_unique
  have hz : parabolic 0 = ⊤ := by
    ext g
    simp only [mem_top, iff_true]
    apply (mem_parabolic_iff_lowerLeft_zero 0 g).mpr
    intro i j hi hj
    omega
  rw [← hz, parabolic_eq_closure_transvections]
  apply (closure_le _).mpr
  rintro _ ⟨i, j, hij, c, _, rfl⟩
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp
  · change Matrix.SpecialLinearGroup.transvection hij 1 ∈ H
    have hh := hall i j hij
    unfold elementary at hh
    rw [dif_pos hij] at hh
    exact hh

end Representation.SL5ExteriorSquare
