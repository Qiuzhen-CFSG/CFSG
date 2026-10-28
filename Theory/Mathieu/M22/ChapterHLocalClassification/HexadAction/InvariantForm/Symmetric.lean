module

public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.InvariantForm.FiveCycle
public import Mathlib.GroupTheory.Perm.Closure
import Mathlib.Tactic

/-!
# An invariant form for faithful binary four-dimensional S₆ actions

A transposition a and a five-cycle c generate S₆, with a² = (ac)⁶ = 1.
Normalize the image of c to the cyclotomic companion matrix. The bounded
matrix certificate then supplies a nonsingular alternating form fixed by
both generators. Its stabilizer is a subgroup, so it contains the whole
image. Pulling the form back through the change of basis proves the result
for the original representation.

This structural argument supplies the form used by the native hexad
conjugation action in Aschbacher--Smith H.14.3(3), printed p.397.
-/

open Equiv Equiv.Perm Subgroup Matrix
namespace BinaryFourSymmetricForm
private def swap01 : Perm (Fin 6) := Equiv.swap 0 1
private def cycle5 : Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5
private theorem cycle5_order : orderOf cycle5 = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime <;> decide +kernel
private theorem generators : closure ({swap01, cycle5} : Set (Perm (Fin 6))) = ⊤ := by
  let S := closure ({swap01, cycle5} : Set (Perm (Fin 6)))
  have ha : swap01 ∈ S := subset_closure (by simp)
  have hb : cycle5 ∈ S := subset_closure (by simp)
  have hc : (swap01 * cycle5).IsCycle := by
    refine ⟨0, by decide +kernel, ?_⟩
    intro y _
    refine ⟨(y.val : ℤ), ?_⟩
    rw [zpow_natCast]
    revert y
    decide +kernel
  have hs : (swap01 * cycle5).support = Finset.univ := by decide +kernel
  have hg := closure_cycle_adjacent_swap hc hs 0
  have hh : closure ({swap01 * cycle5, swap01} : Set (Perm (Fin 6))) ≤ S := by
    apply (closure_le _).2
    intro x hx
    rcases hx with rfl | rfl
    · exact S.mul_mem ha hb
    · exact ha
  have he : Equiv.swap 0 ((swap01 * cycle5) 0) = swap01 := by decide +kernel
  rw [he] at hg
  rw [hg] at hh
  exact top_le_iff.mp hh

private def preserving (B : Mat) : Subgroup GL4 where
  carrier := {g | g.val.transpose * B * g.val = B}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (a.val * b.val).transpose * B * (a.val * b.val) = B
    calc
      _ = b.val.transpose * (a.val.transpose * B * a.val) * b.val := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = B := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    change a.inv.transpose * B * a.inv = B
    calc
      _ = a.inv.transpose * (a.val.transpose * B * a.val) * a.inv := by rw [ha]
      _ = (a.val * a.inv).transpose * B * (a.val * a.inv) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = B := by rw [a.val_inv]; simp

/-- Every faithful binary representation of S₆ of degree four preserves
an actual nonsingular alternating form, by the checked generator relations. -/
public theorem exists_matrix_form (f : Perm (Fin 6) →* GL4) (hf : Function.Injective f) :
    ∃ B : Mat, B.toBilin'.IsAlt ∧ B.toBilin'.Nondegenerate ∧
      ∀ s, (f s).val.transpose * B * (f s).val = B := by
  obtain ⟨e, he⟩ := normalize_five (f cycle5) ((orderOf_injective f hf _).trans cycle5_order)
  let f' : Perm (Fin 6) →* GL4 := (MulAut.conj e).toMonoidHom.comp f
  have hb : f' cycle5 = five := he
  have h2 : (f' swap01).val ^ 2 = 1 := by
    have hh : f' swap01 ^ 2 = 1 := by
      rw [← map_pow, show swap01 ^ 2 = 1 by decide +kernel, map_one]
    exact congrArg Units.val hh
  have h6 : ((f' swap01).val * C) ^ 6 = 1 := by
    have hh : (f' swap01 * f' cycle5) ^ 6 = 1 := by
      rw [← map_mul, ← map_pow,
        show (swap01 * cycle5) ^ 6 = 1 by decide +kernel, map_one]
    rw [hb] at hh
    exact congrArg Units.val hh
  obtain ⟨B, hBa, hBn, hA, hC⟩ := matrixCertificate (f' swap01).val h2 h6
  have hle : closure ({swap01, cycle5} : Set (Perm (Fin 6))) ≤ (preserving B).comap f' := by
    apply (closure_le _).2
    intro x hx
    rcases hx with rfl | rfl
    · exact hA
    · change (f' cycle5).val.transpose * B * (f' cycle5).val = B
      rw [hb]
      exact hC
  have hp (s : Perm (Fin 6)) : (f' s).val.transpose * B * (f' s).val = B :=
    hle (generators.symm ▸ (show s ∈ (⊤ : Subgroup (Perm (Fin 6))) from trivial))
  refine ⟨e.val.transpose * B * e.val, ?_, ?_, ?_⟩
  · rw [← Matrix.toBilin'_comp]
    intro v
    exact hBa (e.val.toLin' v)
  · apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have hn := LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp hBn
    exact mul_ne_zero (mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero e) hn)
      (Matrix.GeneralLinearGroup.det_ne_zero e)
  · intro s
    have heq : e.val * (f s).val = (f' s).val * e.val := by
      have h : e * f s = f' s * e := by dsimp [f']; group
      exact congrArg Units.val h
    calc
      _ = (e.val * (f s).val).transpose * B * (e.val * (f s).val) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ((f' s).val * e.val).transpose * B * ((f' s).val * e.val) := by rw [heq]
      _ = e.val.transpose * ((f' s).val.transpose * B * (f' s).val) * e.val := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hp s]
end BinaryFourSymmetricForm
