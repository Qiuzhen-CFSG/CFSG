module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfectness of binary linear groups

In dimension at least three, each elementary matrix is the commutator of
two elementary matrices through a third coordinate. Gaussian elimination
then proves that SL is perfect. Over the binary field GL equals SL, so the
same assertion holds for the actual linear automorphism group.

This supplies both the full-group exclusion and the four-dimensional Levi
factor needed for the residual recognition in Aschbacher–Smith, combined
manuscript (1 March 2004), A.3.12(5), printed pp.47–48, and 1.3.9, p.514.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace BinaryLinear
open OuterCyclic

/-- Every binary linear group of dimension at least three is perfect. -/
theorem linearGroup_isPerfect (n : ℕ) (hn : 3 ≤ n) : Group.IsPerfect (LinearGroup n) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    constructor
    apply top_unique
    intro g _
    refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun x => x ∈ commutator (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) g ?_ ?_
      (fun _ _ => mul_mem)
    · intro i j hij c hc
      have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc
      have hd : Matrix.SpecialLinearGroup.diag2n hij c hc = 1 := by
        apply Subtype.ext
        simp [Matrix.SpecialLinearGroup.diag2n_coe, hc1]
      rw [hd]
      exact one_mem _
    · intro i j hij c
      obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
      have hik := hki.symm
      let x := Matrix.SpecialLinearGroup.transvection hik c
      let y := Matrix.SpecialLinearGroup.transvection hkj (1 : ZMod 2)
      let z := Matrix.SpecialLinearGroup.transvection hij c
      have hchain : x * y = y * z * x := by
        apply Subtype.ext
        simp [x, y, z, Matrix.SpecialLinearGroup.transvection_coe, mul_add, add_mul,
          Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
          add_assoc, add_comm, add_left_comm]
      have hcomm : y * z = z * y := by
        apply Subtype.ext
        simp [y, z, Matrix.SpecialLinearGroup.transvection_coe, mul_add, add_mul,
          Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
          Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm, add_comm, add_left_comm]
      have he : ⁅x, y⁆ = z := by
        rw [commutatorElement_def, hchain, hcomm]
        simp [mul_assoc]
      change z ∈ _
      rw [← he]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
  exact Group.IsPerfect.ofSurjective (f := (slEquivLinear n).toMonoidHom) (slEquivLinear n).surjective

end BinaryLinear
