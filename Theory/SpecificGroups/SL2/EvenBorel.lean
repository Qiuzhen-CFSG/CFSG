module

public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.CharP.Two

/-!
# The upper-unipotent centralizer in even SL₂

Commutation with the upper transvection of parameter one forces an SL₂
matrix to have zero lower-left entry and equal diagonal entries. In
characteristic two its determinant then forces both diagonal entries to
be one. The upper-unipotent centralizer is therefore exactly the upper
unipotents. This uses the intrinsic transvection model and has no dependency
on a classification campaign.

Source: the elementary PSL₂ Borel calculation used in Aschbacher–Smith,
E.6.11, printed p.250.
-/

public section

open Subgroup Matrix Matrix.SpecialLinearGroup
namespace Theory.SpecificGroups.SL2.EvenBorel

/-- In characteristic two the upper-unipotent subgroup is self-centralizing. -/
theorem unipotent_centralizer {F : Type*} [Field F] [CharP F 2] :
    centralizer (upperUnipotent F : Set (SpecialLinearGroup (Fin 2) F)) =
      upperUnipotent F := by
  apply le_antisymm
  · intro g hg
    let u : SpecialLinearGroup (Fin 2) F := transvection zero_ne_one (1 : F)
    have he := mem_centralizer_iff.mp hg u ((mem_upperUnipotent F _).mpr ⟨1, rfl⟩)
    have h10 : g.val 1 0 = 0 := by
      have he00 := congrArg (fun a : SpecialLinearGroup (Fin 2) F => a.val 0 0) he
      simpa [u, transvection_coe, mul_apply, Fin.sum_univ_two] using he00
    have heq : g.val 0 0 = g.val 1 1 := by
      have he01 := congrArg (fun a : SpecialLinearGroup (Fin 2) F => a.val 0 1) he
      have he01' : g.val 0 1 + g.val 1 1 = g.val 0 0 + g.val 0 1 := by
        simpa [u, transvection_coe, mul_apply, Fin.sum_univ_two] using he01
      exact (add_left_cancel (he01'.trans (add_comm _ _))).symm
    have hs : g.val 0 0 ^ 2 = 1 := by
      simpa only [det_fin_two, h10, ← heq, pow_two, mul_zero, sub_zero] using g.property
    have h00 : g.val 0 0 = 1 := by
      rcases sq_eq_one_iff.mp hs with ha | ha
      · exact ha
      · simpa only [CharTwo.neg_eq] using ha
    apply (mem_upperUnipotent F g).mpr
    refine ⟨g.val 0 1, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transvection_coe, h10, h00, ← heq]
  · rintro g hg
    obtain ⟨a, rfl⟩ := (mem_upperUnipotent F g).mp hg
    apply mem_centralizer_iff.mpr
    intro x hx
    obtain ⟨b, rfl⟩ := (mem_upperUnipotent F x).mp hx
    rw [← transvection_add, ← transvection_add, add_comm]

end Theory.SpecificGroups.SL2.EvenBorel
