module

public import Theory.SpecificGroups.PSL3.CartanActions
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Generation by standard fixed groups and the PSL₃ unipotent subgroup

Coordinate reversal carries upper transvections to lower transvections.
Gaussian elimination therefore shows that the upper unitriangular subgroup
and this one matrix generate PSL₃. Reversal is fixed by inverse transpose,
by the Borel-preserving graph representative, and by every coefficient
field automorphism. Their actual fixed subgroups consequently generate
PSL₃ together with the marked unipotent subgroup.

Source: the matrix generation step for Aschbacher–Smith E.1.14(1), printed
p.214; the matrix actions are GLS3, §2.7. Arbitrary conjugates require a
separate argument retaining the marked unipotent subgroup.
-/

public section
open Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open scoped MatrixGroups
namespace Matrix.PSL3Even.NonbinaryCentralizer
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem upper_transvection_mem {i j : Fin 3} (hij : i < j) (a : F) :
    Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) a ∈ unipotentSL F := by
  rw [unipotentSL, Subgroup.mem_inf, mem_pointLocalSL_iff, mem_lineLocalSL_iff]
  have hijNat : i.val < j.val := hij
  fin_cases i <;> fin_cases j <;> simp_all [Matrix.SpecialLinearGroup.transvection_coe]

private theorem reversal_transvection {i j : Fin 3} (hij : i ≠ j) (a : F) :
    MulAut.conj (reversalSL F) (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection
        (show i.rev ≠ j.rev from fun h => hij (Fin.rev_injective h)) a := by
  have he (x : SL(3,F)) : MulAut.conj (reversalSL F) x =
      linearConjSL F (reversalGL F) x := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [linearConjSL_toGL]
    simp [MulAut.conj_apply, reversalSL_toGL]
  rw [he]
  apply Subtype.ext
  ext r s
  rw [reversal_conj_val]
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, Fin.rev_eq_iff, Fin.rev_rev]

/-- Upper unitriangular matrices and the coordinate reversal generate PSL₃. -/
theorem eq_top_of_unipotent_le_of_reversal_mem (H : Subgroup PSL(3,F))
    (hU : unipotent F ≤ H) (hw : projection F (reversalSL F) ∈ H) : H = ⊤ := by
  let K := H.comap (projection F)
  have hu : unipotentSL F ≤ K := fun x hx => hU (mem_map_of_mem _ hx)
  have hK : K = ⊤ := by
    apply top_unique
    intro x _
    apply Representation.OneCohomology.SLHigherNatural.transvection_induction
      (fun x => x ∈ K) ?_ (fun _ _ => K.mul_mem) x
    intro i j hij a
    by_cases hlt : i < j
    · exact hu (upper_transvection_mem hlt a)
    · have hrev : i.rev < j.rev := by
        simp only [Fin.lt_def, Fin.val_rev]
        omega
      have ht := hu (upper_transvection_mem hrev a)
      have hc := K.mul_mem (K.mul_mem hw ht) (K.inv_mem hw)
      change MulAut.conj (reversalSL F) _ ∈ K at hc
      simpa only [reversal_transvection, Fin.rev_rev] using hc
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := projection_surjective F x
  exact (show y ∈ K from hK ▸ mem_top y)

theorem graph_fixed_sup_unipotent : (graph F).fixedSubgroup ⊔ unipotent F = ⊤ :=
  eq_top_of_unipotent_le_of_reversal_mem _ le_sup_right
    (mem_sup_left ((MulAut.mem_fixedSubgroup _ _).mpr (graph_reversal F)))

theorem field_fixed_sup_unipotent (σ : F ≃+* F) :
    (fieldAction F σ).fixedSubgroup ⊔ unipotent F = ⊤ := by
  apply eq_top_of_unipotent_le_of_reversal_mem _ le_sup_right
  apply mem_sup_left
  rw [MulAut.mem_fixedSubgroup]
  change fieldAction F σ (QuotientGroup.mk (reversalSL F)) = QuotientGroup.mk _
  rw [fieldAction_mk]
  apply congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F))
  apply Subtype.ext
  ext i j
  change σ ((reversalSL F).val i j) = (reversalSL F).val i j
  fin_cases i <;> fin_cases j <;> simp [reversalSL, reversalGL]

/-- The Borel-preserving graph representative also fixes coordinate reversal. -/
theorem oppositionGraph_fixed_sup_unipotent :
    (oppositionGraph F).fixedSubgroup ⊔ unipotent F = ⊤ := by
  apply eq_top_of_unipotent_le_of_reversal_mem _ le_sup_right
  apply mem_sup_left
  rw [MulAut.mem_fixedSubgroup]
  have he : oppositionGraph F = MulAut.conj (projection F (reversalSL F)) * graph F := by
    rw [oppositionGraph, ← reversalSL_toGL, linearConj_toGL]
    rfl
  rw [he, MulAut.mul_apply, graph_reversal, MulAut.conj_apply]
  simp
end Matrix.PSL3Even.NonbinaryCentralizer
