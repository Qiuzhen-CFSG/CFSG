module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
public import CFSG.Quasithin.Chapter13.Section05.SourceDefs
public import Theory.GroupTheory.Recognition.UnitaryFourThree.Recognition
/-!
# The U₄(3) conclusion in the original natural normal branch

The original natural setup and the nine source conclusions of 13.5.15,
in the M=L branch, construct the unchanged Asc94 IsType configuration.
Recognition identifies the literal field-nine projective unitary carrier.
This gives the existing ModelConclusion of 13.5.12 for n=6. The earlier
13.5.15 conclusions and the branch selection remain source hypotheses;
no returning intersection, graph comparison or recognition is assumed.
Source: Aschbacher–Smith,13.5.16, p.921; Asc94,45.11, pp.248–249.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
open Theory.GroupTheory.Recognition Section08.SourceCompletion
open Theory.SpecificGroups.ClassicalUnitary
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G} {g : G}

theorem equiv_native_of_natural_normal_branch
    (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
    (h : D.Hypothesis) (b : Conclusions D M 6 g) (hM : M=D.L) :
    Nonempty (G≃*UnitaryFourThree.Carrier 4) := by
  obtain ⟨z,hz,-⟩ := (Nat.card_eq_two_iff' (1:D.V₁)).mp h.point_card
  exact (isType_of_natural_normal_branch d h b hM z.val z.property
    (fun he=>hz (Subtype.ext he))).equiv_native

theorem isPSU_of_natural_normal_branch
    (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
    (h : D.Hypothesis) (b : Conclusions D M 6 g) (hM : M=D.L) :
    ClassicalGroup.IsPSU G 4 3 := by
  exact ⟨FiniteField.Nine,inferInstance,inferInstance,UnitaryFourThree.form 4,
    (by rw [FiniteField.Nine.natCard]; decide),UnitaryFourThree.form_conj_cube 4,
    equiv_native_of_natural_normal_branch d h b hM⟩

theorem modelConclusion_of_natural_normal_branch
    (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
    (h : D.Hypothesis) (b : Conclusions D M 6 g) (hM : M=D.L) :
    ModelConclusion G 6 :=
  Or.inr ⟨rfl,isPSU_of_natural_normal_branch d h b hM⟩
end CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
