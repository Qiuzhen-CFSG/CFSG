module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.Model
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineShears
public import Theory.GroupTheory.SolvableResidual

/-!+# Normal two-subgroups and the local residuals of the unitary-five model

The projective line shears give a concrete nontrivial normal two-subgroup
of the left parabolic for every model, including the parameter two. This
supplies the normal subgroup needed by the quasithin rank obstruction.

For the local calculations we fix the solvable residuals inside the two
parabolics and an actual three-dimensional special unitary matrix model.
The residuals are perfect by finiteness. Identifying them with the source
local groups, calculating their canonical cores and quotients, and proving
the common Sylow marking require additional parabolic calculations.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12, printed pp. 262--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

open BenderSuzuki.MatrixGroups

variable {q : ℕ} (M : Model q)

/-- A concrete projective shear subgroup of the line parabolic. -/
def leftNormalTwoSubgroup : Subgroup M.leftParabolic :=
  Theory.SpecificGroups.UnitaryFive.projectiveLineShears M.form

instance leftNormalTwoSubgroup_normal : M.leftNormalTwoSubgroup.Normal :=
  Theory.SpecificGroups.UnitaryFive.projectiveLineShears_normal M.form

theorem leftNormalTwoSubgroup_ne_bot : M.leftNormalTwoSubgroup ≠ ⊥ :=
  Theory.SpecificGroups.UnitaryFive.projectiveLineShears_ne_bot M.form M.matrix

theorem leftNormalTwoSubgroup_isPGroup : IsPGroup 2 M.leftNormalTwoSubgroup :=
  Theory.SpecificGroups.UnitaryFive.projectiveLineShears_isPGroup M.form

/-- The normal two-subgroup input to the embedding obstruction, without extra hypotheses. -/
theorem exists_left_normal_two_subgroup :
    ∃ Q : Subgroup M.leftParabolic, Q.Normal ∧ Q ≠ ⊥ ∧ IsPGroup 2 Q :=
  ⟨M.leftNormalTwoSubgroup, inferInstance, M.leftNormalTwoSubgroup_ne_bot,
    M.leftNormalTwoSubgroup_isPGroup⟩

/-- Only the odd-prime rank calculation remains in the parabolic embedding obstruction. -/
theorem field_size_eq_four_of_left_embedding
    {G : Type*} [Group G] [Finite G] (hG : IsQuasithin G)
    (f : M.leftParabolic →* G) (hf : Function.Injective f)
    (hq : Even q) (hq2 : 2 ≤ q)
    (hr : ∀ p : ℕ, p.Prime → p ∣ (q + 1) / Nat.gcd (q + 1) 5 →
      3 ≤ primeRank p M.leftParabolic) : q = 4 :=
  field_size_eq_four_of_embedding hG f hf M.leftNormalTwoSubgroup
    M.leftNormalTwoSubgroup_ne_bot M.leftNormalTwoSubgroup_isPGroup hq hq2 hr

/-- The left residual, as a subgroup of the line parabolic itself. -/
def leftLocal : Subgroup M.leftParabolic := Subgroup.solvableResidual M.leftParabolic

/-- The right residual, as a subgroup of the plane parabolic itself. -/
def rightLocal : Subgroup M.rightParabolic := Subgroup.solvableResidual M.rightParabolic

instance leftLocal_normal : M.leftLocal.Normal := by
  dsimp [leftLocal]
  infer_instance

instance rightLocal_normal : M.rightLocal.Normal := by
  dsimp [rightLocal]
  infer_instance

instance leftLocal_isPerfect : Group.IsPerfect M.leftLocal :=
  Subgroup.solvableResidual_isPerfect (G := M.leftParabolic)

instance rightLocal_isPerfect : Group.IsPerfect M.rightLocal :=
  Subgroup.solvableResidual_isPerfect (G := M.rightParabolic)

/-- The identity Hermitian form in dimension three, with the model's field involution. -/
def localUnitaryForm : HermitianForm 3 M.F where
  conj := M.form.conj
  conj_involutive := M.form.conj_involutive
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

/-- The actual SU₃ matrix group over the same quadratic field. -/
abbrev LocalUnitaryGroup := M.localUnitaryForm.specialSubgroup

/-- The actual PSL₂ matrix group over the quadratic field. -/
abbrev LocalLinearGroup := Matrix.ProjectiveSpecialLinearGroup (Fin 2) M.F

theorem localUnitaryForm_conjugation (x : M.F) : M.localUnitaryForm.conj x = x ^ q :=
  M.conjugation x

/-- At the source's exceptional parameter, the matrix field has order sixteen. -/
theorem local_field_card (M : Model 4) : Nat.card M.F = 16 := by
  simpa using M.card

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
