module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Restriction

/-!
# Separation of the unipotent and special-linear factors

Every product of a plane unipotent and the SL₂ Levi has bottom-right entry one
in the original coordinates. If its projective image is trivial, its scalar
representative is therefore the identity. Restriction to the marked plane
then kills the SL₂ factor, and faithfulness kills the unipotent factor.
This avoids any assumption that the full restriction kernel is exhausted.

Source: the standard unitary plane-parabolic calculation underlying
Aschbacher--Smith, *The Classification of Quasithin Groups*, F.1.12(7),
printed pp.263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

theorem unipotent_SL_middle (c : F) (u : Parameters J)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (Parameters.ambientGL u * planeLeviGL J c (planeSLtoGL A)).val 4 4 = 1 := by
  change ((Parameters.ambientGL u).val * (planeLeviGL J c (planeSLtoGL A)).val) 4 4 = 1
  rw [Parameters.ambientGL_val, planeLeviGL_val]
  simp [planeBasis, planeBasisInv, planeBlockMatrix, planeMiddleScalar,
    Parameters.ambientMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem unipotent_mul_SL_eq_one (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (u : Parameters J) (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : Parameters.toParabolic hJ u * planeSLParabolic J c hc hJ A = 1) :
    u = 1 ∧ A = 1 := by
  have hp : ProjGenLinGroup.mk (Parameters.ambientGL u *
      planeLeviGL J c (planeSLtoGL A)) = 1 := by
    have he := congrArg (fun g : planeParabolic J => g.val.val) h
    exact he
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨a, ha⟩ := hp
  have hm := congrArg (fun B : GL (Fin 5) F => B.val 4 4) ha
  have haone : a = 1 := by
    apply Units.ext
    simpa [unipotent_SL_middle] using hm
  subst a
  have hunit : Parameters.toStabilizer hJ u * planeSLStabilizer J c hc hJ A = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change Parameters.ambientGL u * planeLeviGL J c (planeSLtoGL A) = 1
    simpa using ha.symm
  have hu : planeRestriction J (Parameters.toStabilizer hJ u) = 1 :=
    parameters_le_ker_restriction J hJ ⟨u, rfl⟩
  have hr := congrArg (planeRestriction J) hunit
  have hA : planeSLtoGL A = 1 := by
    simpa [map_mul, hu, planeSLStabilizer] using hr
  have hAone : A = 1 := Subtype.ext (congrArg Units.val hA)
  refine ⟨?_, hAone⟩
  apply Parameters.toParabolic_injective hJ
  simpa [hAone] using h

end Theory.SpecificGroups.UnitaryFive.PlaneCore
