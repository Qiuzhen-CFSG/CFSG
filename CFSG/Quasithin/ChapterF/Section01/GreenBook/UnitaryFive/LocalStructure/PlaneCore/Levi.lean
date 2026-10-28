module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.PlaneCore.Basic
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourFormTransport

/-!
# The plane Levi decomposition in the marked U₅(4) model

The field and Frobenius data supply a trace-one scalar, hence a hyperbolic
basis and a GL₂ section of the exact SU plane restriction. Its special-linear
part embeds faithfully into the projective right parabolic. The full unipotent
kernel is normal, and its quotient is GL₂ modulo scalar fifth roots, with a
faithful section. The unipotent--SL₂ subgroup is the geometric semidirect product,
normal of index three in the full parabolic. The actual flag overlap has index
seventeen. Identification of that subgroup with the residual still requires
perfection and is left to the residual assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12(7), printed pp.263--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive Matrix
variable (M : Model 4)

/-- The actual Frobenius involution admits the hyperbolic basis correction. -/
theorem right_exists_trace_one : ∃ c : M.F, c + M.form.conj c = 1 := by
  exact BenderSuzuki.External.huppert_II_10_4_trace_surjective M.form 4
    M.local_field_card (fixed_card_four M.form M.local_field_card M.conjugation)
    1 (map_one _)

/-- A fixed choice makes the Levi embeddings and their generated subgroup coherent. -/
noncomputable def rightLeviTrace : M.F := Classical.choose M.right_exists_trace_one

theorem rightLeviTrace_spec : M.rightLeviTrace + M.form.conj M.rightLeviTrace = 1 :=
  Classical.choose_spec M.right_exists_trace_one

/-- Restriction to the marked plane in its given ordered coordinates. -/
abbrev rightPlaneRestriction : specialStabilizer M.form (plane M.F) →* GL (Fin 2) M.F :=
  PlaneCore.planeRestriction M.form

/-- The full GL₂ Levi section of the exact SU plane stabilizer. -/
noncomputable def rightLeviStabilizer :
    GL (Fin 2) M.F →* specialStabilizer M.form (plane M.F) :=
  PlaneCore.planeLeviStabilizer M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

@[simp] theorem rightPlaneRestriction_section (A : GL (Fin 2) M.F) :
    M.rightPlaneRestriction (M.rightLeviStabilizer A) = A :=
  PlaneCore.planeRestriction_section M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix A

theorem rightPlaneRestriction_surjective : Function.Surjective M.rightPlaneRestriction :=
  PlaneCore.planeRestriction_surjective M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

/-- The projective full Levi; its scalar kernel is treated separately. -/
noncomputable def rightLevi : GL (Fin 2) M.F →* M.rightParabolic :=
  PlaneCore.planeLeviParabolic M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

/-- The full projective Levi loses exactly the scalar fifth roots. -/
theorem rightLevi_ker : M.rightLevi.ker = PlaneCore.planeScalarRoots (F := M.F) :=
  PlaneCore.planeLeviParabolic_ker M.form M.rightLeviTrace M.rightLeviTrace_spec
    M.matrix M.conjugation

/-- The Levi image is the general linear group modulo that scalar subgroup. -/
noncomputable def rightLeviImageEquiv :
    (GL (Fin 2) M.F ⧸ PlaneCore.planeScalarRoots (F := M.F)) ≃* M.rightLevi.range :=
  PlaneCore.planeLeviImageEquiv M.form M.rightLeviTrace M.rightLeviTrace_spec
    M.matrix M.conjugation

theorem rightLevi_scalar_card : Nat.card (PlaneCore.planeScalarRoots (F := M.F)) = 5 :=
  PlaneCore.planeScalarRoots_card M.local_field_card

/-- The embedded special-linear Levi. -/
noncomputable def rightSLLevi : SpecialLinearGroup (Fin 2) M.F →* M.rightParabolic :=
  PlaneCore.planeSLParabolic M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

theorem rightSLLevi_injective : Function.Injective M.rightSLLevi :=
  PlaneCore.planeSLParabolic_injective M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

/-- The concrete radical--SL₂ subgroup, before residual identification. -/
noncomputable def rightRadicalLevi : Subgroup M.rightParabolic :=
  PlaneCore.planeRadicalLevi M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

theorem rightRadicalLevi_eq :
    M.rightRadicalLevi = M.rightUnipotent ⊔ M.rightSLLevi.range := rfl

/-- The entire SU restriction kernel is the constructed parameter image. -/
theorem rightPlaneRestriction_ker :
    M.rightPlaneRestriction.ker = (PlaneCore.Parameters.toStabilizer M.matrix).range :=
  PlaneCore.ker_planeRestriction M.form M.matrix

/-- Normality in the full right parabolic. -/
instance rightUnipotent_normal : M.rightUnipotent.Normal :=
  PlaneCore.projectiveUnipotent_normal M.form M.matrix

/-- Every element of the full right parabolic has a unipotent--GL₂ factorization. -/
theorem rightParabolic_factorization (g : M.rightParabolic) :
    ∃ (u : M.RightUnipotentParameters) (A : GL (Fin 2) M.F),
      g = PlaneCore.Parameters.toParabolic M.matrix u * M.rightLevi A :=
  PlaneCore.planeParabolic_factorization M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix g

/-- Restriction with precisely the projective scalar ambiguity removed. -/
noncomputable def rightProjectiveRestriction :
    M.rightParabolic →* (GL (Fin 2) M.F ⧸ PlaneCore.planeScalarRoots (F := M.F)) :=
  PlaneCore.planeProjectiveRestriction M.form

theorem rightProjectiveRestriction_surjective : Function.Surjective M.rightProjectiveRestriction :=
  PlaneCore.planeProjectiveRestriction_surjective M.form M.rightLeviTrace
    M.rightLeviTrace_spec M.matrix

theorem rightProjectiveRestriction_ker : M.rightProjectiveRestriction.ker = M.rightUnipotent :=
  PlaneCore.planeProjectiveRestriction_ker M.form M.rightLeviTrace M.rightLeviTrace_spec
    M.matrix M.conjugation

/-- The quotient of the whole parabolic by the actual unipotent subgroup. -/
noncomputable def rightParabolicQuotientEquiv :
    (M.rightParabolic ⧸ M.rightUnipotent) ≃*
      (GL (Fin 2) M.F ⧸ PlaneCore.planeScalarRoots (F := M.F)) :=
  PlaneCore.planeParabolicQuotientEquiv M.form M.rightLeviTrace M.rightLeviTrace_spec
    M.matrix M.conjugation

/-- The faithful full projective Levi section. -/
noncomputable def rightProjectiveLevi :
    (GL (Fin 2) M.F ⧸ PlaneCore.planeScalarRoots (F := M.F)) →* M.rightParabolic :=
  PlaneCore.planeProjectiveLevi M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix M.conjugation

@[simp] theorem rightProjectiveRestriction_section
    (q : GL (Fin 2) M.F ⧸ PlaneCore.planeScalarRoots (F := M.F)) :
    M.rightProjectiveRestriction (M.rightProjectiveLevi q) = q :=
  PlaneCore.planeProjectiveRestriction_section M.form M.rightLeviTrace M.rightLeviTrace_spec
    M.matrix M.conjugation q

theorem rightProjectiveLevi_injective : Function.Injective M.rightProjectiveLevi :=
  PlaneCore.planeProjectiveLevi_injective M.form M.rightLeviTrace M.rightLeviTrace_spec
    M.matrix M.conjugation

/-- The coordinate action is implemented by the actual embedded SL₂ matrices. -/
theorem rightSLLevi_conjugation (A : SpecialLinearGroup (Fin 2) M.F)
    (u : M.RightUnipotentParameters) :
    M.rightSLLevi A * PlaneCore.Parameters.toParabolic M.matrix u * (M.rightSLLevi A)⁻¹ =
      PlaneCore.Parameters.toParabolic M.matrix (PlaneCore.Parameters.planeAction A u) :=
  PlaneCore.Parameters.planeSLParabolic_conjugation M.rightLeviTrace M.rightLeviTrace_spec
    M.matrix A u

/-- The generated radical--SL₂ subgroup, with its geometric multiplication map. -/
noncomputable def rightRadicalLeviEquiv : PlaneCore.PlaneSemidirect M.form ≃* M.rightRadicalLevi :=
  PlaneCore.planeRadicalLeviEquiv M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

@[simp] theorem rightRadicalLeviEquiv_val (p : PlaneCore.PlaneSemidirect M.form) :
    (M.rightRadicalLeviEquiv p).val =
      PlaneCore.Parameters.toParabolic M.matrix p.left * M.rightSLLevi p.right := rfl

/-- The special-linear factor projection on the actual generated subgroup. -/
noncomputable def rightRadicalLeviProjection :
    M.rightRadicalLevi →* SpecialLinearGroup (Fin 2) M.F :=
  PlaneCore.planeRadicalLeviProjection M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

theorem rightRadicalLeviProjection_surjective :
    Function.Surjective M.rightRadicalLeviProjection :=
  PlaneCore.planeRadicalLeviProjection_surjective M.form M.rightLeviTrace
    M.rightLeviTrace_spec M.matrix

theorem rightRadicalLeviProjection_ker :
    M.rightRadicalLeviProjection.ker = M.rightUnipotent.subgroupOf M.rightRadicalLevi :=
  PlaneCore.planeRadicalLeviProjection_ker M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

/-- The abelian quotient measuring the difference between K and the full parabolic. -/
noncomputable def rightParabolicDeterminant : M.rightParabolic →* (M.Fˣ ⧸ rootsOfUnity 5 M.F) :=
  PlaneCore.planeParabolicDeterminant M.form

theorem rightParabolicDeterminant_surjective : Function.Surjective M.rightParabolicDeterminant :=
  PlaneCore.planeParabolicDeterminant_surjective M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

theorem rightParabolicDeterminant_ker : M.rightParabolicDeterminant.ker = M.rightRadicalLevi :=
  PlaneCore.planeParabolicDeterminant_ker M.form M.rightLeviTrace M.rightLeviTrace_spec
    M.matrix M.conjugation

/-- K is normal inside the full plane parabolic. -/
instance rightRadicalLevi_normal : M.rightRadicalLevi.Normal :=
  PlaneCore.planeRadicalLevi_normal M.form M.rightLeviTrace M.rightLeviTrace_spec
    M.matrix M.conjugation

theorem rightRadicalLevi_index : M.rightRadicalLevi.index = 3 :=
  PlaneCore.planeRadicalLevi_index M.form M.local_field_card M.rightLeviTrace
    M.rightLeviTrace_spec M.matrix M.conjugation

/-- The actual flag overlap has seventeen cosets in the plane parabolic. -/
theorem overlap_rightParabolic_index : (M.overlap.subgroupOf M.rightParabolic).index = 17 :=
  PlaneCore.plane_flag_index_seventeen M.form M.local_field_card M.rightLeviTrace
    M.rightLeviTrace_spec M.matrix

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
