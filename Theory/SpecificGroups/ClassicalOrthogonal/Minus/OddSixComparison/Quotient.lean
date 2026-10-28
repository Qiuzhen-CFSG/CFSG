module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Realization
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.ScalarKernel
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The two scalar kernels in the minus-six exterior comparison

The exterior action itself kills exactly the square-one scalar matrices.
After passage to the original orthogonal scalar quotient, its kernel is
exactly the kernel of SU₄ → PSU₄. This second kernel may be larger in odd
characteristic. The proof uses scalar rigidity of the exterior square and
spanning of the actual descended coordinates. The reverse implication uses
determinant one: a scalar SU₄ matrix has fourth power one, so its exterior
scalar is 1 or -1 and belongs to the original coefficient field.

Thus any surjective projective exterior action gives the required equivalence
on the literal projective carriers. Geometry and the image theorem remain
explicit; this module does not assert the source exceptional isomorphism.
Source: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open Matrix BenderSuzuki.MatrixGroups Atlas.Order20160A8.Bivectors
open Theory.SpecificGroups.ClassicalUnitary

variable {F E : Type} [Field F] [Finite F] [Field E]
variable {J : HermitianForm 4 E} (R : ExteriorRealization F E J)

/-- The exterior action has the square-one scalar kernel, before projectivizing. -/
theorem ExteriorRealization.action_eq_one_iff (g : J.specialSubgroup) :
    R.action g = 1 ↔ ∃ a : E, a ^ 2 = 1 ∧ g.val.val = a • 1 := by
  constructor
  · intro hg
    apply scalar_of_exteriorMap_eq_id
    have hs := (R.scalar_action_iff g 1).mp (by
      intro v
      rw [hg]
      simp)
    simpa only [map_one, one_smul] using hs
  · rintro ⟨a, ha, hg⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hs := (R.scalar_action_iff g 1).mpr (by
      intro w
      rw [hg, exteriorMap_scalar, ha]
      simp)
    change (R.action g).val v = v
    simpa only [one_smul] using hs v

/-- The literal projection into PGL kills precisely scalar special unitary matrices. -/
theorem unitary_project_eq_one_iff_scalar (g : J.specialSubgroup) :
    UnitaryFourFlag.project E J g = 1 ↔ ∃ a : E, g.val.val = a • 1 := by
  constructor
  · intro hg
    have hz := ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val hg)
    obtain ⟨a, ha⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hz
    exact ⟨a, by simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using ha.symm⟩
  · rintro ⟨a, ha⟩
    apply Subtype.ext
    apply ProjGenLinGroup.mk_eq_one.mpr
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    exact ⟨a, by simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using ha.symm⟩

variable (hcomm : ∀ g, R.action g ∈ commutator (FullOrthogonal F))

/-- The actual descended action with its proved commutator membership. -/
def ExteriorRealization.omegaAction : J.specialSubgroup →*
    Omega F (Space F 2) (quadraticForm F 3) :=
  R.action.codRestrict _ hcomm

/-- The commutator map retains the original full-isometry representative. -/
@[simp] theorem ExteriorRealization.omegaAction_val (g : J.specialSubgroup) :
    (R.omegaAction hcomm g).val = R.action g := by rfl

/-- The original orthogonal scalar quotient, applied to the exterior action. -/
def ExteriorRealization.projectiveAction : J.specialSubgroup →* ClassicalGroup.POmegaMinus 3 F :=
  (QuotientGroup.mk' (scalarSubgroup F (Space F 2) (quadraticForm F 3))).comp
    (R.omegaAction hcomm)

/-- Evaluation uses precisely the original orthogonal scalar quotient map. -/
@[simp] theorem ExteriorRealization.projectiveAction_apply (g : J.specialSubgroup) :
    R.projectiveAction hcomm g =
      QuotientGroup.mk' (scalarSubgroup F (Space F 2) (quadraticForm F 3))
        (R.omegaAction hcomm g) := by rfl

/-- The two actual projective maps have exactly the same kernel. -/
theorem ExteriorRealization.projectiveAction_eq_one_iff (g : J.specialSubgroup) :
    R.projectiveAction hcomm g = 1 ↔ UnitaryFourFlag.project E J g = 1 := by
  change QuotientGroup.mk' _ (R.omegaAction hcomm g) = 1 ↔ _
  rw [projectiveOmega_mk_eq_one_iff, unitary_project_eq_one_iff_scalar]
  constructor
  · rintro ⟨c, hc⟩
    have hs := (R.scalar_action_iff g (c : F)).mp hc
    obtain ⟨a, _, ha⟩ := scalar_of_exteriorMap_scalar g.val.val
      (R.coefficient (c : F)) (by
        intro hz
        apply Units.ne_zero c
        apply R.coefficient.injective
        simpa only [map_zero] using hz) hs
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    have hd : a ^ 4 = 1 := by
      have h := congrArg Units.val g.property.2
      change g.val.val.det = 1 at h
      rw [ha, Matrix.det_smul] at h
      simpa using h
    have hs : a ^ 2 = 1 ∨ a ^ 2 = -1 := sq_eq_one_iff.mp (by
      simpa only [← pow_mul] using hd)
    rcases hs with hs | hs
    · refine ⟨1, ?_⟩
      apply (R.scalar_action_iff g 1).mpr
      intro w
      rw [ha, exteriorMap_scalar, hs]
      simp
    · refine ⟨-1, ?_⟩
      apply (R.scalar_action_iff g (-1)).mpr
      intro w
      rw [ha, exteriorMap_scalar, hs]
      simp

/-- Kernel equality retains the literal orthogonal and unitary projective maps. -/
theorem ExteriorRealization.projectiveAction_ker :
    (R.projectiveAction hcomm).ker = (UnitaryFourFlag.project E J).ker := by
  ext g
  exact R.projectiveAction_eq_one_iff hcomm g

/-- A surjective projective exterior action identifies the exact projective carriers. -/
def ExteriorRealization.projectiveEquiv_of_surjective
    (hsurj : Function.Surjective (R.projectiveAction hcomm)) :
    ClassicalGroup.POmegaMinus 3 F ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  (QuotientGroup.quotientKerEquivOfSurjective (R.projectiveAction hcomm) hsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (R.projectiveAction_ker hcomm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (UnitaryFourFlag.project E J)
        (UnitaryFourFlag.project_surjective E J)))

/-- The comparison sends each actual exterior representative to its PSU class. -/
@[simp] theorem ExteriorRealization.projectiveEquiv_of_surjective_apply
    (hsurj : Function.Surjective (R.projectiveAction hcomm)) (g : J.specialSubgroup) :
    R.projectiveEquiv_of_surjective hcomm hsurj (R.projectiveAction hcomm g) =
      UnitaryFourFlag.project E J g := by
  have h : QuotientGroup.quotientKerEquivOfSurjective (R.projectiveAction hcomm) hsurj
      (QuotientGroup.mk g) = R.projectiveAction hcomm g := rfl
  rw [← h]
  simp only [ExteriorRealization.projectiveEquiv_of_surjective, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- Inherited simplicity reduces the image obligation to normality and nontriviality
in the original projective carrier; simplicity of its central cover is not used. -/
theorem ExteriorRealization.projectiveAction_surjective_of_normal
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)]
    (hN : (R.projectiveAction hcomm).range.Normal)
    (hne : (R.projectiveAction hcomm).range ≠ ⊥) :
    Function.Surjective (R.projectiveAction hcomm) :=
  MonoidHom.range_eq_top.mp (hN.eq_bot_or_eq_top.resolve_left hne)

end ClassicalOrthogonal.Minus.OddSixComparison
