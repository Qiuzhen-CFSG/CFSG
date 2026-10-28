module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.UnitaryCandidates.Data

/-!
# Explicit unitary matrices matching both block generators

Two matrices over the computable field of nine elements preserve the identity
Hermitian form and have determinant one. Their compound matrices act, up to
sign, exactly like the two degree-252 block generators under the displayed
bijection of points. All inverse, unitary, determinant and action identities
are checked in Lean's kernel. Generation of the full projective unitary group
is deliberately not asserted here.

The candidate matrices and labeling were found by a GAP comparison of the
original block group with the exterior action of an explicitly generated
unitary matrix group. This search and its order/isomorphism calculations are
not used as proof oracles. The numerical witnesses are retained in
`ProjectiveComparison/source/unitary-candidate.json`; coefficients [x,y] mean
x+yi with i²=-1. Source: ATLAS U₄(3) numerical data (see `BlockData`), GLS3 §2.7,
and Aschbacher–Smith I.1.4(5), printed p.408.
-/

public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryCandidates
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open Atlas.Order20160A8.Bivectors UnitaryGeometry

set_option Elab.async false

private theorem form_adjoint (A : Matrix (Fin 4) (Fin 4) FiniteField.Nine) :
    (UnitaryFourThree.form 4).conjTranspose A = adjoint A := by
  funext i j
  change (UnitaryFourThree.form 4).conj (A j i) = star (A j i)
  rw [UnitaryFourThree.form_conj_cube, FiniteField.Nine.star_eq_cube]

/-- The first displayed matrix belongs to the actual identity-form SU₄(3). -/
noncomputable def first : (UnitaryFourThree.form 4).specialSubgroup := by
  refine ⟨⟨matrixFirst, adjoint matrixFirst, first_inverse, first_unitary⟩, ?_, ?_⟩
  · change (UnitaryFourThree.form 4).conjTranspose matrixFirst *
      (UnitaryFourThree.form 4).form * matrixFirst = (UnitaryFourThree.form 4).form
    rw [UnitaryFourThree.form_gram, mul_one, form_adjoint, first_unitary]
  · apply Units.ext
    exact first_det

/-- The second displayed matrix belongs to the same literal special unitary group. -/
noncomputable def second : (UnitaryFourThree.form 4).specialSubgroup := by
  refine ⟨⟨matrixSecond, adjoint matrixSecond, second_inverse, second_unitary⟩, ?_, ?_⟩
  · change (UnitaryFourThree.form 4).conjTranspose matrixSecond *
      (UnitaryFourThree.form 4).form * matrixSecond = (UnitaryFourThree.form 4).form
    rw [UnitaryFourThree.form_gram, mul_one, form_adjoint, second_unitary]
  · apply Units.ext
    exact second_det

@[simp] theorem first_val : first.val.val = matrixFirst := by rfl
@[simp] theorem second_val : second.val.val = matrixSecond := by rfl

/-- The first compound matrix has the required action on all 252 nonisotropic lines. -/
theorem first_action : ∀ i,
    exteriorMap first.val.val (point (labeling i)) =
        point (labeling (BlockAction.blockA i)) ∨
    exteriorMap first.val.val (point (labeling i)) =
        -point (labeling (BlockAction.blockA i)) := by
  simpa only [first_val] using matrixFirst_action

/-- The second compound matrix uses exactly the same labeling and signs. -/
theorem second_action : ∀ i,
    exteriorMap second.val.val (point (labeling i)) =
        point (labeling (BlockAction.blockB i)) ∨
    exteriorMap second.val.val (point (labeling i)) =
        -point (labeling (BlockAction.blockB i)) := by
  simpa only [second_val] using matrixSecond_action

/-- Only genuine projective generation remains to complete this fixed comparison. -/
noncomputable def comparisonOfGeneration
    (hgen : Subgroup.closure ({UnitaryFourThree.project 4 first,
      UnitaryFourThree.project 4 second} : Set (UnitaryFourThree.Carrier 4)) = ⊤) :
    GeneratorComparison where
  first := first
  second := second
  labeling := labeling
  generates := hgen
  first_action := first_action
  second_action := second_action

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryCandidates
