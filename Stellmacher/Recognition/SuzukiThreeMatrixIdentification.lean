module

public import Theory.SpecificGroups.UnitaryThree.MatrixGroup
public import Theory.SpecificGroups.UnitaryThree.MatrixModel
public import Stellmacher.Recognition.PSU3ThreeCoordinates
public import Stellmacher.Recognition.PSU3ThreeProjective

/-!
# Concrete Hermitian models and the standard projective unitary group

All special isometries of the anti-diagonal form over the computable field
`Nine` identify with the full group `PGU3Three`. The explicit isotropic basis
changes the form to the identity, and the finite-field equivalence transports
quadratic conjugation to cube Frobenius. Every special unitary matrix over
`GaloisField 3 2` lifts back through this coefficient equivalence. The projective
map is injective since determinant-one scalar matrices are trivial in dimension
three and characteristic three. Finally PGU₃(3) equals PSU₃(3).

The faithful matrix action identifies this full matrix group with the concrete
permutation model: the matrix generators act as its defining generators, and
they generate every special isometry. Composing gives `modelEquivPGU`, an
isomorphism onto the full standard projective unitary group.

Source: Suzuki, J. Algebra 2 (1965), Section VI, and the scalar adjustment in
`PSU3ThreeProjective`.
-/

public section

open Matrix FiniteField BenderSuzuki.MatrixGroups
namespace Stellmacher.Recognition
namespace SuzukiThreeMatrix

local notation "E" => GaloisField 3 2
local notation "J" => ABG.unitaryForm 3 3 1 (by decide)

private theorem map_conjTranspose (A : Matrix (Fin 3) (Fin 3) Nine) :
    (J).conjTranspose (A.map Nine.equivGaloisField) =
      Aᴴ.map Nine.equivGaloisField := by
  ext i j
  change iterateFrobeniusEquiv E 3 1 (Nine.equivGaloisField (A j i)) =
    Nine.equivGaloisField (star (A j i))
  rw [Nine.equivGaloisField_star]
  simp [frobenius_def]

/-- Coefficient transport detects the full unitary equation in either direction. -/
theorem coefficient_isometry_iff (A : Matrix (Fin 3) (Fin 3) Nine) :
    (J).conjTranspose (A.map Nine.equivGaloisField) *
      A.map Nine.equivGaloisField = 1 ↔ Aᴴ * A = 1 := by
  rw [map_conjTranspose, ← Matrix.map_mul]
  have hone : (1 : Matrix (Fin 3) (Fin 3) E) =
      (1 : Matrix (Fin 3) (Fin 3) Nine).map Nine.equivGaloisField :=
    Nine.equivGaloisField.toRingHom.mapMatrix.map_one.symm
  rw [hone]
  exact (Matrix.map_injective Nine.equivGaloisField.injective).eq_iff

/-- The standard projective map on the full concrete identity-form group. -/
noncomputable def identityToPSU : UnitaryThree.identityMatrixGroup →*
    ABG.PSU3 3 1 (by decide) :=
  PSU3Three.lift UnitaryThree.identityMatrixGroup.subtype (fun A =>
    (UnitaryThree.mem_identityMatrixGroup A.val).mp A.property)

theorem identityToPSU_injective : Function.Injective identityToPSU :=
  PSU3Three.lift_injective _ _ Subtype.val_injective

/-- Every projective special unitary element has a preimage over `Nine`. -/
theorem identityToPSU_surjective : Function.Surjective identityToPSU := by
  intro g
  obtain ⟨A, hA, he⟩ := g.property
  obtain ⟨hunit, hdet⟩ := (HermitianForm.mem_specialSubgroup_iff _ _).mp hA
  let B : SpecialLinearGroup (Fin 3) E := ⟨(A : Matrix (Fin 3) (Fin 3) E), by
    have hd := congrArg (fun d : Eˣ => (d : E)) hdet
    exact hd⟩
  let C : UnitaryThree.SL := SpecialLinearGroup.map Nine.equivGaloisField.symm.toRingHom B
  have hcoeff : C.val.map Nine.equivGaloisField = (A : Matrix (Fin 3) (Fin 3) E) := by
    ext i j
    exact Nine.equivGaloisField.apply_symm_apply (A.val i j)
  have hC : C ∈ UnitaryThree.identityMatrixGroup := by
    rw [UnitaryThree.mem_identityMatrixGroup]
    apply (coefficient_isometry_iff C.val).mp
    rw [hcoeff]
    simpa only [ABG.unitaryForm, mul_one] using hunit
  refine ⟨⟨C, hC⟩, ?_⟩
  apply Subtype.ext
  trans PSU3Three.projectiveMap C
  · exact PSU3Three.lift_coe _ _ (⟨C, hC⟩ : UnitaryThree.identityMatrixGroup)
  rw [← he, PSU3Three.projectiveMap_apply]
  apply congrArg ProjGenLinGroup.mk
  exact Units.ext hcoeff

/-- The full identity-form special unitary group, with no image restriction. -/
noncomputable def identityEquivPSU : UnitaryThree.identityMatrixGroup ≃*
    ABG.PSU3 3 1 (by decide) :=
  MulEquiv.ofBijective identityToPSU ⟨identityToPSU_injective, identityToPSU_surjective⟩

/-- The full anti-diagonal special unitary matrix group is PGU₃(3). -/
noncomputable def matrixEquivPGU : UnitaryThree.matrixGroup ≃* PGU3Three :=
  (UnitaryThree.matrixEquivIdentity.trans identityEquivPSU).trans
    pgu3ThreeEquivPSU3Three.symm

/-- The concrete permutation model is the full projective unitary group PGU₃(3). -/
noncomputable def modelEquivPGU : UnitaryThree.Model ≃* PGU3Three :=
  UnitaryThree.matrixEquivModel.symm.trans matrixEquivPGU

/-- Existence of the permutation-model identification, for recognition assembly. -/
theorem model_nonempty_equiv_pgu3Three : Nonempty (UnitaryThree.Model ≃* PGU3Three) :=
  ⟨modelEquivPGU⟩

end SuzukiThreeMatrix
end Stellmacher.Recognition
end
