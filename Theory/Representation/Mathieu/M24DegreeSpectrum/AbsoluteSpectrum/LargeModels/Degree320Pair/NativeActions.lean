module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.CarrierMap

/-!
# Native degree-320 actions from the two independent certificates

The shared ATLAS presentation has a proved marked surjection onto the full
Witt-design M24. Injectivity identifies its carrier with native M24. The seven
row-matrix equations give a homomorphism from this presentation with generator
images `A.transpose` and `B.transpose`. Inverse transpose then gives a second
homomorphism, whose values at the inverse native generators are exactly `A`
and `B`. The matrix-to-linear-map equivalence supplies the required actions.

The literal `actorA` and `actorB` conventions in `Degree320Pair.Contracts` are
preserved. In particular, no relabeling or change of basis is assumed. The final
`ActionsExist` applications below retain the presentation and matrix certificates
as explicit premises; they do not assert unconditional existence.

Source: John Bray's ATLAS `M24G1-P1`,
https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/M24G1-P1, and the four degree-320
matrix files documented in `Degree320Pair/source/README.md`.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
open Sporadic.Mathieu Degrees12421792.NativeActions.Presentation

/-- Inversion and transposition each reverse products, so together they preserve them. -/
private def inverseTranspose {G : Type*} [Group G] {d : ℕ}
    (f : G →* Matrix (Fin d) (Fin d) (ZMod 2)) :
    G →* Matrix (Fin d) (Fin d) (ZMod 2) where
  toFun g := (f g⁻¹).transpose
  map_one' := by simp
  map_mul' g h := by simp [Matrix.transpose_mul]

/-- An actual representation of the full native M24 from carrier injectivity
and the seven equations on one literal degree-320 matrix pair. -/
def nativeRepresentation (variant : Bool)
    (hinj : Function.Injective toCarrier)
    (h : RowRelations (matrixA variant) (matrixB variant)) :
    Representation (ZMod 2) M24 Space :=
  let e : UniversalGroup ≃* M24 :=
    MulEquiv.ofBijective toCarrier ⟨hinj, toCarrier_surjective⟩
  let f := toMonoid (matrixA variant).transpose (matrixB variant).transpose h.transpose
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    ((inverseTranspose f).comp e.symm.toMonoidHom)

/-- The native action has the raw matrices at exactly the prescribed inverse generators. -/
theorem nativeRepresentation_realizes (variant : Bool)
    (hinj : Function.Injective toCarrier)
    (h : RowRelations (matrixA variant) (matrixB variant)) :
    Realizes variant (nativeRepresentation variant hinj h) := by
  let e : UniversalGroup ≃* M24 :=
    MulEquiv.ofBijective toCarrier ⟨hinj, toCarrier_surjective⟩
  have ha : e.symm a = PresentedGroup.of 0 := by
    apply e.injective
    exact (e.apply_symm_apply a).trans toCarrier_zero.symm
  have hb : e.symm b = PresentedGroup.of 1 := by
    apply e.injective
    exact (e.apply_symm_apply b).trans toCarrier_one.symm
  constructor
  · change LinearMap.toMatrix' (Matrix.toLinAlgEquiv'
      ((toMonoid (matrixA variant).transpose (matrixB variant).transpose h.transpose)
        ((e.symm a⁻¹)⁻¹)).transpose) = _
    rw [map_inv e.symm a, inv_inv, ha, toMonoid_zero, Matrix.transpose_transpose]
    exact LinearMap.toMatrix'_toLin' _
  · change LinearMap.toMatrix' (Matrix.toLinAlgEquiv'
      ((toMonoid (matrixA variant).transpose (matrixB variant).transpose h.transpose)
        ((e.symm b⁻¹)⁻¹)).transpose) = _
    rw [map_inv e.symm b, inv_inv, hb, toMonoid_one, Matrix.transpose_transpose]
    exact LinearMap.toMatrix'_toLin' _

/-- Supply exactly the action premise of `pair320_of_certificates` from the
shared carrier comparison and the independent degree-320 matrix checks. -/
theorem actionsExist_of_relations (hinj : Function.Injective toCarrier)
    (h : MatrixRelations) : ActionsExist :=
  fun variant => ⟨nativeRepresentation variant hinj (h variant),
    nativeRepresentation_realizes variant hinj (h variant)⟩

/-- A finite bound on the genuine abstract presentation discharges the carrier
comparison. The two certificate producers must still supply these premises. -/
theorem actionsExist_of_presentation_bound
    (hbound : Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 244823040)
    (h : MatrixRelations) : ActionsExist :=
  actionsExist_of_relations (toCarrier_injective_of_bound hbound) h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
