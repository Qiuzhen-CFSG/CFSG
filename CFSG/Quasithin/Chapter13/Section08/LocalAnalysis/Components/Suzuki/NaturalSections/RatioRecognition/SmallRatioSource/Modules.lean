module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions.Irreducible
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Natural
public import Theory.Representation.OrthogonalNatural
public import Theory.Representation.MathieuCodeRestriction.M22.Construction
public import Theory.Representation.SemilinearConjugation
public import Theory.Representation.ExtendScalars
public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.Mathieu.M12.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2

/-!+# Module data in B.4.5

The orthogonal row uses the four-dimensional minus quadratic space, and
the unitary row uses SU, not its projective image: K.3.3 identifies the
faithful actor with the universal group. The M₂₂ cocode is the dual of the
actual ten-dimensional code, as in H.13.1. Clause (iii)(a) records the
scalar field as the full commuting endomorphism ring, the quadratic field
extension, and an intertwiner after extension of scalars to the tensor of
the natural symplectic action and its Galois conjugate.

These are conclusions to be constructed by the classification theorem,
not extra assumptions on the actions to which that theorem applies.

Source: Aschbacher–Smith, B.4.5, printed p.87; H.13.1, p.395;
K.3.1–4, pp.453–457. K.3.6, p.457 (and the paragraph immediately before
K.3.5), explicitly justifies the natural Suzuki module assertion.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open BenderSuzuki.MatrixGroups
open scoped TensorProduct

namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

universe u v

/-- The actual four-dimensional minus orthogonal module over the smaller field. -/
def orthogonalFour (K : BinaryField) :=
  restrictScalars (k := ZMod 2)
    (ClassicalOrthogonal.Minus.projectiveOmegaNatural
      (ClassicalOrthogonal.Minus.quadraticForm K.Carrier 2)
      (ClassicalOrthogonal.Minus.quadraticForm_represents_one (F := K.Carrier) 2))

/-- The defining SU₃ action, with binary scalars. Its actor retains the center. -/
def unitaryThree (F : BinaryField) (J : HermitianForm 3 F.Carrier) :=
  restrictScalars (k := ZMod 2)
    ((generalLinearNatural 3).comp J.specialSubgroup.subtype)

/-- H.13.1 identifies the ten-dimensional cocode with the dual code action. -/
def m22Cocode := MathieuCode.m22CodeRepresentation.dual

/-- Apply the field automorphism to the natural symplectic matrices. -/
def conjugateSymplectic (F : BinaryField) (σ : F.Carrier ≃+* F.Carrier) :=
  semilinearConjugate σ (symplecticNatural (k := F.Carrier) 2)
    (coordinateSemilinearEquiv σ (Fin 2 ⊕ Fin 2))

variable {L : Type u} [Group L] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) L V)

/-- The entire scalar-extension/descent assertion in B.4.5(iii)(a).
`commutant` says exactly that every binary L-endomorphism is a unique
K-scalar. The original binary action is the restriction of `overK`, and
`intertwines` identifies its scalar extension with N tensor N^σ using
one actor equivalence. No dimension equality stands in for this assertion. -/
structure SymplecticTensorDescent where
  K : BinaryField
  F : BinaryField
  [extension : Algebra K.Carrier F.Carrier]
  [scalarTower : IsScalarTower (ZMod 2) K.Carrier F.Carrier]
  field_degree : F.degree = 2 * K.degree
  sigma : F.Carrier ≃ₐ[K.Carrier] F.Carrier
  sigma_frobenius : ∀ x, sigma x = x ^ (2 ^ K.degree)
  sigma_ne_one : sigma ≠ 1
  galois : ∀ τ : F.Carrier ≃ₐ[K.Carrier] F.Carrier, τ = 1 ∨ τ = sigma
  [moduleK : Module K.Carrier V]
  [moduleTower : IsScalarTower (ZMod 2) K.Carrier V]
  overK : Representation K.Carrier L V
  restriction : restrictScalars (k := ZMod 2) overK = ρ
  commutant : ∀ f : Module.End (ZMod 2) V,
    (∀ g v, f (ρ g v) = ρ g (f v)) ↔ ∃! c : K.Carrier, ∀ v, f v = c • v
  actor : L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier
  descent : (F.Carrier ⊗[K.Carrier] V) ≃ₗ[F.Carrier]
    (((Fin 2 ⊕ Fin 2) → F.Carrier) ⊗[F.Carrier] ((Fin 2 ⊕ Fin 2) → F.Carrier))
  intertwines : ∀ g v, descent (extendScalars F.Carrier overK g v) =
    ((symplecticNatural (k := F.Carrier) 2).tprod
      (conjugateSymplectic F sigma.toRingEquiv)) (actor g) (descent v)

attribute [instance] SymplecticTensorDescent.extension SymplecticTensorDescent.scalarTower
  SymplecticTensorDescent.moduleK SymplecticTensorDescent.moduleTower

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
