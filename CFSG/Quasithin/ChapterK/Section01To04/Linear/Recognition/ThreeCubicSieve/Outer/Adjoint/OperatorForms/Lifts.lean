module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Forms

/-!+# Actual semilinear lifts of the projective component action

This interface separates construction of adjoint intertwiners from elimination
of the scalar and coefficient factors. Both intertwining identities use the
same automorphism of the literal central quotient SL₃/Z(SL₃). Thus an SL₃
central kernel is allowed, and no arbitrary lift of a projective automorphism
to the covering group is assumed.

The assembly in `OperatorForms` proves that the quotient of these two operators
is a scalar, removes coefficient transport using Schur linearity, and removes
the scalar using the involution equation. Existence of the lifts below is a
separate prerequisite; this module asserts no automorphism or operator coverage.

Source: GM, Proposition 4.8, step 3A; GLS III, §2.7, actual matrix automorphisms.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)

/-- A standard semilinear adjoint operator inducing exactly the same projective
component action as the given normalizer element. -/
structure SemilinearLift (t : linearNormalizer σ) where
  quotientAction : MulAut PSL(3,B.Carrier)
  equiv : AdjointSpace B.Carrier ≃ₗ[ZMod 2] AdjointSpace B.Carrier
  conjugator : GL (Fin 3) B.Carrier
  coefficient : B.Carrier ≃+* B.Carrier
  scalar_action : ∀ (c : B.Carrier) (x : AdjointSpace B.Carrier),
    equiv (c • x) = coefficient c • equiv x
  matrix_action :
    (∀ x : AdjointSpace B.Carrier, LinearMap.toMatrix' (equiv x).val =
      conjugator.val * (LinearMap.toMatrix' x.val).map coefficient * conjugator.inv) ∨
    (∀ x : AdjointSpace B.Carrier, LinearMap.toMatrix' (equiv x).val =
      conjugator.val * ((LinearMap.toMatrix' x.val).map coefficient).transpose *
        conjugator.inv)
  original_action : ∀ (l h : SL(3,B.Carrier)),
    quotientAction (QuotientGroup.mk l) = QuotientGroup.mk h →
      ∀ v : V, t.val.val (σ l v) = σ h (t.val.val v)
  adjoint_action : ∀ (l h : SL(3,B.Carrier)),
    quotientAction (QuotientGroup.mk l) = QuotientGroup.mk h →
      ∀ x : AdjointSpace B.Carrier,
        equiv (binaryRep B l x) = binaryRep B h (equiv x)

/-- The outstanding construction, with the actual binary adjoint marking as
input. Neither Schur linearity nor an involution equation is required to lift
the induced component automorphism. -/
def NormalizerLifts : Prop :=
  ∀ (_e : σ.Equiv (binaryRep B)) (t : linearNormalizer σ),
    Nonempty (SemilinearLift B σ t)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms
