module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.Small
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd

public import Mathlib.Algebra.Field.ZMod

/-!
# Hyperbolic coordinates for the Co₁ local matrix image

The coordinate equivalence orders the split space as `e0,e1,e2,e3,f0,f1,f2,f3`.
`matrixHom` faithfully expresses actual quadratic isometries as eight by eight
matrices. Its action theorem fixes the column-vector and multiplication
conventions used by the word certificates and the elementary embedding.

Source purpose: GLS3 Table 5.3l, the Ω₈⁺(2) section of the Co₁ involution
centralizer; Aschbacher–Smith A.2.19, printed pp.40–41.
-/

@[expose] public section
open scoped Matrix
open ClassicalOrthogonal Theory.AlgebraicGroup
namespace Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
abbrev V := VectorD 4 (ZMod 2)
abbrev Q := formD 4 (ZMod 2)
abbrev O := quadraticIsometrySubgroup Q

def coordinates : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  LinearEquiv.funCongrLeft _ _ (finSumFinEquiv (m := 4) (n := 4)).symm

def linearAction : SmallAmbient ≃* (V ≃ₗ[ZMod 2] V) :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.congrLinearEquiv coordinates.symm)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem linearAction_apply (g : SmallAmbient) (v : V) :
    linearAction g v = coordinates.symm (g.val *ᵥ coordinates v) := rfl

def matrixHom : O →* SmallAmbient :=
  linearAction.symm.toMonoidHom.comp (quadraticIsometrySubgroup Q).subtype

theorem matrixHom_injective : Function.Injective matrixHom :=
  linearAction.symm.injective.comp Subtype.val_injective

theorem matrixHom_action (g : O) (v : V) :
    (matrixHom g).val *ᵥ coordinates v = coordinates (g.val v) := by
  have h := congrArg (fun t : V ≃ₗ[ZMod 2] V => t v) (linearAction.apply_symm_apply g.val)
  change coordinates.symm ((matrixHom g).val *ᵥ coordinates v) = g.val v at h
  exact coordinates.symm.injective (h.trans (coordinates.symm_apply_apply _).symm)

abbrev e0 : V := e 0

theorem coordinates_e0 : coordinates e0 = Pi.single 0 1 := by
  decide +kernel

end Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding

namespace Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
open scoped Matrix

theorem matrixHom_entry (g : O) (i j : Fin 8) :
    (matrixHom g).val i j =
      coordinates (g.val (coordinates.symm (Pi.single j 1))) i := by
  have h := congrArg (fun w : Fin 8 → ZMod 2 => w i)
    (matrixHom_action g (coordinates.symm (Pi.single j 1)))
  simpa using h

end Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
