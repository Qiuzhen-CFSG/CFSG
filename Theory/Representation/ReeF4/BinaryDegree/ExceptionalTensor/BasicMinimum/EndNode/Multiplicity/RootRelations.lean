module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Multiplicity.RootOperators
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup.Commutation


/-!
# Mixed simple-root commutation on rational F4 factors

The integral positive and negative Geck curves at distinct simple nodes
commute. Transporting their actual matrix identity through the closed carrier
and the rational action proves commutation of each raising curve with the
other lowering operator. Extracting one more coefficient gives the mixed
operator commutation relation. In particular, lowering at a different node
preserves fixation by the entire positive root group.

Source: GLS3, Theorem 1.12.1, for distinct simple roots of opposite signs.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

@[expose] def raising (B : AlgebraicFactor F) (i : Fin 4) : Module.End F B.Space :=
  rootOperator B (typeF4SimpleRootIndex i)

@[expose] def lowering (B : AlgebraicFactor F) (i : Fin 4) : Module.End F B.Space :=
  rootOperator B (-typeF4SimpleRootIndex i)

private def ambientUnitsEquiv :
    (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ ≃*
      Variety.Point (F4Chevalley.Ambient F) :=
  Matrix.GeneralLinearGroup.toLin.trans
    ((Matrix.GeneralLinearGroup.toLin'
      (carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base))).symm.trans
      (translationGLPointMulEquiv _).symm)

private theorem ambientUnitsEquiv_rootCurve (r : F4Chevalley.Root) (t : F) :
    ambientUnitsEquiv (F4Chevalley.rootCurve r t) =
      (F4Chevalley.ambientRootMorphism r).onPoints (kPlusPoint t) := by
  rw [F4Chevalley.ambientRootMorphism_apply]
  rfl

theorem algebraicRootElement_commute_of_curves (r s : F4Chevalley.Root) (t u : F)
    (h : Commute (F4Chevalley.rootCurve r t) (F4Chevalley.rootCurve s u)) :
    Commute (algebraicRootElement r t) (algebraicRootElement s u) := by
  apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
  simp only [map_mul, algebraicRootElement, F4Chevalley.rootMorphism_inclusion_apply]
  rw [← ambientUnitsEquiv_rootCurve, ← ambientUnitsEquiv_rootCurve]
  exact (h.map ambientUnitsEquiv.toMonoidHom).eq

theorem positive_negative_commute (i j : Fin 4) (hij : i ≠ j) (t u : F) :
    Commute (algebraicRootElement (typeF4SimpleRootIndex i) t)
      (algebraicRootElement (-typeF4SimpleRootIndex j) u) := by
  apply algebraicRootElement_commute_of_curves
  change Commute
    (rootCurveUnit integralChevalleyRootOperators (typeF4SimpleRootIndex i) t)
    (rootCurveUnit integralChevalleyRootOperators (-typeF4SimpleRootIndex j) u)
  rw [← typeF4RootPairing_baseEquiv_val i, ← typeF4RootPairing_baseEquiv_val j,
    rootCurveUnit_simple, rootCurveUnit_neg_simple]
  exact (commute_positive_negative (typeF4RootPairing_baseEquiv i)
    (typeF4RootPairing_baseEquiv j)
    (fun h => hij (typeF4RootPairing_baseEquiv.injective h)) t u).map
      (subgroup typeF4RootPairing_base F).subtype

theorem action_commute_lowering (B : AlgebraicFactor F) (i j : Fin 4) (hij : i ≠ j)
    (t : F) :
    (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) * lowering B j =
      lowering B j * (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) t) :
        Module.End F B.Space) := by
  let A : Module.End F B.Space :=
    B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) t)
  have h := rootOperator_intertwine B (-typeF4SimpleRootIndex j)
    (-typeF4SimpleRootIndex j) A A 1 (by
      intro u v
      have hc := ((positive_negative_commute i j hij t u).map B.action.action).eq
      have hv := congrArg (fun g : LinearMap.GeneralLinearGroup F B.Space =>
        (g : Module.End F B.Space) v) hc
      simpa only [one_mul, Units.val_mul, Module.End.mul_apply, A] using hv)
  simpa only [one_smul, lowering, A] using h

theorem raising_commute_lowering (B : AlgebraicFactor F) (i j : Fin 4) (hij : i ≠ j) :
    raising B i * lowering B j = lowering B j * raising B i := by
  have h := rootOperator_intertwine B (typeF4SimpleRootIndex i)
    (typeF4SimpleRootIndex i) (lowering B j) (lowering B j) 1 (by
      intro t v
      have hc := congrArg (fun A : Module.End F B.Space => A v)
        (action_commute_lowering B i j hij t).symm
      simpa only [one_mul, Module.End.mul_apply] using hc)
  simpa only [one_smul, raising] using h.symm

theorem lowering_fixed_of_fixed (B : AlgebraicFactor F) (i j : Fin 4) (hij : i ≠ j)
    (v : B.Space)
    (hv : ∀ t : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = v) :
    ∀ t : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) (lowering B j v) = lowering B j v := by
  intro t
  have h := congrArg (fun A : Module.End F B.Space => A v)
    (action_commute_lowering B i j hij t)
  simpa only [Module.End.mul_apply, hv] using h

end
end ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
