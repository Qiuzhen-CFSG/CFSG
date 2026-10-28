module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.NaturalFour
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.ThreeDuality
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Natural module comparisons for the literal exterior stabilizers

The pointwise wedge-coordinate calculations give equivalences of the actual
stabilizer representations on V₃, V₄ and V/V₆ with natural block modules.
The V₃ actor uses the inverse-transpose automorphism of the upper SL₃ block;
the V₄ and V/V₆ actors use the lower and upper SL₄ blocks, respectively.

The proved stabilizer equalities identify these actors with their flag
parabolics without changing their ambient matrices. In particular, the
quotient-to-shear equivalence intertwines the literal V₆ stabilizer action
with conjugation in SL₅(F₂). These comparisons are the module inputs to the
source's residual-quotient transport; no radical identification is assumed.

Source: Aschbacher–Smith, Lemma 12.5.2(2–4), printed p.817/PDF p.834.
-/

@[expose] public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
noncomputable section

/-- Complementary-wedge coordinates give an equivalence of representations for
the literal V₃ stabilizer, using the inverse-transpose twist of its upper block. -/
def V₃StabilizerEquivNatural :
    V₃StabilizerAction.Equiv
      ((specialLinearNatural 3).comp threeStabilizerNaturalProjection) :=
  .mk V₃Equiv (fun g => by
    apply LinearMap.ext
    intro v
    exact V₃Equiv_stabilizer_natural g v)

/-- Identify the literal exterior stabilizer of V₄ with the line parabolic. -/
def fourStabilizerToParabolic : exteriorStabilizer V₄ →* parabolic 1 :=
  Subgroup.inclusion (le_of_eq exteriorStabilizer_V₄_eq_parabolic)

/-- The lower-right SL₄ block of the actual exterior stabilizer of V₄. -/
def fourStabilizerNaturalProjection :
    exteriorStabilizer V₄ →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  lowerFourProjection.comp fourStabilizerToParabolic

/-- The actual exterior action restricted to V₄ and its literal stabilizer. -/
def V₄StabilizerAction :
    Representation (ZMod 2) (exteriorStabilizer V₄) V₄ where
  toFun g := (exteriorAction 2 g.val).restrict (fun v hv => (g.property v).mpr hv)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change exteriorAction 2 1 v.val = v.val
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change exteriorAction 2 (g.val * h.val) v.val =
      exteriorAction 2 g.val (exteriorAction 2 h.val v.val)
    rw [map_mul]
    rfl

@[simp] theorem V₄StabilizerAction_apply (g : exteriorStabilizer V₄) (v : V₄) :
    (V₄StabilizerAction g v).val = exteriorAction 2 g.val v.val := rfl

/-- The four wedge coordinates intertwine the literal stabilizer action with
its lower-right natural block action. -/
theorem V₄Equiv_stabilizer_natural (g : exteriorStabilizer V₄) (v : V₄) :
    V₄Equiv (V₄StabilizerAction g v) =
      specialLinearNatural 4 (fourStabilizerNaturalProjection g) (V₄Equiv v) :=
  V₄Equiv_natural (fourStabilizerToParabolic g) v

/-- The natural-module comparison on V₄ as an equivalence of the actual
stabilizer representations. -/
def V₄StabilizerEquivNatural :
    V₄StabilizerAction.Equiv
      ((specialLinearNatural 4).comp fourStabilizerNaturalProjection) :=
  .mk V₄Equiv (fun g => by
    apply LinearMap.ext
    intro v
    exact V₄Equiv_stabilizer_natural g v)

/-- Identify the literal exterior stabilizer of V₆ with the four-space parabolic. -/
def sixStabilizerToParabolic : exteriorStabilizer V₆ →* parabolic 4 :=
  Subgroup.inclusion (le_of_eq exteriorStabilizer_V₆_eq_parabolic)

/-- The upper-left SL₄ block of the actual exterior stabilizer of V₆. -/
def sixStabilizerNaturalProjection :
    exteriorStabilizer V₆ →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  upperFourProjection.comp sixStabilizerToParabolic

/-- The action of the literal V₆ stabilizer on the actual quotient V/V₆. -/
def quotientSixStabilizerAction :
    Representation (ZMod 2) (exteriorStabilizer V₆) (V ⧸ V₆) :=
  quotientSixAction.comp sixStabilizerToParabolic

@[simp] theorem quotientSixStabilizerAction_mk (g : exteriorStabilizer V₆) (v : V) :
    quotientSixStabilizerAction g (V₆.mkQ v) =
      V₆.mkQ (exteriorAction 2 g.val v) := rfl

/-- The surviving wedge coordinates 3, 6, 8, 9 identify the actual quotient
stabilizer action with the upper-left natural block action. -/
theorem shearQuotientEquiv_stabilizer_natural
    (g : exteriorStabilizer V₆) (v : V ⧸ V₆) :
    shearQuotientEquiv (quotientSixStabilizerAction g v) =
      specialLinearNatural 4 (sixStabilizerNaturalProjection g) (shearQuotientEquiv v) :=
  shearQuotientEquiv_natural (sixStabilizerToParabolic g) v

/-- The natural-module comparison on V/V₆ as an equivalence of the actual
stabilizer representations. -/
def quotientSixStabilizerEquivNatural :
    quotientSixStabilizerAction.Equiv
      ((specialLinearNatural 4).comp sixStabilizerNaturalProjection) :=
  .mk shearQuotientEquiv (fun g => by
    apply LinearMap.ext
    intro v
    exact shearQuotientEquiv_stabilizer_natural g v)

/-- The literal quotient-to-shear equivalence is equivariant for every element
of the actual exterior stabilizer. The source identification of this shear
subgroup with R̄₆ is a separate group-theoretic conclusion. -/
theorem quotientSixShearEquiv_stabilizer_action
    (g : exteriorStabilizer V₆) (v : V ⧸ V₆) :
    (quotientSixShearEquiv
      (Multiplicative.ofAdd (quotientSixStabilizerAction g v)) : Group) =
      g.val * (quotientSixShearEquiv (Multiplicative.ofAdd v) : Group) * g.val⁻¹ :=
  quotientSixShearEquiv_action (sixStabilizerToParabolic g) v

end
end Representation.SL5ExteriorSquare
