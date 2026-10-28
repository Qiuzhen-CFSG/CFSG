module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs
public import CFSG.Quasithin.Defs
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SimpleFittingExtensions

/-!
# The marked Hall--Janko recognition boundary for Chapter K

The source input retains the actual finite SQTK actor, its quasisimple
generalized Fitting subgroup, its faithful binary action irreducible on that
subgroup, the cubic-ratio bound two, and the actual J₂ central quotient.

For a supplied geometric marking and a center-free component identification,
we construct the ambient map into the actual inner-field extension of G₂(4).
It preserves the component inclusion. An equivariant identification in six
F₄ coordinates then gives an identification with the actual octonion quotient,
including its coefficient involution. These are conditional assembly results.

The existence of the geometric marking, the source cover/degree reduction,
and the degree-twelve module recognition remain separate proof obligations.
Neither the input record nor these transports proves source recognition.
All later offender and ratio calculations belong to Chapter K's J₂ owner.

Source: Aschbacher--Smith K.4 opening paragraph, printed pp.457--458, and K.4.5,
printed p.460. The source cites Guralnick--Malle, Classification of 2F-modules I,
Theorem 6.6 and Table 6.7, for the representation reduction.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko

open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.G2FourModule
open Atlas.G2.Natural.BinarySemilinear

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The genuine Chapter K hypotheses in the J₂ central-quotient branch. -/
structure SourceHypotheses (ρ : Representation (ZMod 2) G W) : Prop where
  finite_group : Finite G
  finite_module : FiniteDimensional (ZMod 2) W
  sqtk : IsSQTK KnownSimple.IsKnownSimple G
  quasisimple : IsQuasisimple (generalizedFitting G)
  faithful : Function.Injective ρ
  irreducible : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype)
  cubic_le_two : cubicRatio ρ ≤ 2
  centralQuotient : Nonempty
    ((generalizedFitting G) ⧸ center (generalizedFitting G) ≃* KnownSimple.SporadicName.j2.Carrier)

variable (d : MarkedEmbedding) (e : generalizedFitting G ≃* Carrier)

/-- The original ambient actor maps through its genuine conjugation action. -/
noncomputable def ambientEmbedding : G →* OuterM :=
  d.outer.comp (SimpleFittingExtensions.ambientAction e)

/-- Injectivity uses the generalized Fitting centralizer theorem for the actual G. -/
theorem ambientEmbedding_injective [IsSimpleGroup (generalizedFitting G)] :
    Function.Injective (ambientEmbedding d e) :=
  d.outer_injective.comp (SimpleFittingExtensions.ambientAction_injective e)

/-- The component map is exactly the marked embedding, with its literal inclusion. -/
theorem ambientEmbedding_on_fitting (x : generalizedFitting G) :
    ambientEmbedding d e x = SemidirectProduct.inl (d.inner (e x)) := by
  change d.outer (SimpleFittingExtensions.ambientAction e x) = _
  rw [SimpleFittingExtensions.ambientAction_on_fitting, d.on_inner]

/-- The natural quotient action pulled back to the original ambient actor. -/
noncomputable def naturalPullback : Representation (ZMod 2) G V :=
  (representation F).comp (ambientEmbedding d e)

/-- The same actual action in six F₄ coordinates. -/
noncomputable def coordinatePullback : Representation (ZMod 2) G (Coordinates F) :=
  (coordinateRepresentation F).comp (ambientEmbedding d e)

/-- This pullback restricts to the marked natural G₂(4) action on F*(G). -/
theorem naturalPullback_on_fitting (x : generalizedFitting G) (v : V) :
    naturalPullback d e x v = Atlas.G2.Natural.action F (d.inner (e x)) v := by
  change representation F (ambientEmbedding d e x) v = _
  rw [ambientEmbedding_on_fitting, representation_inner]

/-- The literal outside involution, when present, has the specified field action. -/
theorem naturalPullback_on_outer (i : G)
    (hi : SimpleFittingExtensions.ambientAction e i = ExceptionalParabolics.extensionInvolution)
    (v : V) : naturalPullback d e i v = fieldEquivalence F fourFrobenius v := by
  change representation F (d.outer (SimpleFittingExtensions.ambientAction e i)) v = _
  rw [hi, d.on_involution, representation_field]

/-- Recognition in coordinates identifies the actual quotient representation. -/
noncomputable def quotientIdentification (ρ : Representation (ZMod 2) G W)
    (c : Representation.RepEquiv ρ (coordinatePullback d e)) :
    Representation.RepEquiv ρ (naturalPullback d e) where
  toLinearEquiv := c.toLinearEquiv.trans (coordinatesEquiv F).symm
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    apply (coordinatesEquiv F).injective
    change coordinatesEquiv F ((coordinatesEquiv F).symm (c (ρ g w))) =
      coordinatesEquiv F (representation F (ambientEmbedding d e g)
        ((coordinatesEquiv F).symm (c w)))
    rw [LinearEquiv.apply_symm_apply, coordinates_representation,
      LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (c.isIntertwining' g) w

omit [FiniteDimensional (ZMod 2) W] in
/-- The recognized source action has binary degree twelve. -/
theorem finrank_of_coordinateIdentification (ρ : Representation (ZMod 2) G W)
    (c : Representation.RepEquiv ρ (coordinatePullback d e)) :
    Module.finrank (ZMod 2) W = 12 :=
  (quotientIdentification d e ρ c).toLinearEquiv.finrank_eq.trans finrank_four

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko
