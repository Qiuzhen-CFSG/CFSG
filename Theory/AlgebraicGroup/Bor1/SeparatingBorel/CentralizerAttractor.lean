module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ModelRestriction
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.BasinComparison
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.TwoPointSign

/-!
# Restricting the attracting Borel to the original centralizer

A positive ratio selects one of the two fixed points on the actual centralizer
orbit. The global attracting basin contains its own endpoint, so its
restriction to the centralizer orbit through that endpoint is nonempty open.
Comparing this basin with the selected local basin proves equality of the
literal restricted stabilizers. All cocharacters and characters are
transported through the original torus inclusion.

Source: Borel, *Linear Algebraic Groups*, IV, 13.8 and 13.11(2)--(3).
-/

public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Theory.AlgebraicGroup.Variety.Geometric
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
open ProjectiveLimit
universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

theorem centralizer_attractor_stabilizer_eq
    (hG : Variety.IsConnected G) (S T : ClosedSubgroup G)
    (hS : IsSubtorus S) (hT : IsMaximalTorus T) (hST : S ≤ T)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (A : MorphicAction G (projectiveSpace k E))
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b p))
    (x y : Point (projectiveSpace k E))
    (hxB : IsBorelSubgroup (A.pointStabilizer x)) (hxT : T ≤ A.pointStabilizer x)
    (hyB : IsBorelSubgroup (A.pointStabilizer y)) (hyT : T ≤ A.pointStabilizer y)
    (hy : ∃ g : Variety.Point G, A.toMulAction.smul g x = y)
    (c : ClosedSubgroupTorusCocharacter T)
    (hc : (T.inclusion.comp c).imageClosedSubgroup.centralizer = T.centralizer)
    (U : (projectiveSpace k E).toScheme.Opens) (hyU : y.1 (IsLocalRing.closedPoint k) ∈ U)
    (hcurve : ∀ z : Point (projectiveSpace k E),
      (∃ g : Variety.Point G, A.toMulAction.smul g x = z) →
      z.1 (IsLocalRing.closedPoint k) ∈ U →
      ∃ f : Variety.Geometric.Morphism (polynomialAffineLine k) (projectiveSpace k E),
        f (ProjectivePolynomialCurve.affinePoint 0) = y ∧
        ∀ (a : k) (ha : a ≠ 0), f (ProjectivePolynomialCurve.affinePoint a) =
          A.toMulAction.smul
            (T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹))) z)
    (wPlus wMinus : E) (α β : TorusWeight T)
    (hwPlus : IsWeightVector ρ T wPlus α) (hwMinus : IsWeightVector ρ T wMinus β)
    (hplus : ∃ g : Variety.Point S.centralizer.carrierVariety,
      A.toMulAction.smul (S.centralizer.includePoint g) x =
        projectivePointOfVector (b.equivFun wPlus) (b.equivFun.map_ne_zero_iff.mpr hwPlus.1))
    (hcover : ∀ z : Point (projectiveSpace k E),
      (∃ g : Variety.Point S.centralizer.carrierVariety,
        A.toMulAction.smul (S.centralizer.includePoint g) x = z) →
      (∀ t : Variety.Point T.carrierVariety, A.toMulAction.smul (T.includePoint t) z = z) →
      z = projectivePointOfVector (b.equivFun wPlus) (b.equivFun.map_ne_zero_iff.mpr hwPlus.1) ∨
      z = projectivePointOfVector (b.equivFun wMinus) (b.equivFun.map_ne_zero_iff.mpr hwMinus.1))
    (hpositive : 0 < characterCocharacterPairing T c (Additive.ofMul (α / β))) :
    (A.pullbackGroup S.centralizer.inclusion).pointStabilizer y =
      (A.pullbackGroup S.centralizer.inclusion).pointStabilizer
        (projectivePointOfVector (b.equivFun wPlus) (b.equivFun.map_ne_zero_iff.mpr hwPlus.1)) := by
  let H := S.centralizer
  let Ti := H.inclusion.closedSubgroupPreimage T
  let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
  let AH := A.pullbackGroup H.inclusion
  let ρH := representationPullback ρ H.inclusion
  have hH : Variety.IsConnected H.carrierVariety :=
    SemisimpleCenterContainment.CartanGeometry.subtorus_centralizer_isConnected hG hS
  have hTH : T ≤ H := maximalTorus_le_subtorusCentralizer S T hT hST
  have hTi : IsMaximalTorus Ti := maximalTorus_preimage_inclusion T H hT hTH
  have hBx : IsBorelSubgroup (AH.pointStabilizer x) :=
    centralizer_restricted_stabilizer_isBorel hG A x S hS hxB (fun s hs => hxT (hST hs))
  have hBy : IsBorelSubgroup (AH.pointStabilizer y) :=
    centralizer_restricted_stabilizer_isBorel hG A y S hS hyB (fun s hs => hyT (hST hs))
  have hclosed := AH.orbit_isClosed_of_borel_fixed hH (AH.pointStabilizer x) hBx x
    (fun g hg => (AH.mem_pointStabilizer x g).mp hg)
  obtain ⟨cH,hcH,hregH⟩ := semiregular_cocharacter_restriction T H hTH c hc
  let j := inclusionPreimageBack T H
  let αH := TorusCharacter.pullback j α
  let βH := TorusCharacter.pullback j β
  have hwPlusH := weightVector_restrict_overgroup ρ T H wPlus α hwPlus
  have hwMinusH := weightVector_restrict_overgroup ρ T H wMinus β hwMinus
  have hpositiveH : 0 < characterCocharacterPairing Ti cH (Additive.ofMul (αH / βH)) := by
    change 0 < characterCocharacterPairing Ti cH
      (Additive.ofMul (TorusCharacter.pullback j α / TorusCharacter.pullback j β))
    rw [← map_div]
    rw [pairing_restrict_overgroup T H c (α / β) cH hcH]
    exact hpositive
  let := AH.toMulAction
  have hxstab : ∀ g : Variety.Point H.carrierVariety, g • x = x ↔
      g ∈ (AH.pointStabilizer x).toSubgroup := fun g => (AH.mem_pointStabilizer x g).symm
  obtain ⟨V,_,hV,hneV,hcurveV⟩ := exists_attractor_at_positive_weight_point ρH
    (representationPullback_isRational ρ hρ H.inclusion) hH Ti hTi.1 cH AH b
    (projective_action_restrict_equivariant ρ A b he H.inclusion) x hclosed
    wPlus wMinus αH βH hwPlusH hwMinusH hplus (by
      intro z hz
      have ht := (cocharacter_fixed_orbit_iff_torus_fixed hH (AH.pointStabilizer x) hBx x hxstab
        Ti hTi cH hregH z hz.1).mp hz.2
      apply hcover z hz.1
      intro t
      let f := inclusionPreimageMorphism T H hTH
      have hh := ht (f.onPoints t)
      change A.toMulAction.smul (H.includePoint (Ti.includePoint (f.onPoints t))) z = z at hh
      rw [show H.includePoint (Ti.includePoint (f.onPoints t)) = T.includePoint t from
        inclusionPreimageMorphism_apply T H hTH t] at hh
      exact hh) hpositiveH
  let UH := {g : Variety.Point H.carrierVariety |
    (AH.toMulAction.smul g y).1 (IsLocalRing.closedPoint k) ∈ U}
  let VH := {g : Variety.Point H.carrierVariety |
    (AH.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈ V}
  apply attracting_stabilizers_eq hH AH AH y y x
    (projectivePointOfVector (b.equivFun wPlus) (b.equivFun.map_ne_zero_iff.mpr hwPlus.1))
    hBy hBx
    (fun a : kˣ => Ti.includePoint (cH.onPoints (cocharacterParameter a⁻¹)))
    UH VH (orbit_preimage_isOpen AH y U) hV
    (by
      refine ⟨1, ?_⟩
      change (AH.toMulAction.smul 1 y).1 (IsLocalRing.closedPoint k) ∈ U
      change ((1 : Variety.Point H.carrierVariety) • y).1 (IsLocalRing.closedPoint k) ∈ U
      rw [one_smul]
      exact hyU) hneV
  · intro g hg
    have horbit : ∃ a : Variety.Point G, A.toMulAction.smul a x = AH.toMulAction.smul g y := by
      obtain ⟨a,ha⟩ := hy
      refine ⟨H.includePoint g * a, ?_⟩
      let := A.toMulAction
      change (H.includePoint g * a) • x = H.includePoint g • y
      rw [mul_smul]
      exact congrArg (fun z : Point (projectiveSpace k E) => (H.includePoint g) • z) ha
    obtain ⟨f,hf,hfa⟩ := hcurve _ horbit hg
    refine ⟨f,hf,?_⟩
    intro a ha
    rw [hfa a ha]
    change A.toMulAction.smul (T.includePoint (c.onPoints _)) (AH.toMulAction.smul g y) =
      A.toMulAction.smul (H.includePoint (Ti.includePoint (cH.onPoints _))) (AH.toMulAction.smul g y)
    exact congrArg (fun t : Variety.Point G => A.toMulAction.smul t (AH.toMulAction.smul g y))
      (hcH (cocharacterParameter (Units.mk0 a ha)⁻¹)).symm
  · intro g hg
    exact (hcurveV _ ⟨g,rfl⟩).mp hg
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
