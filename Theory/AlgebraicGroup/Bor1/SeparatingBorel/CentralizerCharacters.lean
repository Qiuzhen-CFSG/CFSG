module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ModelRestriction
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.DistinctWeights

/-!
# The actual character attached to a singular codimension-one subtorus

Restrict the original Chevalley projective model to the literal centralizer.
The source rank-one quotient and Borel correspondence give exactly two torus
fixed points on this closed orbit. Their genuine regular characters are
distinct by the maximal/minimal-weight argument, and their ratio has the
original subtorus as its ambient connected kernel. The same original model
is retained for different subtori.

Source: Borel, *Linear Algebraic Groups*, IV, 11.15 and 13.11(1)--(3).
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

theorem weight_of_projective_fixed_vector
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (T : ClosedSubgroup G) (A : MorphicAction G (projectiveSpace k E))
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b p))
    (v : E) (hv : v ≠ 0)
    (hfix : ∀ t : Variety.Point T.carrierVariety,
      A.toMulAction.smul (T.includePoint t)
        (projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv)) =
        projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv)) :
    ∃! χ : TorusWeight T, IsWeightVector ρ T v χ := by
  apply invariantLine_torusWeight_existsUnique_public ρ hρ T v
  refine ⟨hv, ?_⟩
  intro g hg
  let t := T.pointEquiv.symm ⟨g,hg⟩
  have hh := congrArg (projectiveSpacePointEquivOf b) (hfix t)
  rw [he, projectiveSpacePointEquivOf_projectivePointOfVector b v hv, Projectivization.map_mk] at hh
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp hh
  exact ⟨a,ha.symm⟩

theorem exists_centralizer_orbit_character
    (hG : Variety.IsConnected G) (S T B : ClosedSubgroup G)
    (hS : IsSubtorus S) (hT : IsMaximalTorus T) (hST : S ≤ T)
    (hcodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hns : ¬ Group.IsSolvable (Variety.Point S.centralizer.carrierVariety))
    (hB : IsBorelSubgroup B) (hTB : T ≤ B)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (A : MorphicAction G (projectiveSpace k E))
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b p))
    (v : E) (α : TorusWeight T) (hv : IsWeightVector ρ T v α)
    (hx : ∀ g : Variety.Point G, A.toMulAction.smul g
      (projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv.1)) =
        projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv.1) ↔ g ∈ B.toSubgroup) :
    ∃ (w : E) (β : TorusWeight T) (hw : IsWeightVector ρ T w β),
      α ≠ β ∧
      (∃ g : Variety.Point S.centralizer.carrierVariety,
        A.toMulAction.smul (S.centralizer.includePoint g)
          (projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv.1)) =
        projectivePointOfVector (b.equivFun w) (b.equivFun.map_ne_zero_iff.mpr hw.1)) ∧
      projectivePointOfVector (b.equivFun w) (b.equivFun.map_ne_zero_iff.mpr hw.1) ≠
        projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv.1) ∧
      (∀ z : Point (projectiveSpace k E),
        (∃ g : Variety.Point S.centralizer.carrierVariety,
          A.toMulAction.smul (S.centralizer.includePoint g)
            (projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv.1)) = z) →
        (∀ t : Variety.Point T.carrierVariety, A.toMulAction.smul (T.includePoint t) z = z) →
        z = projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv.1) ∨
        z = projectivePointOfVector (b.equivFun w) (b.equivFun.map_ne_zero_iff.mpr hw.1)) ∧
      (α * β⁻¹).ambientConnectedKernel T = S := by
  let H := S.centralizer
  let Ti := H.inclusion.closedSubgroupPreimage T
  let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
  let BH := H.inclusion.closedSubgroupPreimage B
  let AH := A.pullbackGroup H.inclusion
  let ρH := representationPullback ρ H.inclusion
  let x : Point (projectiveSpace k E) := projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv.1)
  let : MulAction (Variety.Point H.carrierVariety) (Point (projectiveSpace k E)) := AH.toMulAction
  have hTH : T ≤ H := maximalTorus_le_subtorusCentralizer S T hT hST
  have hTi : IsMaximalTorus Ti := maximalTorus_preimage_inclusion T H hT hTH
  have hH : Variety.IsConnected H.carrierVariety :=
    SemisimpleCenterContainment.CartanGeometry.subtorus_centralizer_isConnected hG hS
  have hBH : IsBorelSubgroup BH :=
    SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.isBorel_centralizer_restriction
      hG S B hS hB (fun s hs => hTB (hST hs))
  have hTBH : Ti ≤ BH := fun t ht => hTB ht
  have hxH : ∀ g : Variety.Point H.carrierVariety, g • x = x ↔ g ∈ BH.toSubgroup :=
    fun g => hx (H.includePoint g)
  obtain ⟨_, z, hz, hzx, hzT, htwo⟩ :=
    centralizer_orbit_exactly_two_fixed_points hG S T hS hT hST hcodim hns BH hBH hTBH x hxH
  have hzT' : ∀ t : Variety.Point T.carrierVariety, A.toMulAction.smul (T.includePoint t) z = z := by
    intro t
    let j := inclusionPreimageMorphism T H hTH
    have hh := hzT (Ti.includePoint (j.onPoints t)) (Ti.pointEquiv (j.onPoints t)).property
    change A.toMulAction.smul (H.includePoint (Ti.includePoint (j.onPoints t))) z = z at hh
    rw [show H.includePoint (Ti.includePoint (j.onPoints t)) = T.includePoint t from
      inclusionPreimageMorphism_apply T H hTH t] at hh
    exact hh
  obtain ⟨w,hw0,hwz⟩ := exists_projective_vector b z
  obtain ⟨β,hw,_⟩ := weight_of_projective_fixed_vector ρ hρ T A b he w hw0 (by
    simpa only [hwz] using hzT')
  have hworb : ∃ g : Variety.Point H.carrierVariety,
      AH.toMulAction.smul g x = projectivePointOfVector (b.equivFun w) (b.equivFun.map_ne_zero_iff.mpr hw.1) := by
    obtain ⟨g,hg⟩ := hz
    exact ⟨g,hg.trans hwz⟩
  have hwne : projectivePointOfVector (b.equivFun w) (b.equivFun.map_ne_zero_iff.mpr hw.1) ≠ x := by
    simpa only [hwz] using hzx
  have hwcover : ∀ y : Point (projectiveSpace k E),
      (∃ g : Variety.Point H.carrierVariety, AH.toMulAction.smul g x = y) →
      (∀ t : Variety.Point T.carrierVariety, A.toMulAction.smul (T.includePoint t) y = y) →
      y = x ∨ y = projectivePointOfVector (b.equivFun w) (b.equivFun.map_ne_zero_iff.mpr hw.1) := by
    intro y hy ht
    have hh := htwo y hy (fun t hti => ht (T.pointEquiv.symm ⟨H.includePoint t, hti⟩))
    simpa only [hwz] using hh
  have hne : α ≠ β := by
    obtain ⟨c,hc⟩ := exists_semiregular_cocharacter Ti hTi.1
    let f := inclusionPreimageBack T H
    have hvH := weightVector_restrict_overgroup ρ T H v α hv
    have hwH := weightVector_restrict_overgroup ρ T H w β hw
    have hclosed := AH.orbit_isClosed_of_borel_fixed hH BH hBH x (fun g hg => (hxH g).mpr hg)
    have hneH := two_fixed_point_weights_ne ρH (representationPullback_isRational ρ hρ H.inclusion)
      hH Ti hTi.1 c AH b (projective_action_restrict_equivariant ρ A b he H.inclusion)
      v w (TorusCharacter.pullback f α) (TorusCharacter.pullback f β) hvH hwH
      hclosed hworb hwne (by
        intro y hy
        have ht := (cocharacter_fixed_orbit_iff_torus_fixed hH BH hBH x hxH Ti hTi c hc y hy.1).mp hy.2
        have hh := htwo y hy.1 (fun t hti => ht (Ti.pointEquiv.symm ⟨t,hti⟩))
        simpa only [hwz] using hh)
    exact fun h => hneH (congrArg (TorusCharacter.pullback f) h)
  refine ⟨w,β,hw,hne,hworb,hwne,hwcover,?_⟩
  obtain ⟨g,hg⟩ := hworb
  apply orbit_weight_ratio_ambientConnectedKernel ρ T S hT.1 hS hST hcodim v w α β hne hv hw
    (H.includePoint g) (H.pointEquiv g).property
  have hp := congrArg (projectiveSpacePointEquivOf b) hg
  rw [projectiveSpacePointEquivOf_projectivePointOfVector b w hw.1] at hp
  change projectiveSpacePointEquivOf b (A.toMulAction.smul (H.includePoint g) x) = _ at hp
  rw [he] at hp
  change Projectivization.map (ρ.action (H.includePoint g)).1 _
    (projectiveSpacePointEquivOf b (projectivePointOfVector (b.equivFun v) _)) = _ at hp
  rw [projectiveSpacePointEquivOf_projectivePointOfVector b v hv.1] at hp
  exact hp.symm
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
