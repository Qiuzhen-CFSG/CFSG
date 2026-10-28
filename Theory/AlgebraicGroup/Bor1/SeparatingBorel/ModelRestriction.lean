module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.CharacterRestriction
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.OrbitWeights
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.CentralizerOrbit

/-!
# Restricting the original projective model to a centralizer

Rational representations and their equivariant projective actions restrict
along the literal closed-subgroup inclusion. The inverse-image torus maps
back to the original torus, preserving weight vectors and their cocharacter
pairings. Stabilizers restrict by the same inverse image, so source Borel
restriction applies to the actual centralizer action.

Source: Borel, *Linear Algebraic Groups*, IV, 11.15 and 13.11--13.12.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
open Variety.Geometric
open scoped LinearAlgebra.Projectivization
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
variable {E : Type u} [AddCommGroup E] [Module k E]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

@[expose] def representationPullback (ρ : RationalRepresentation G E)
    (f : AlgebraicGroup.Morphism H G) : RationalRepresentation H E :=
  ⟨ρ.action.comp f.onPoints⟩

theorem representationPullback_isRational (ρ : RationalRepresentation G E)
    (hρ : IsRationalRepresentation ρ) (f : AlgebraicGroup.Morphism H G) :
    IsRationalRepresentation (representationPullback ρ f) := by
  obtain ⟨b, g, hg⟩ := hρ
  exact ⟨b, g.comp f, fun x => hg (f.onPoints x)⟩

@[expose] noncomputable def inclusionPreimageBack (T K : ClosedSubgroup G) :
    let Ti := K.inclusion.closedSubgroupPreimage T
    let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
    AlgebraicGroup.Morphism Ti.carrierVariety T.carrierVariety := by
  dsimp only
  let Ti := K.inclusion.closedSubgroupPreimage T
  let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
  exact (K.inclusion.comp Ti.inclusion).codRestrictClosedSubgroup T
    (fun x => (Ti.pointEquiv x).property)

omit [IsAlgClosed k] in
theorem inclusionPreimageBack_apply (T K : ClosedSubgroup G) :
    let Ti := K.inclusion.closedSubgroupPreimage T
    let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
    ∀ x : Variety.Point Ti.carrierVariety,
    T.includePoint ((inclusionPreimageBack T K).onPoints x) = K.includePoint (Ti.includePoint x) := by
  dsimp only
  let Ti := K.inclusion.closedSubgroupPreimage T
  let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
  intro x
  exact Morphism.codRestrictClosedSubgroup_inclusion_apply _ T _ x

omit [IsAlgClosed k] in
theorem inclusionPreimageBack_comp_cocharacter (T K : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T) :
    let Ti := K.inclusion.closedSubgroupPreimage T
    let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
    ∀ cK : ClosedSubgroupTorusCocharacter Ti,
      (∀ t, K.includePoint (Ti.includePoint (cK.onPoints t)) = T.includePoint (c.onPoints t)) →
      (inclusionPreimageBack T K).comp cK = c := by
  dsimp only
  let Ti := K.inclusion.closedSubgroupPreimage T
  let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
  intro cK hc
  apply AlgebraicGroup.Morphism.ext
  funext t
  apply T.inclusion_injective
  exact (inclusionPreimageBack_apply T K _).trans (hc t)

omit [IsAlgClosed k] in
theorem weightVector_restrict_overgroup (ρ : RationalRepresentation G E)
    (T K : ClosedSubgroup G) (v : E) (χ : TorusWeight T) (hv : IsWeightVector ρ T v χ) :
    let Ti := K.inclusion.closedSubgroupPreimage T
    let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
    IsWeightVector (representationPullback ρ K.inclusion) Ti v
      (TorusCharacter.pullback (inclusionPreimageBack T K) χ) := by
  dsimp only
  let Ti := K.inclusion.closedSubgroupPreimage T
  let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
  refine ⟨hv.1, ?_⟩
  intro t
  change (ρ.action (K.includePoint (Ti.includePoint t))).1 v =
    χ.pointCharacter ((inclusionPreimageBack T K).onPoints t) • v
  rw [← inclusionPreimageBack_apply]
  exact hv.2 _

theorem pairing_restrict_overgroup (T K : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T) (χ : TorusWeight T) :
    let Ti := K.inclusion.closedSubgroupPreimage T
    let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
    ∀ cK : ClosedSubgroupTorusCocharacter Ti,
      (∀ t, K.includePoint (Ti.includePoint (cK.onPoints t)) = T.includePoint (c.onPoints t)) →
      characterCocharacterPairing Ti cK
        (Additive.ofMul (TorusCharacter.pullback (inclusionPreimageBack T K) χ)) =
          characterCocharacterPairing T c (Additive.ofMul χ) := by
  dsimp only
  let Ti := K.inclusion.closedSubgroupPreimage T
  let : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
  intro cK hc
  rw [characterCocharacterPairing_pullback,
    inclusionPreimageBack_comp_cocharacter T K c cK hc]

theorem projective_action_restrict_equivariant [FiniteDimensional k E]
    (ρ : RationalRepresentation G E)
    (A : MorphicAction G (projectiveSpace k E))
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b p))
    (f : AlgebraicGroup.Morphism H G) (g : Variety.Point H) (p : Point (projectiveSpace k E)) :
    projectiveSpacePointEquivOf b ((A.pullbackGroup f).toMulAction.smul g p) =
      Projectivization.map ((representationPullback ρ f).action g).1
        ((representationPullback ρ f).action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b p) := he (f.onPoints g) p

theorem pointStabilizer_restrict (X : Variety.Geometric k) (A : MorphicAction G X)
    (x : Point X) (f : AlgebraicGroup.Morphism H G) :
    (A.pullbackGroup f).pointStabilizer x = f.closedSubgroupPreimage (A.pointStabilizer x) := by
  apply SetLike.coe_injective
  ext g
  change g ∈ ((A.pullbackGroup f).pointStabilizer x).toSubgroup ↔
    f.onPoints g ∈ (A.pointStabilizer x).toSubgroup
  rw [(A.pullbackGroup f).mem_pointStabilizer, A.mem_pointStabilizer]
  rfl

omit [IsAlgClosed k] in
theorem maximalTorus_le_subtorusCentralizer (S T : ClosedSubgroup G)
    (hT : IsMaximalTorus T) (hST : S ≤ T) : T ≤ S.centralizer := by
  intro t ht
  have hc := maximalTorus_le_centralizer hT ht
  exact fun s hs => hc s (hST hs)

theorem centralizer_restricted_stabilizer_isBorel
    {X : Variety.Geometric k} (hG : Variety.IsConnected G)
    (A : MorphicAction G X) (x : Point X)
    (S : ClosedSubgroup G) (hS : IsSubtorus S)
    (hB : IsBorelSubgroup (A.pointStabilizer x)) (hSB : S ≤ A.pointStabilizer x) :
    IsBorelSubgroup ((A.pullbackGroup S.centralizer.inclusion).pointStabilizer x) := by
  rw [pointStabilizer_restrict]
  exact SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.isBorel_centralizer_restriction
    hG S (A.pointStabilizer x) hS hB hSB

end Theory.AlgebraicGroup.Bor1.SeparatingBorel
