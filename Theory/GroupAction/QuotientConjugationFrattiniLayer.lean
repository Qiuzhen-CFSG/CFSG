module

public import Theory.GroupAction.SubgroupQuotientFullAction
public import Mathlib.GroupTheory.Frattini

/-!
# Frattini displacement through a prescribed quotient action

A subgroup centralizing an ambient layer commutes with its distinguished
elements and fixes the layer's image in every prescribed conjugation quotient.
The displacement of a distinguished layer element lies in that image.

If the Frattini subgroup of the actual action image displaces only that
layer image, the Frattini subgroup of the original actor has its ambient
commutator in the layer. The proof uses the surjective core-to-image map
and the quotient kernel containment; it requires no identification of the
full action kernel with the core.

These are transport lemmas for the terminal module preceding Stellmacher
(9.1)(10), printed p.47. They do not prove the structural Frattini bound
for that terminal module.
-/

open scoped commutatorElement
namespace Subgroup

public theorem quotient_conjugation_centralizing_actor_data
    {G : Type*} [Group G] (vertexGroup actedGroup kernel layer core : Subgroup G)
    (hnormalizes : vertexGroup ≤ normalizer (actedGroup : Set G))
    (hnormal : (kernel.subgroupOf actedGroup).Normal)
    (hactedLayer : actedGroup ≤ normalizer (layer : Set G))
    (hcentralizes : core ≤ centralizer (layer : Set G)) :
    let _ := hnormal
    ∀ action : vertexGroup →* MulAut (actedGroup ⧸ kernel.subgroupOf actedGroup),
      (∀ actor : vertexGroup, ∀ point : actedGroup,
        action actor (QuotientGroup.mk' (kernel.subgroupOf actedGroup) point) =
          QuotientGroup.mk' (kernel.subgroupOf actedGroup)
            ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
              (mem_normalizer_iff.mp (hnormalizes actor.property) point).mp point.property⟩) →
      ∀ distinguished : vertexGroup, (distinguished : G) ∈ layer →
        let quotientMap := QuotientGroup.mk' (kernel.subgroupOf actedGroup)
        let displacement := commutatorAction (zpowers (action distinguished))
          (actedGroup ⧸ kernel.subgroupOf actedGroup)
        let layerImage := (layer.subgroupOf actedGroup).map quotientMap
        let actors := (core.subgroupOf vertexGroup).map action
        displacement ≤ layerImage ∧
          (∀ actor ∈ actors, Commute actor (action distinguished)) ∧
          (∀ actor ∈ actors, ∀ point ∈ layerImage, actor point = point) := by
  let _ := hnormal
  dsimp only
  intro action haction distinguished hdistinguished
  let quotientMap := QuotientGroup.mk' (kernel.subgroupOf actedGroup)
  let layerImage := (layer.subgroupOf actedGroup).map quotientMap
  refine ⟨?_, ?_, ?_⟩
  · rw [commutatorAction_eq_closure]
    apply (closure_le (K := layerImage)).mpr
    rintro _ ⟨actor, point, rfl⟩
    have hactor : (actor : MulAut (actedGroup ⧸ kernel.subgroupOf actedGroup)) ∈
        (zpowers distinguished).map action := by
      rw [MonoidHom.map_zpowers]
      exact actor.property
    obtain ⟨representative, hrepresentative, heq⟩ := hactor
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (kernel.subgroupOf actedGroup) point
    have hinLayer : (representative : G) ∈ layer :=
      (zpowers_le.mpr (show distinguished ∈ layer.subgroupOf vertexGroup from
        hdistinguished)) hrepresentative
    change (quotientMap lift)⁻¹ *
      (actor : MulAut (actedGroup ⧸ kernel.subgroupOf actedGroup)) (quotientMap lift) ∈ _
    rw [← heq, haction, ← map_inv, ← map_mul]
    apply mem_map_of_mem
    change (lift : G)⁻¹ *
      ((representative : G) * (lift : G) * (representative : G)⁻¹) ∈ layer
    have hmem := layer.mul_mem
      ((mem_normalizer_iff.mp (hactedLayer (actedGroup.inv_mem lift.property))
        representative).mp hinLayer) (layer.inv_mem hinLayer)
    simpa only [inv_inv, mul_assoc] using hmem
  · rintro actor ⟨representative, hrepresentative, rfl⟩
    apply Commute.map _ action
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hcentralizes hrepresentative)
      distinguished hdistinguished).symm
  · rintro actor ⟨representative, hrepresentative, rfl⟩ point ⟨lift, hlift, rfl⟩
    rw [haction]
    apply congrArg quotientMap
    apply Subtype.ext
    have hcomm : (representative : G) * (lift : G) =
        (lift : G) * (representative : G) :=
      (mem_centralizer_iff.mp (hcentralizes hrepresentative) lift hlift).symm
    change (representative : G) * (lift : G) * (representative : G)⁻¹ = (lift : G)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

public theorem commutator_frattini_le_of_quotient_action
    {G : Type*} [Group G] (vertexGroup actedGroup kernel layer core : Subgroup G)
    (hnormalizes : vertexGroup ≤ normalizer (actedGroup : Set G))
    (hnormal : (kernel.subgroupOf actedGroup).Normal)
    (hkernelLayer : kernel ≤ layer) (hcoreVertex : core ≤ vertexGroup) :
    let _ := hnormal
    ∀ action : vertexGroup →* MulAut (actedGroup ⧸ kernel.subgroupOf actedGroup),
      (∀ actor : vertexGroup, ∀ point : actedGroup,
        action actor (QuotientGroup.mk' (kernel.subgroupOf actedGroup) point) =
          QuotientGroup.mk' (kernel.subgroupOf actedGroup)
            ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
              (mem_normalizer_iff.mp (hnormalizes actor.property) point).mp point.property⟩) →
      (let actors := (core.subgroupOf vertexGroup).map action
       commutatorAction ((frattini actors).map actors.subtype)
          (actedGroup ⧸ kernel.subgroupOf actedGroup) ≤
        (layer.subgroupOf actedGroup).map (QuotientGroup.mk' (kernel.subgroupOf actedGroup))) →
      ⁅(frattini core).map core.subtype, actedGroup⁆ ≤ layer := by
  let _ := hnormal
  dsimp only
  intro action haction hdisplacement
  let actors := (core.subgroupOf vertexGroup).map action
  let quotientMap := QuotientGroup.mk' (kernel.subgroupOf actedGroup)
  let layerImage := (layer.subgroupOf actedGroup).map quotientMap
  let coreAction : core →* actors :=
    { toFun := fun element => ⟨action ⟨element, hcoreVertex element.property⟩,
        mem_map_of_mem action element.property⟩
      map_one' := Subtype.ext (map_one action)
      map_mul' := fun left right => Subtype.ext
        (map_mul action (⟨left, hcoreVertex left.property⟩ : vertexGroup)
          (⟨right, hcoreVertex right.property⟩ : vertexGroup)) }
  have hsurjective : Function.Surjective coreAction := by
    rintro ⟨actor, representative, hrepresentative, rfl⟩
    exact ⟨⟨representative, hrepresentative⟩, rfl⟩
  have hfrattini : frattini core ≤ (frattini actors).comap coreAction :=
    frattini_le_comap_frattini_of_surjective hsurjective
  have hpreimage : layerImage.comap quotientMap = layer.subgroupOf actedGroup := by
    apply comap_map_eq_self
    intro point hpoint
    exact hkernelLayer ((QuotientGroup.eq_one_iff point).mp hpoint)
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro point hpoint _ ⟨coreElement, hcoreElement, rfl⟩
  let actor : vertexGroup := ⟨coreElement, hcoreVertex coreElement.property⟩
  let inversePoint : actedGroup := ⟨point⁻¹, actedGroup.inv_mem hpoint⟩
  let movedPoint : actedGroup :=
    ⟨(coreElement : G) * point⁻¹ * (coreElement : G)⁻¹,
      (mem_normalizer_iff.mp (hnormalizes actor.property) point⁻¹).mp
        (actedGroup.inv_mem hpoint)⟩
  have hactor : action actor ∈ (frattini actors).map actors.subtype := by
    exact ⟨coreAction coreElement, hfrattini hcoreElement, rfl⟩
  have hdisplaced : (quotientMap inversePoint)⁻¹ * action actor
      (quotientMap inversePoint) ∈ layerImage := hdisplacement (by
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨⟨action actor, hactor⟩, quotientMap inversePoint, rfl⟩)
  have heq : action actor (quotientMap inversePoint) = quotientMap movedPoint :=
    haction actor inversePoint
  rw [heq, ← map_inv, ← map_mul] at hdisplaced
  have hmem : inversePoint⁻¹ * movedPoint ∈ layer.subgroupOf actedGroup :=
    hpreimage ▸ hdisplaced
  change ⁅point, (coreElement : G)⁆ ∈ layer
  simpa only [inversePoint, movedPoint, mem_subgroupOf, Subgroup.coe_mul,
    Subgroup.coe_inv, inv_inv, commutatorElement_def, mul_assoc] using hmem

end Subgroup
