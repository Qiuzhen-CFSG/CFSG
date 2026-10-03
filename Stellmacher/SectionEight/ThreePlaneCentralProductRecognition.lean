module

public import Stellmacher.LaterDefs
public import Stellmacher.SectionEight.ThreePlaneInvolutionSelection
public import Theory.GroupTheory.ThreeInvolutionRecognition

namespace Stellmacher.SectionEight

open Later

universe u

public theorem three_involution_central_product_and_centralizer_models
    {G : Type u} [Group G] [Finite G]
    (seed whole : Subgroup G) (first second third central : G)
    (relations : ThreeInvolution.Relations first second third central)
    (hgeneration : whole = Subgroup.closure ({first, second, third} : Set G))
    (hseed : seed = Subgroup.closure ({first, central} : Set G)) :
    IsCentralProductModel whole C4 Q8 ∧
      IsModel (whole ⊓ Subgroup.centralizer (seed : Set G)) (C2 × C4) := by
  subst whole seed
  constructor
  · refine ⟨Subgroup.zpowers (first * second * third),
      Subgroup.closure ({first * second, second * third} : Set G), ?_,
      relations.quaternion_model.2, relations.factor_join,
      relations.factor_intersection_card, relations.factor_commute, ?_⟩
    · exact ⟨mulEquivOfCyclicCardEq (by simpa using relations.triple_order)⟩
    · intro element helement
      have hwhole : element ∈ Subgroup.closure ({first, second, third} : Set G) := by
        rw [relations.factor_join]
        exact Subgroup.mem_sup_left helement.1
      refine ⟨⟨element, hwhole⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
      intro other
      exact Subtype.ext (relations.cyclic_factor_centralizes helement.1 other other.property)
  · exact relations.seed_centralizer_model

public theorem three_plane_central_product_and_centralizer_models
    {G : Type u} [Group G] [Finite G]
    (seed actors common whole : Subgroup G)
    (hseedActors : seed ≤ actors)
    (helementary : IsElementaryAbelian 2 seed)
    (hseedCard : Nat.card seed = 4)
    (hcommonCard : Nat.card common = 2)
    (hcommonSeed : common ≤ seed)
    (hcentral : actors ≤ Subgroup.centralizer (common : Set G))
    (hgeneration : whole = conjugateClosure seed actors)
    (hderived : ⁅whole, whole⁆ = common)
    (horbit : ((Subgroup.normalizer (seed : Set G)).subgroupOf actors).index = 3)
    (hsmall : Nat.card whole ≤ 16) :
    IsCentralProductModel whole C4 Q8 ∧
      IsModel (whole ⊓ Subgroup.centralizer (seed : Set G)) (C2 × C4) := by
  obtain ⟨first, second, third, involution, hfirst, hsecond, hthird, hinvolution,
    hne, hcentralFirst, hcentralSecond, hcentralThird, hfirstSecond, hsecondThird,
    hfirstThird, hwhole, hseed⟩ := three_plane_involution_generators seed actors common
      whole hseedActors helementary hseedCard hcommonCard hcommonSeed hcentral
      hgeneration hderived horbit hsmall
  exact three_involution_central_product_and_centralizer_models seed whole first
    second third involution ⟨hfirst, hsecond, hthird, hinvolution, hne, hcentralFirst,
      hcentralSecond, hcentralThird, hfirstSecond, hsecondThird, hfirstThird⟩ hwhole hseed

end Stellmacher.SectionEight
