module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticStabilizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticCentralCarrier

/-!
# The marked quintic product in the effective component action

Map the actual component-stabilizer Sylow and the original quintic
subgroup through normalizer conjugation on (K/O₂(K))/Z. Surjective images
preserve Sylow membership, while the two actual set products preserve
permutability. Faithfulness keeps the original five-subgroup of order five.
All three images use the same normalizer action and simple carrier.

Source: Aschbacher--Smith 6.1.4, printed p.665.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The effective image retains the actual Sylow image and a permuting,
faithful order-five image of the original quintic subgroup. -/
theorem original_hermitian_quintic_effective_product
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    Chapter1.IsSylowIn 2 (coreCentralActorImage K (T : Subgroup G))
      (coreCentralActorImage K M₁) ∧
    ∃ D : Subgroup G, Nat.card D = 5 ∧ D ≤ quinticResidual T L ∧
      Nat.card (coreCentralActorImage K D) = 5 ∧
      coreCentralActorImage K D ≤ coreCentralActorImage K M₁ ∧
      (coreCentralActorImage K D : Set (MulAut (coreCentralQuotient K))) *
          (coreCentralActorImage K (T : Subgroup G) : Set (MulAut (coreCentralQuotient K))) =
        (coreCentralActorImage K (T : Subgroup G) : Set (MulAut (coreCentralQuotient K))) *
          (coreCentralActorImage K D : Set (MulAut (coreCentralQuotient K))) := by
  let N := normalizer (K : Set G)
  obtain ⟨hS,D,hD,hDX,hDN,hDT,hTD⟩ :=
    original_hermitian_quintic_component_stabilizer_product h hout hm hM₁ hCM₁ hK
  have hSN : Chapter1.IsSylowIn 2 ((T : Subgroup G).subgroupOf N) (M₁.subgroupOf N) := by
    apply (Chapter1.IsSylowIn.map_iff N.subtype N.subtype_injective).mp
    simpa only [subgroupOf_map_subtype] using hS
  have hmap := Chapter1.Section02.IndexTwo.isSylowIn_map hSN (normalizerCoreCentralAction K)
  refine ⟨hmap,D,hD,hDX,
    original_hermitian_quintic_central_image_card h hout hm hM₁ hCM₁ hK hnot hq D hD hDX,
    map_mono (subgroupOf_mono N (hDN.trans inf_le_left)),?_⟩
  have hperm : (D.subgroupOf N : Set N) * ((T : Subgroup G).subgroupOf N : Set N) =
      ((T : Subgroup G).subgroupOf N : Set N) * (D.subgroupOf N : Set N) := by
    apply Set.image_injective.mpr N.subtype_injective
    have hDNg : D ≤ N := hDN.trans inf_le_right
    simpa only [Set.image_mul,←coe_map,subgroupOf_map_subtype,inf_eq_left.mpr hDNg,N]
      using hDT.trans hTD.symm
  have he := congrArg (Set.image (normalizerCoreCentralAction K)) hperm
  simpa only [coreCentralActorImage,N,Set.image_mul,←coe_map] using he

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
