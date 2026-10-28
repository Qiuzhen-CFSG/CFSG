module
public import Theory.SpecificGroups.J2HSMultipliers.HSModelComparison
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.CubicCentralizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ThreeRank
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.CubicBlock
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.Cardinality
public import CFSG.Quasithin.ClassificationModels.Families

/-! The original opposite block yields a cubic centralizing the faithful
alternating-five block in the HS quotient. The block order is divisible by
960, whereas the certified native cubic-centralizer bound is 720.
Source: Aschbacher–Smith 2.4.25, printed pp.542–543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi

/-- A literal deleted-five block cannot be centralized by a cubic in HS. -/
theorem hs_no_cubic_centralizing_alternating_block
    (A : Subgroup Sporadic.LeechRelated.HS.Carrier) (hA : IsAlternatingBlock A 5)
    (hU : Nat.card ((blockU A).map A.subtype) = 16)
    (b : Sporadic.LeechRelated.HS.Carrier) (hb : orderOf b = 3)
    (hc : b ∈ centralizer (A : Set Sporadic.LeechRelated.HS.Carrier)) : False := by
  have hU' : Nat.card (blockU A) = 16 := by
    rwa [card_map_of_injective A.subtype_injective] at hU
  have hcore : 16 ∣ Nat.card (pCore 2 A) := by
    rw [←hU']
    exact card_dvd_of_le blockU_le_core
  have hcard : 960 ∣ Nat.card A := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),
      Chapter13.Section05.NormalBranch.DeletedFive.alternatingFive_quotient_card A hA]
    exact Nat.mul_dvd_mul_left 60 hcore
  have hAC : A ≤ centralizer ({b} : Set Sporadic.LeechRelated.HS.Carrier) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hc a ha)
  have hlo := Nat.le_of_dvd (Nat.card_pos (α := A)) hcard
  have hle := Nat.card_le_card_of_injective (Subgroup.inclusion hAC)
    (Subgroup.inclusion_injective hAC)
  have hhi := Sporadic.LeechRelated.HS.CubicCentralizer.centralizer_card_le b hb
  omega

variable {G : Type*} [Group G] [Finite G]
variable {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

/-- The HS row of the original paired alternating-five terminal argument. -/
theorem AlternatingPairSourceSetup.hs_overcomponent_false
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
      SI S L ≤ normalizer (K.map GI.subtype : Set G) →
      Nonempty ((K ⧸ pCore 2 K) ≃* ClassificationModels.SporadicName.hs.Carrier) → False := by
  intro S L GI K hK hLK _ hm
  change Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.HS.Carrier) at hm
  exact c.cubic_block_centralizer_overcomponent_false
    hG T hM hTM hu hST hSM hMT hi
    Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot
    Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank
    (IsPGroup.of_card_dvd_pow (n := 1) Sporadic.LeechRelated.HS.outer_card_dvd_two)
    hs_no_cubic_centralizing_alternating_block K hK hLK hm

end CFSG.Quasithin.Chapter2
