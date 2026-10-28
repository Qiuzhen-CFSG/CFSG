module
public import Theory.SpecificGroups.Held.CubicCentralizers.Terminal
public import Theory.SpecificGroups.Held.LocalPairs.Faithfulness
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.CubicBlock
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.Cardinality
public import CFSG.Quasithin.ClassificationModels.Families

/-! The original opposite block gives a cubic centralizing a faithful
alternating-five block in the Held quotient. The block order is divisible by
960. The certified native cubic centralizers have order not divisible by 960.
Source: Aschbacher–Smith 2.4.25, printed pp.542–543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi

/-- A literal deleted-five block cannot be centralized by a cubic in Held. -/
theorem held_no_cubic_centralizing_alternating_block
    (A : Subgroup Held.He) (hA : IsAlternatingBlock A 5)
    (hU : Nat.card ((blockU A).map A.subtype) = 16)
    (b : Held.He) (hb : orderOf b = 3)
    (hc : b ∈ centralizer (A : Set Held.He)) : False := by
  have hU' : Nat.card (blockU A) = 16 := by
    rwa [card_map_of_injective A.subtype_injective] at hU
  have hcore : 16 ∣ Nat.card (pCore 2 A) := by
    rw [←hU']
    exact card_dvd_of_le blockU_le_core
  have hcard : 960 ∣ Nat.card A := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),
      Chapter13.Section05.NormalBranch.DeletedFive.alternatingFive_quotient_card A hA]
    exact Nat.mul_dvd_mul_left 60 hcore
  have hAC : A ≤ centralizer ({b} : Set Held.He) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hc a ha)
  exact Held.CubicCentralizers.not_960_dvd_centralizer b hb
    (hcard.trans (card_dvd_of_le hAC))

private theorem held_three_rank_ge_two : 2 ≤ primeRank 3 Held.He := by
  by_contra hh
  have hr : primeRank 3 Held.He ≤ 1 := by omega
  let P : Sylow 3 Held.He :=
    Held.CubicCentralizers.three_sylow.1.toSylow Held.CubicCentralizers.three_sylow.2
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  have hc : IsMulCommutative Held.OddCubeCandidates.three :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy =>
      (isMulCommutative_iff_of_setLike.mp (inferInstance : IsMulCommutative P))
        x hx y hy
  exact Held.OddCubeCandidates.three_not_commutative hc

private theorem held_outer_two : IsPGroup 2 (MulAut.Outer Held.He) :=
  Subgroup.isPGroup_outer_of_normalizer Held.permutationGroup 2
    Held.Realization.normalizer_surjective
    Held.isPGroup_permutationNormalizerQuotient

variable {G : Type*} [Group G] [Finite G]
variable {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

/-- The Held row of the original paired alternating-five terminal argument. -/
theorem AlternatingPairSourceSetup.held_overcomponent_false
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
      Nonempty ((K ⧸ pCore 2 K) ≃* ClassificationModels.SporadicName.he.Carrier) → False := by
  intro S L GI K hK hLK _ ⟨e⟩
  change (K ⧸ pCore 2 K) ≃* Held.He at e
  let : IsQuasisimple K := hK.2
  let : IsQuasisimple Held.He := IsQuasisimple.of_surjective
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact c.cubic_block_centralizer_overcomponent_false
    hG T hM hTM hu hST hSM hMT hi
    Held.LocalPairs.center_eq_bot held_three_rank_ge_two held_outer_two
    held_no_cubic_centralizing_alternating_block K hK hLK ⟨e⟩

end CFSG.Quasithin.Chapter2
