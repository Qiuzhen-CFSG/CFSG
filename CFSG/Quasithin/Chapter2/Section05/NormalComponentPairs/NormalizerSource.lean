module

public import CFSG.Quasithin.Chapter2.Section05.LargestPairSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Source

/-!
# Normal two-subgroup normalizers of the original largest local pairs

A normal two-subgroup of a largest local pair, containing the distinguished
central Sylow involution z, has a characteristic-two ambient normalizer by
1.1.4(3). That normalizer remains a local pair with the original base.
Extending the base to a Sylow and applying its global order maximality
forces equality. Thus the normalizer lies in Gamma and the original base
is Sylow in it.

This is the whole implication of Aschbacher--Smith 2.5.12(4), printed
pp.557--558. It holds before the normal-component four-group classification.
The final application retains the original source tuple and its literal z.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05
open A6Shadow.Frattini ComponentRefinement
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
  {M H U L Q : Subgroup G} {z : G}

/-- The normalizer conclusion of 2.5.12(4), for any original largest pair. -/
theorem largest_pair_normal_two_normalizer
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G)
    (hp : (U, L) ∈ largestLocalPairs M H)
    (hz : orderOf z = 2)
    (hzT : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype)
    (hQ : IsPGroup 2 Q) (hzQ : z ∈ Q) (hLN : L ≤ normalizer (Q : Set G)) :
    normalizer (Q : Set G) ∈ gamma (Chapter1.He G) M ∧
      ∃ P : Sylow 2 (normalizer (Q : Set G)),
        (P : Subgroup (normalizer (Q : Set G))).map
          (normalizer (Q : Set G)).subtype = U := by
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hQne : Q ≠ ⊥ := by
    intro he
    exact hz1 (mem_bot.mp (he ▸ hzQ))
  have hZQ : (center (T : Subgroup G)).map (T : Subgroup G).subtype ⊓ Q ≠ ⊥ := by
    intro he
    exact hz1 (mem_bot.mp (he ▸ (show z ∈ _ from ⟨hzT, hzQ⟩)))
  have hN := (Chapter1.lemma_1_1_4_3 T (hG.evenCharacteristic T) hQne hQ hZQ).2.2
  let N := normalizer (Q : Set G)
  have hcore : twoCore N ≠ ⊥ := by
    intro he
    have hle : Q ≤ twoCore N :=
      le_pCoreIn_of_normalizes hQ Q.le_normalizer le_rfl
    exact hQne (bot_unique (he ▸ hle))
  have hpair : (U, N) ∈ localPairs (Chapter1.He G) M :=
    ⟨hp.1.1.1, hN, hcore, hp.1.1.2.2.2.1.trans hLN,
      fun hn => hp.1.1.2.2.2.2 (hLN.trans hn)⟩
  refine ⟨localPair_snd_mem_gamma hpair, ?_⟩
  obtain ⟨P, hUP, hPb⟩ := beta_exists_sylow hpair.1 hpair.2.2.2.1
  have hp' : ((P : Subgroup N).map N.subtype, N) ∈ localPairs (Chapter1.He G) M :=
    ⟨hPb, hN, hcore, map_subtype_le _, hpair.2.2.2.2⟩
  exact ⟨P, (eq_of_le_of_card_ge hUP (hp.2 _ ⟨N, hp'⟩)).symm⟩

/-- Literal application of 2.5.12(4) to the original Chapter 2 component tuple. -/
theorem largest_pair_normal_two_normalizer_of_source
    {K : Subgroup G} {S : Sylow 2 H}
    (c : MathieuSourceSetup H K M S z) (hG : IsSimpleQTKE κ G)
    (hp : (U, L) ∈ largestLocalPairs M H)
    (hQ : IsPGroup 2 Q) (hzQ : z ∈ Q) (hLN : L ≤ normalizer (Q : Set G)) :
    normalizer (Q : Set G) ∈ gamma (Chapter1.He G) M ∧
      ∃ P : Sylow 2 (normalizer (Q : Set G)),
        (P : Subgroup (normalizer (Q : Set G))).map
          (normalizer (Q : Set G)).subtype = U :=
  Section05.largest_pair_normal_two_normalizer hG c.T hp c.involution c.mem_center
    hQ hzQ hLN

end CFSG.Quasithin.Chapter2.Section05
