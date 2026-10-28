module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.FourNormalizerFixedFive
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingFullCentralizerSource

/-!
The terminal involution in the trivial block-centralizer branch of 2.4.29
cannot be conjugate to the original central involution. The actual component
is A6. Its marked four-group is normalized by the index-two half of the
original two-group and moved by a crossing element. Consequently every
involution outside that half has a five-divisible relative centralizer.
The original centralizer has order 2304, giving the contradiction.

The earlier source owners construct the component, four-group and transfer
involution; this consumer retains their literal ambient subgroup markings.
Source: Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_moving_four_not_isConj
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥)
    (K Tu F : Subgroup G) (hTuK : Tu ≤ normalizer (K : Set G))
    (hTu : IsPGroup 2 Tu) (e : K ≃* AlternatingSix.ShadowLocal.A6)
    [IsKleinFour F] (hFK : F ≤ K) (hFTu : F ≤ Tu)
    (R : Subgroup Tu) (hR : R.index = 2)
    (hRF : R.map Tu.subtype ≤ normalizer (F : Set G))
    (hx : ∃ x ∈ Tu, x ∉ normalizer (F : Set G))
    (i : Tu) (hi : i ∉ R) (hi2 : orderOf (i : G) = 2)
    (z : G) (hz : centralizer ({z} : Set G) = M) : ¬IsConj z (i : G) := by
  intro hc
  have hfive := AlternatingSix.ShadowLocal.five_dvd_centralizer_of_four_normalizer
    K Tu F hTuK hTu e hFK hFTu R hR hRF hx i hi hi2
  have hdiv : Nat.card (K ⊓ centralizer ({(i : G)} : Set G) : Subgroup G) ∣
      Nat.card (centralizer ({(i : G)} : Set G)) := card_dvd_of_le inf_le_right
  have hiM : Nat.card (centralizer ({(i : G)} : Set G)) = Nat.card M := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    let f := MulAut.conj g
    have he : f z = (i : G) := hg
    rw [←he, ←hz]
    symm
    apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
    intro a
    change a ∈ centralizer ({z} : Set G) ↔ f a ∈ centralizer ({f z} : Set G)
    simp only [mem_centralizer_singleton_iff, ←map_mul, f.injective.eq_iff]
  have h := dvd_trans hfive hdiv
  rw [hiM, d.single_alternating_maximal_card_of_centralizer_bot
    hG T hM hTM hu hST hsingle hA hD] at h
  norm_num at h

end CFSG.Quasithin.Chapter2
