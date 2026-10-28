module

public import CFSG.Quasithin.Chapter14.Section01.AlternatingThree.Reduction
public import CFSG.Quasithin.Chapter14.Section01.AlternatingThree.NativeAction
public import Theory.SpecificGroups.Alternating.FourPairThompson
public import CFSG.Quasithin.Chapter13.Section09.SourceSetup
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The original alternating-three exclusion, 14.1.10

The normal orbit and its centralizer alternative are constructed from the
original block and characteristic-two local. In the faithful pair case,
the native Thompson theorem forces the full symmetric wreath image:
a proper image would put [X,J(R)] in an elementary sixteen-group, whereas
X has order twelve. The original 13.9.1 then excludes that maximal local.

The only earlier-source input retained is full 13.9.1, with its actual
Configuration and original simple QTKE hypotheses. Unique-Mc placement,
full automorphism image, and the one-block contradiction are all proved.
No 3.1.1, module classification, or Chapter 15 target is assumed.

Source: Aschbacher--Smith 14.1.10, printed p.978.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.AlternatingThree
open AlternatingFourPair
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original core containment and Thompson movement force the full faithful pair action. -/
theorem faithful_pair_equiv
    (hf : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (S : Sylow 2 G) (X R : Subgroup G) (hb : ChapterC.IsBlock X)
    (ha : ChapterC.IsAlternatingBlock X 3) (hQR : pCore 2 G ≤ R)
    (hm : X = ⁅X,elementaryAbelianMaxJ R⁆)
    (hn : (conjugateSpanBy X (S : Subgroup G)).Normal)
    (hcard : Nat.card (conjugateSpanBy X (S : Subgroup G)) = 144)
    (hc : centralizer (conjugateSpanBy X (S : Subgroup G) : Set G) = ⊥) :
    Nonempty (G ≃* W) := by
  obtain ⟨f,hi,hAlt,htrans,hKR,hXcard,hmove⟩ :=
    Chapter14.AlternatingThree.faithful_pair_native_action hf hr S X R hb ha hQR hm hn hcard hc
  have htop : f.range = ⊤ := by
    by_contra hproper
    have hJ := Thompson.thompson_le_kleinBase f.range (R.map f) hAlt htrans hproper hKR (map_le_range f R)
    have hXK : X.map f ≤ Thompson.kleinBase := by
      rw [hmove]
      exact (commutator_mono le_top hJ).trans (commutator_le_right _ _)
    have hd := card_dvd_of_le hXK
    rw [hXcard,Thompson.kleinBase_card] at hd
    norm_num at hd
  exact ⟨MulEquiv.ofBijective f ⟨hi,MonoidHom.range_eq_top.mp htop⟩⟩

/-- Original 14.1.10, with full 13.9.1 as its explicit earlier input. -/
theorem source_lemma_14_1_10
    (h1391 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleQTKE KnownSimple.IsKnownSimple H → Chapter13.Section09.Configuration H → False)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (X R : Subgroup M) (hb : ChapterC.IsBlock X) (ha : ChapterC.IsAlternatingBlock X 3)
    (hQR : pCore 2 M ≤ R) (_hRT : R ≤ (T.subtype hM.2 : Subgroup M))
    (hm : X = ⁅X,elementaryAbelianMaxJ R⁆) :
    M = Mc ∧ 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G)) := by
  rcases Chapter14.AlternatingThree.source_faithful_pair_reduction
    hG T hM hu hmany X R hb ha hm with hdone | ⟨hn,hc,⟨eN⟩⟩
  · exact hdone
  · have hf : generalizedFitting M = pCore 2 M :=
      generalizedFitting_eq_pCore_of_selfCentralizing 2
        (hG.evenCharacteristic T M hM.1 hM.2)
    have hr : primeRank 3 M ≤ 2 :=
      (hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
    have hcard : Nat.card (conjugateSpanBy X (T.subtype hM.2 : Subgroup M)) = 144 := by
      rw [Nat.card_congr eN.toEquiv]
      change Nat.card (A × A) = 144
      rw [Nat.card_prod,alternatingGroup.card_of_card_eq_four (by norm_num)]
    obtain ⟨e⟩ := faithful_pair_equiv hf hr (T.subtype hM.2) X R hb ha hQR hm hn hcard hc
    exact (h1391 G hG ⟨T,M,hM.1,hM.2,e⟩).elim

end CFSG.Quasithin.Chapter14.AlternatingThree
