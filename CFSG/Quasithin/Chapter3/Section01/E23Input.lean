module
public import CFSG.Quasithin.Chapter3.Section01.OmegaMovement
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The genuine intrinsic hypotheses for E.2.3

The original H* is SQTK and has characteristic two. Translate its
unique maximal subgroup and the original Thompson movement to its
intrinsic carrier and Sylow subgroup. The omega-center orbit is the same
original subgroup, and its reducedness was constructed in OmegaModule.
Thus every hypothesis of E.2.3 is proved from the qrc configuration and
the noncentral branch, without any factor or module-classification input.

Source: Aschbacher–Smith, Lemma 3.1.7, printed pp.575–576,
and Lemma E.2.3, printed pp.216–217 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.intrinsic_minimalParabolic
    (h : QrcHypotheses T M M₀ H V) (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤ := by
  apply (ChapterB.isMinimalParabolicOver_top_iff _).mpr
  refine ⟨?_, ?_⟩
  · obtain ⟨B, ⟨hBc, hBT⟩, hb⟩ := HStar.unique_maximal_subgroup T
      (h.sylow_le.trans h.left_le) h.right_mem
    have hSB : ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) ≤ B := by
      intro s hs
      obtain ⟨b, hb, he⟩ := hBT hs
      exact H.subtype_injective he ▸ hb
    refine ⟨B, ⟨hBc, hSB⟩, ?_⟩
    intro C hC
    apply hb C
    refine ⟨hC.1, ?_⟩
    intro t ht
    exact ⟨⟨t, h.right_mem.1.1.2 ht⟩, hC.2 ht, rfl⟩
  · exact ((ChapterB.isMinimalParabolicOver_iff T H).mp
      (h.minimalParabolic_of_thompson_centralizes hM hu hJ)).2

theorem QrcHypotheses.intrinsic_thompson_moves_sylowOmega
    (h : QrcHypotheses T M M₀ H V) (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    ¬ elementaryAbelianMaxJ
        ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) ≤
      centralizer (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) : Set H) := by
  intro hc
  apply h.thompson_moves_sylowOmega hM hu hJ hZ
  have hjmap : (elementaryAbelianMaxJ
      ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le h.right_mem.1.1.2
  have hUH : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H ≤ H :=
    conjugateSpanBy_le
      (fun z hz => h.right_mem.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
      H.le_normalizer
  rw [← hjmap]
  rintro g ⟨j, hj, rfl⟩ z hz
  exact congrArg H.subtype (hc hj ⟨z, hUH hz⟩ hz)

/-- Every hypothesis of E.2.3 holds on the literal intrinsic H and its original omega-orbit. -/
theorem QrcHypotheses.e23_hypotheses
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    IsSQTK K H ∧ generalizedFitting H = pCore 2 H ∧
      ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤ ∧
      IsPReduced 2 ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) ∧
      ¬ elementaryAbelianMaxJ
          ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) ≤
        centralizer (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) : Set H) :=
  ⟨sqtk_of_mem_H hG h.right_mem.1.1.1,
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) h.right_mem.1.1)),
    h.intrinsic_minimalParabolic hM hu hJ,
    h.sylowOmega_reduced (hG.evenCharacteristic T),
    h.intrinsic_thompson_moves_sylowOmega hM hu hJ hZ⟩

end CFSG.Quasithin.Chapter3
