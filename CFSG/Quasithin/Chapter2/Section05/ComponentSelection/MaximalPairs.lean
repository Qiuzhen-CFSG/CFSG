module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalizerCensus
public import Theory.GroupTheory.SelfCentralizingCoreNormalPJoin

/-!
# Maximal local pairs supply the source saturation

Adjoining an H_U-invariant two-subgroup preserves characteristic two in
the actual join H_U P. All other local-pair conditions persist, proving
2.5.3(2). Choose a maximal pair in the finite componentwise order. The join
must equal H_U, so every invariant two-subgroup lies in its two-core.
This constructs the saturation needed by the core-normalizer and component
projection arguments; it is not an extra source hypothesis.

Source: Aschbacher--Smith, Lemma 2.5.3(2,4), printed p.552.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {M H U HU : Subgroup G}

/-- Original 2.5.3(2): the invariant two-subgroup can be adjoined to the
second coordinate while retaining the same beta-subgroup. -/
theorem lemma_2_5_3_two
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (P : Subgroup G) (hPH : P ≤ H) (hp : IsPGroup 2 P)
    (hn : HU ≤ normalizer (P : Set G)) :
    (U, HU ⊔ P) ∈ localPairsIn (Chapter1.He G) M H := by
  have hchar : HU ⊔ P ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (Theory.GroupTheory.centralizer_pCore_sup_le_of_normalized_pgroup HU P
      (Chapter1.mem_He_iff.mp hpair.1.2.1) hp hn)
  have hcore : twoCore (HU ⊔ P) ≠ ⊥ := by
    by_cases hPb : P = ⊥
    · simpa only [hPb, sup_bot_eq] using hpair.1.2.2.1
    · have hPcore : P ≤ twoCore (HU ⊔ P) :=
        le_pCoreIn_of_normalizes hp le_sup_right (sup_le hn P.le_normalizer)
      intro hb
      exact hPb (bot_unique (hb ▸ hPcore))
  exact ⟨⟨hpair.1.1, hchar, hcore, hpair.1.2.2.2.1.trans le_sup_left,
    fun hh => hpair.1.2.2.2.2 (le_sup_left.trans hh)⟩, sup_le hpair.2 hPH⟩

/-- Maximality in the original componentwise order gives the full
invariant-two-subgroup saturation, through the literal join in 2.5.3(2). -/
theorem saturation_of_maximal_pair
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hmax : ∀ V K, (V, K) ∈ localPairsIn (Chapter1.He G) M H →
      U ≤ V → HU ≤ K → V ≤ U ∧ K ≤ HU) :
    ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU := by
  intro P hPH hp hn
  have hPHU : P ≤ HU := le_sup_right.trans
    (hmax U (HU ⊔ P) (lemma_2_5_3_two hpair P hPH hp hn) le_rfl le_sup_left).2
  exact le_pCoreIn_of_normalizes hp hPHU hn

/-- A genuine Gamma member supplies a maximal local pair and hence a
saturated core. No saturation or maximal-pair witness is assumed. -/
theorem exists_saturated_local_pair
    (hH : H ∈ gamma (Chapter1.He G) M) :
    ∃ U HU : Subgroup G, (U, HU) ∈ localPairsIn (Chapter1.He G) M H ∧
      (∀ V K, (V, K) ∈ localPairsIn (Chapter1.He G) M H →
        U ≤ V → HU ≤ K → V ≤ U ∧ K ≤ HU) ∧
      ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
        HU ≤ normalizer (P : Set G) → P ≤ twoCore HU := by
  obtain ⟨⟨U, HU⟩, hp, hmax⟩ :=
    (localPairsIn (Chapter1.He G) M H).toFinite.exists_maximal hH.2
  have hm : ∀ V K, (V, K) ∈ localPairsIn (Chapter1.He G) M H →
      U ≤ V → HU ≤ K → V ≤ U ∧ K ≤ HU := by
    intro V K hv hUV hHK
    exact hmax hv ⟨hUV, hHK⟩
  exact ⟨U, HU, hp, hm, saturation_of_maximal_pair hp hm⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
