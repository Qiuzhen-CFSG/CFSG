module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import Theory.GroupTheory.Commutator.EqualImages
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Reductions for the rank-two component exclusion

For a minimal member `I` of `H₊`, once `Y₊ ≤ L ≤ I` and `L ≰ M`,
minimality gives `I = LS`. The nontrivial two-core needed for `LS ∈ H₊`
comes from `O₂(I) ≤ S`; it is not an additional premise. Passing to the
actual centralizer quotient then gives the simple generalized Fitting
subgroup in 15.3.41(1). Case (2) of Hypothesis 15.3.10 also forces `Y₊ < Y`.

The diagonal, rank-one-factor, and simple-group local analyses remain to
be supplied before 15.3.35 or 15.3.39--42 can be asserted in full.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), pp.1137--1139.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G]

/-- The minimality step preceding 15.3.41. It proves that `LS` belongs to
the actual outside family before applying minimality. -/
theorem eq_component_join_of_minimal
    {M Yplus S I L : Subgroup G}
    (hI : I ∈ minimalOutsideFamily Yplus S M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hYL : Yplus ≤ L) (hLI : L ≤ I) (hLM : ¬ L ≤ M) : I = L ⊔ S := by
  have hSI : S ≤ I := le_sup_right.trans hI.1.1.2
  have hLSI : L ⊔ S ≤ I := sup_le hLI hSI
  have hcoreS : I.pCoreIn 2 ≤ S := hP ▸ pCoreIn_le_sylow I P
  have hnorm : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
    I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hcore : I.pCoreIn 2 ≤ (L ⊔ S : Subgroup G).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
      (hcoreS.trans le_sup_right) (hLSI.trans hnorm)
  have hLS : L ⊔ S ∈ outsideFamily Yplus S M := by
    refine ⟨⟨?_, sup_le_sup hYL le_rfl⟩, ?_⟩
    · intro hz
      exact hI.1.1.1 (le_bot_iff.mp (hcore.trans hz.le))
    · intro h
      exact hLM (le_sup_left.trans h)
  exact le_antisymm (hI.2 hLS hLSI) hLSI

/-- The quotient part of 15.3.41(1), with the component classification
left to the separate 1.1.5 input. -/
theorem simple_generalizedFitting_of_join [Finite G]
    {I L S : Subgroup G} [(L.subgroupOf I).Normal] [IsQuasisimple L]
    (hLI : L ≤ I) (hI : I = L ⊔ S) (hS : IsPGroup 2 S) :
    IsSimpleGroup (componentImage I L L) ∧
      generalizedFitting (ComponentQuotient I L) = componentImage I L L := by
  let : IsQuasisimple (L.subgroupOf I) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLI).symm
  have hgen : L.subgroupOf I ⊔ S.subgroupOf I = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLI,
      map_subgroupOf_eq_of_le (hI ▸ le_sup_right)]
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hI.symm
  have hp : IsPGroup 2 (I ⧸ L.subgroupOf I) :=
    isPGroup_quotient_of_sup_eq_top _ _ hS.comap_subtype hgen
  exact ⟨centralizerQuotientComponent_simple (L.subgroupOf I),
    centralizerQuotient_generalizedFitting (L.subgroupOf I) hp⟩

/-- The quotient-normalizer assertion used in 15.3.41(2). Containment of
the kernel in `M` follows from `Y₊ ≤ L`; the `θ` identity is 15.3.11(6).
Here the ambient group is the source's `I`, so `M` denotes `M_I`. -/
theorem normalizer_component_image
    (L Yplus M : Subgroup G) [L.Normal]
    (hYL : Yplus ≤ L) (hθ : theta M = Yplus)
    (hN : normalizer (Yplus : Set G) = M) :
    normalizer (Yplus.map (centralizerQuotientMap L) : Set (CentralizerQuotient L)) =
      M.map (centralizerQuotientMap L) := by
  have hker : (centralizerQuotientMap L).ker ≤ M := by
    rw [centralizerQuotientMap, QuotientGroup.ker_mk', ← hN]
    exact (centralizer_le hYL).trans (Subgroup.centralizer_le_normalizer _)
  exact image_normalizer_of_theta (centralizerQuotientMap L)
    (QuotientGroup.mk'_surjective _) Yplus M (hθ ▸ theta_le M) hker hθ hN

/-- The strict-containment clause of 15.3.35 follows from genuine
uniqueness for `YS` and membership of `I` in `H₊`. -/
theorem yplus_lt_of_caseTwo [Finite G]
    {M Y S V₁ Yplus I : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M) (hcase : CaseTwo M Y S V₁ Yplus) :
    Yplus < Y := by
  have hle : Yplus ≤ Y := hcase.2 ▸ (map_subtype_le _).trans inf_le_left
  apply lt_of_le_of_ne hle
  intro heq
  have hnorm : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
    I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  apply hI.2
  apply hnorm.trans
  apply normalizer_le_of_unique_maximalTwoLocal hcase.1.2.2
    (isPGroup_pCoreIn 2 I) hI.1.1
  exact (heq ▸ hI.1.2).trans hnorm

/-- The final contradiction on p.1139. Only the image's nontriviality and
order bound are needed; injectivity of the four-group in the quotient is
not assumed. `hirred` is irreducibility of conjugation on the radical,
expressed through its invariant subgroups. The parabolic calculation must
establish it for the actual radical before this lemma can be applied. -/
theorem no_irreducible_sixteen_radical [Finite G]
    (L Yplus J V₂ : Subgroup G) [L.Normal]
    (hYL : Yplus ≤ L) (hV : ⁅V₂, Yplus⁆ = V₂) (hcardV : Nat.card V₂ = 4)
    (hJV : J ≤ normalizer (V₂ : Set G))
    (R : Subgroup (CentralizerQuotient L)) (hcardR : Nat.card R = 16)
    (hVR : V₂.map (centralizerQuotientMap L) ≤ R)
    (hirred : ∀ W : Subgroup (CentralizerQuotient L), W ≤ R →
      J.map (centralizerQuotientMap L) ≤ normalizer (W : Set (CentralizerQuotient L)) →
      W = ⊥ ∨ W = R) : False := by
  let q := centralizerQuotientMap L
  have hne : V₂.map q ≠ ⊥ := by
    intro hz
    have hker : V₂ ≤ q.ker := (map_eq_bot_iff V₂).mp hz
    have hc : V₂ ≤ centralizer (Yplus : Set G) := by
      apply hker.trans
      simpa only [q, centralizerQuotientMap, QuotientGroup.ker_mk'] using
        centralizer_le hYL
    have hb : V₂ = ⊥ := hV.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hc)
    have horder := V₂.card_eq_one.mpr hb
    omega
  have hnormal : J.map q ≤ normalizer (V₂.map q : Set (CentralizerQuotient L)) :=
    (map_mono hJV).trans (V₂.le_normalizer_map q)
  rcases hirred (V₂.map q) hVR hnormal with hz | heq
  · exact hne hz
  · have hbound : Nat.card (V₂.map q) ≤ Nat.card V₂ :=
      Nat.le_of_dvd Nat.card_pos (V₂.card_map_dvd q)
    rw [heq, hcardR, hcardV] at hbound
    omega

end CFSG.Quasithin.Chapter15.Section03.RankTwo
