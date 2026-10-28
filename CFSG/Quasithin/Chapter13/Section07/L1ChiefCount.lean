module

public import CFSG.Quasithin.Chapter13.Section07.sourceL1CubicQuotient
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients

/-!
# The original local residual's complete chief count

A common actual cubic lies in the two-conjugate pair I and an L-conjugate
of L₁. The original Q normalizes both groups, so both intersections with Q
contain every cubic displacement of Q and have the same cubic fixed index.
The literal S₃ and A₄ quotient maps then show that L₁ has exactly one more
noncentral binary chief factor than I. Combining this comparison with the
proved pair count establishes the full original 13.7.10(8).

The last theorem is the numerical use in 13.7.13: its preceding five-factor
lower bound implies m(A*) ≥ 3. Construction of that lower bound and the
rank-four classification argument remain independent source obligations.

Source: Aschbacher–Smith, 13.7.10(8) and 13.7.13, printed pp.942–943.
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement NoncentralChiefRefinement.CubicComparison
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Original 13.7.10(8), for every complete chief series of the literal L₁. -/
theorem source_L1_full_chief_count
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    (s : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁)
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount = Nat.log 2 (Nat.card
      (((conjugate (Section08.Source.VH H V) (g : G) ⊓
        (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
          (QuotientGroup.mk' (pCore 2 H)))) + 2 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  let I := Section08.Source.VH H V ⊔ conjugate (Section08.Source.VH H V) (g : G)
  obtain ⟨A,l,hAc,hAI,hAJ⟩ := pair_common_cubic d h hU hV g hs hspan hout
  let J := conjugate F.L₁ (l : G)
  obtain ⟨hIX,hJX,hQI,hQJ⟩ := pair_core_normalizes d h hU g l
  have hQX : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hQ : IsPGroup 2 Q := (pCore_isPGroup (p := 2) (G := X)).map X.subtype
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hAc)
  have hlength := intersection_lengths_eq A Q I J hA hQ hAI hAJ hQI hQJ
    (hIX.trans hQX) (hJX.trans hQX)
  obtain ⟨f,hf,hfk⟩ := pair_symmetricThree_surjection d h hU hV g hout
  obtain ⟨j,hj,hjk⟩ := conjugate_local_residual_surjection d h hU hV l
  have hfc : IsPGroup 2 f.ker := by rw [hfk]; exact hQ.comap_subtype
  have hjc : IsPGroup 2 j.ker := by rw [hjk]; exact hQ.comap_subtype
  have hAIc : Nat.card (A.subgroupOf I) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAI).toEquiv).trans hAc
  have hAJc : Nat.card (A.subgroupOf J) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hAc
  have hfi : conjugationCubicLength (A.subgroupOf I) f.ker =
      conjugationCubicLength A (Q ⊓ I) := by
    rw [hfk]
    have he := length_subgroupOf A (I ⊓ Q) I hAI inf_le_left
    rw [inf_subgroupOf_left] at he
    simpa only [inf_comm] using he
  have hji : conjugationCubicLength (A.subgroupOf J) j.ker =
      conjugationCubicLength A (Q ⊓ J) := by
    rw [hjk]
    have he := length_subgroupOf A (J ⊓ Q) J hAJ inf_le_left
    rw [inf_subgroupOf_left] at he
    simpa only [inf_comm] using he
  obtain ⟨t,ht0,ht1⟩ := exists_chiefSeries (⊥ : NormalNode I) ⊤ bot_le
  have htc := symmetricThree_count f hf hfc (A.subgroupOf I) hAIc t ht0 ht1
  have htp := pair_full_chief_count d h hU hV g hs hspan hout t ht0 ht1
  let e : F.L₁ ≃* J := (MulAut.conj (l : G)⁻¹).subgroupMap F.L₁
  obtain ⟨hs0,hs1⟩ := s.mapActor_complete e h0 h1
  have hsc := alternatingFour_count j hj hjc (A.subgroupOf J) hAJc
    (s.mapActor e) hs0 hs1
  rw [s.mapActor_noncentralTwoCount, hji, ← hlength, ← hfi, ← htc, htp] at hsc
  omega

/-- The source choice of g supplies the exact L₁ count without a chosen-pair premise. -/
theorem exists_source_L1_chief_count
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g))^2 = 1 ∧
      V ≤ V₃ ⊔ conjugate V₁ (g : G) ∧
      ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃ ∧
      ∀ s : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁,
        s.head = ⊥ → s.last = ⊤ →
        s.noncentralTwoCount = Nat.log 2 (Nat.card
          (((conjugate (Section08.Source.VH H V) (g : G) ⊓
            (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
              (QuotientGroup.mk' (pCore 2 H)))) + 2 := by
  obtain ⟨g,hs,hspan⟩ := exists_chosen_conjugator d
  have hout := ConjugateIntersections.lemma_13_7_10_one h (g : G) hspan hU hV
  exact ⟨g,hs,hspan,hout,fun s h0 h1 =>
    source_L1_full_chief_count d h hU hV (inclusion le_sup_left g) hs hspan hout s h0 h1⟩

/-- The numerical inference in original 13.7.13, applied to its literal full
L₁ series. The five-factor lower bound is its separate preceding source input. -/
theorem source_13_7_13_rank_bound
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    (s : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁)
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) (hfive : 5 ≤ s.noncentralTwoCount) :
    3 ≤ Nat.log 2 (Nat.card
      (((conjugate (Section08.Source.VH H V) (g : G) ⊓
        (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
          (QuotientGroup.mk' (pCore 2 H)))) := by
  rw [source_L1_full_chief_count d h hU hV g hs hspan hout s h0 h1] at hfive
  omega

end CFSG.Quasithin.Chapter13.Section07
