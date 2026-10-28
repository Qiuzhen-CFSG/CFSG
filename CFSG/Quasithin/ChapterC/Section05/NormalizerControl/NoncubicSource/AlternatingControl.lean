module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.FixedFreeRows
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SmallSourceControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.PrimeSourceControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EnlargedControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.JankoFourInvolutionSource
/-!
# The complete A₅ reduced-source branch of C.5.12

C.5.13 first removes the enlarged auxiliary block. In the equality case,
the original A₅ module has zero fixed layer, so the genuine larger A.3.12
row selection applies. The original J₁/J₄ displacement exclusions and
all remaining classical/alternating normalizer bounds close every row.
Only the genuine universal A.3.12 implication and original reduced-source
hypotheses remain; no model selection, centralizer, or kernel callback is assumed.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
omit [Finite G] in
private theorem alternating_not_three {K : Subgroup G} (h : IsAlternatingBlock K 5) :
    ¬ IsAlternatingBlock K 3 := by
  intro h3
  obtain ⟨e5⟩ := h.2.2.quotient_iso
  obtain ⟨e3⟩ := h3.2.2.quotient_iso
  have hc := Nat.card_congr (e5.symm.trans e3).toEquiv
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  have hthree : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  rw [h5,hthree] at hc
  norm_num at hc

theorem alternating_source_theorem_5_12 {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  rcases alternating_source_control_or_auxiliary_eq hG hA312 h hTK P hP X hA hAX hX S hS hx hnc hVC with hLK | hc
  · have hK : IsChiZeroBlock K := Or.inr (Or.inr h.block)
    have h3 := alternating_not_three h.block
    have hUT : U K ≤ T := h.module_le.trans inf_le_left
    have hKX : K ≤ X := le_sup_left.trans hAX
    have h513 := alternating_source_normalizer_control hG hA312 h hTK P hP X hA hAX hX S hS hx hnc
    have hJ4 := alternating_source_full_span_not_jankoFour h hTK X hKX hX S hS hVC
    have hsmall := noncubic_control_of_small_full_span K T X hK h3 h.twoGroup hUT hTK
      P hP hAX hX S hS hVC
    rcases EmbeddingSelection.fixedFree_full_span_selection hG hA312 K T X hK h3 hUT h.twoGroup
      hTK hAX hX S hS hVC h.block.blockFixed_eq_bot hLK hJ4 with he | h7 | hcover | hj | h25 | ⟨p,hp,hpmodel⟩
    · let V := conjugateSpanBy (U K) X
      let D := conjugateSpanBy K X
      have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
      have hDX : D ≤ X := conjugateSpanBy_le_self hKX
      have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
      have hr := noncubic_full_span_reduced K T hK h3 hUT h.twoGroup hTK X hKX S hS hVC
      let : IsElementaryAbelian 2 (U K) := h.block.2.1.elementary.map K.subtype
      let : IsMulCommutative V := (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
      let : IsElementaryAbelian 2 V := conjugateSpanBy_elementary_of_commutative (U K) X
      let : (V.subgroupOf X).Normal := hr.normal
      let : (D.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hDX).mpr
        (le_normalizer_conjugateSpanBy K X)
      let φ := twoCoreToCentralizer (V.subgroupOf X) hr
      let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
      have heq : (K.subgroupOf X).map q = (D.subgroupOf X).map q := by
        have hm := congrArg (Subgroup.map φ) he
        rwa [twoCoreToCentralizer_image,twoCoreToCentralizer_image] at hm
      have hnorm : (((conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))).subgroupOf X).map q).Normal := by
        rw [hLK,heq]
        infer_instance
      exact noncubic_control_of_normal_span_image K T X V hK h3 h.twoGroup hTK P hP hAX hVX hXV
        (le_conjugateSpanBy _ _) hnorm h513
    · exact hsmall (.inl h7) h513
    · exact hsmall (.inr (.inl hcover)) h513
    · exact (alternating_source_full_span_not_janko h hTK X hKX hX S hS hVC hj).elim
    · exact hsmall (.inr (.inr h25)) h513
    · have hlarge : 3 < p := by
        by_contra! he
        interval_cases p <;> norm_num [A312ExceptionalPrime] at hp
      exact alternating_source_prime_full_span_control hG hA312 h hTK P hP X hA hAX hX S hS hx hnc hVC
        hp.1 hlarge hpmodel
  · exact hc
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
