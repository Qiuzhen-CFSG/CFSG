module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.NaturalRows
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SmallSourceControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SignedThreeSourceControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.PrimeSourceControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EnlargedControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.JankoFourInvolutionSource
/-!
# The complete natural reduced-source branch of C.5.12

The earlier matched block theorem handles an enlarged auxiliary span.
Otherwise the original larger-component embedding selects every possible
model. The binary models use the proved small-group and prime-field
normalizer bounds; the SL2(5) image uses the marked signed-three bounds.
The full-span quasisimplicity argument excludes the noncentral-Fitting
rows, and the actual moved-action theorem excludes J1 and J4. Thus the
original normalizer of T preserves U(K), with no model or kernel callback.
The genuine universal A.3.12 source implication remains explicit.
Source: Aschbacher--Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
omit [Finite G] in
private theorem natural_not_three {K : Subgroup G} {n : ℕ} (hn : IsL2EvenBlock K n) :
    ¬ IsAlternatingBlock K 3 := by
  intro h3
  obtain ⟨F,_,_,hF,_,hm⟩ := hn.2.2
  obtain ⟨e⟩ := hm.quotient_iso
  obtain ⟨e3⟩ := h3.2.2.quotient_iso
  have hc : Nat.card (K ⧸ pCore 2 K) = 3 := by
    rw [Nat.card_congr e3.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  have hle := Nat.card_le_card_of_injective (Matrix.SpecialLinearGroup.upperUnipotentHom F)
    (Matrix.SpecialLinearGroup.upperUnipotentHom_injective F)
  change Nat.card F ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) at hle
  rw [← Nat.card_congr e.toEquiv,hF,hc] at hle
  have hlo : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn.1
  omega

theorem natural_source_theorem_5_12 {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  rcases natural_source_control_or_auxiliary_eq hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc hVC with hLK | hc
  · have hK : IsChiZeroBlock K := Or.inl ⟨n,hn⟩
    have h3 := natural_not_three hn
    have hUT : U K ≤ T := h.module_le.trans inf_le_left
    have hKX : K ≤ X := le_sup_left.trans hAX
    have h513 := natural_source_normalizer_control hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc
    have hsmall := noncubic_control_of_small_full_span K T X hK h3 hT hUT hTK
      P hP hAX hX S hS hVC
    rcases EmbeddingSelection.natural_full_span_selection hG hA312 h hn h3 hT hTK X hAX hX S hS hVC hLK with he | ⟨hn2,hmodels⟩
    · let V := conjugateSpanBy (U K) X
      let D := conjugateSpanBy K X
      have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
      have hDX : D ≤ X := conjugateSpanBy_le_self hKX
      have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
      have hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
      let : IsElementaryAbelian 2 (U K) := h.short.elementary.map K.subtype
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
      exact noncubic_control_of_normal_span_image K T X V hK h3 hT hTK P hP hAX hVX hXV
        (le_conjugateSpanBy _ _) hnorm h513
    · rcases hmodels with (h7 | hcover | hj | h25 | ⟨p,hp,hpmodel⟩) | ⟨hB,hmodels⟩
      · exact hsmall (.inl h7) h513
      · exact hsmall (.inr (.inl hcover)) h513
      · exact (natural_source_full_span_not_janko h hn hT hTK X hKX hX S hS hVC hj).elim
      · exact hsmall (.inr (.inr h25)) h513
      · have hlarge : 3 < p := by
          by_contra! he
          interval_cases p <;> norm_num [A312ExceptionalPrime] at hp
        exact natural_source_prime_full_span_control hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc hVC
          hp.1 hlarge hpmodel
      · exact noncubic_control_of_signed_three_full_span K T X hK h3 hT hUT hTK P hP hAX hX S hS hVC hLK hB hmodels h513
  · exact hc
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
