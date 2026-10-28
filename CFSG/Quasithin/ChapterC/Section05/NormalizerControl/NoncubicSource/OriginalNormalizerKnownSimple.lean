module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalNormalizer
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.AuxiliaryKnownSimple

/-!
# The original auxiliary normalizer control with the full source catalogue

The complete known-simple auxiliary selector now supplies the original
C.5.13 alternatives directly. The moved-module ratio excludes the triple
A₇, J₁ and odd-linear survivors, leaving the actual A₇ calculation or
equality of the auxiliary span and the original block. This yields the
normalizer bound for both the natural and alternating-five source markings.

No A.3.12 premise remains in these original auxiliary normalizer bounds.
The later full-span control in X uses a separate quotient argument.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02
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

private theorem noncubic_control_of_source_ratio (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hq : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      let V := conjugateSpanBy (omegaOneCenterAmbient T) N
      let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
      let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
      let : IsElementaryAbelian 2 V := hs.1
      let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
      quadraticRatio (DualOffender.movedRepresentation (V.subgroupOf N) (K.subgroupOf N)).dual ≤ 2) :
    (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (U K : Set G) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  have hrows := EmbeddingSelection.source_embedding_selection_knownSimple hG
    K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  rcases hrows with he | ⟨_htype,_hfour,hmodels⟩
  · have hn : N ≤ normalizer (K : Set G) := by
      rw [← he]
      exact le_normalizer_conjugateSpanBy K N
    exact inf_le_left.trans (hn.trans (normalizer_le_normalizer_characteristic_image K (blockU K)))
  · apply noncubic_control_of_alternatingSeven_image K T X hK h3 hT hUT hTK P hP hA hAX S hS
    have hex := DualOffender.moved_model_exclusions_of_reduced (V.subgroupOf N) (K.subgroupOf N)
      hs.2.2.2.2.2.2.1 hq
    rcases hmodels with h | h | h | h | ⟨p,hp,h⟩
    · exact h
    · exact (DualOffender.moved_not_triple_seven_of_reduced _ _ hs.2.2.2.2.2.2.1 hq h).elim
    · exact (hex.2 h).elim
    · exact (hex.1 h).elim
    · have hf := (DualOffender.noncubic_source_moved_faithful K T X hK h3 hT hUT hTK P hP hA hAX S hS).2
      have hfix := DualOffender.noncubic_source_moved_dual_fixed K T X hK h3 hT hUT hTK P hP hA hAX S hS
      exact (DualOffender.not_exceptional_prime_of_fixed_cubic _ hf hfix
        ((cubicRatio_le_quadraticRatio _).trans hq) hp h).elim

/-- The original natural marking proves the auxiliary normalizer bound. -/
theorem natural_source_normalizer_control_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (U K : Set G) := by
  exact noncubic_control_of_source_ratio hG K T X (Or.inl ⟨n,hn⟩)
    (natural_not_three hn) hT (h.module_le.trans inf_le_left) hTK
    P hP hA hAX hX S hS
    (DualOffender.natural_source_moved_dual_ratio h hn hT hTK P hP X hA hAX hx hnc)

/-- The original A₅ marking proves the same bound on its entire central cover. -/
theorem alternating_source_normalizer_control_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (sourceModule K : Set G) := by
  exact noncubic_control_of_source_ratio hG K T X (Or.inr (Or.inr h.block))
    (alternating_not_three h.block) h.twoGroup (h.module_le.trans inf_le_left) hTK
    P hP hA hAX hX S hS
    (DualOffender.alternating_source_moved_dual_ratio h hTK P hP X hA hAX hx hnc)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
