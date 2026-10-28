module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalTheoremKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.PrimeComponentControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceShort
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalNormalizer
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.FullSpanKernel
/-!
# Known-simple source PrimeControl

The original prime-field larger-span normalizer bound now uses the proved known-simple C.5.13 conclusion. Its matched block alternatives supply shortness, and the literal auxiliary normalizer bound supplies the second input. Thus the exact prime-component control has no embedding-classification premise.

Source: Aschbacher–Smith C.5.8–13, printed pp.160–163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
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

theorem natural_source_prime_full_span_control_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hmodel : let D := conjugateSpanBy K X
      ClassicalGroup.IsPSL ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 2 p) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  let V := conjugateSpanBy (U K) X
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  let : IsElementaryAbelian 2 (U K) := h.short.elementary.map K.subtype
  let : IsMulCommutative V := (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
  let : IsElementaryAbelian 2 V := conjugateSpanBy_elementary_of_commutative (U K) X
  have hfull := natural_source_theorem_5_13_knownSimple hG h hn hT hTK P hP X hA hAX hX S hS hx hnc
  have hshort : IsShort (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
    rcases hfull.2 with he | ⟨_,he⟩
    · rw [he]; exact h.short
    · exact he.1
  have h513 := hfull.1
  have hr := noncubic_full_span_reduced K T (Or.inl ⟨n,hn⟩) (natural_not_three hn)
    (h.module_le.trans inf_le_left) hT hTK X hKX S hS hVC
  let : (V.subgroupOf X).Normal := hr.normal
  obtain ⟨eD⟩ := (noncubic_full_span_kernel K T X (Or.inl ⟨n,hn⟩) (natural_not_three hn)
    (h.module_le.trans inf_le_left) hT hTK hKX hX S hS hVC).2.2.2.1
  exact noncubic_prime_component_control K T X V (Or.inl ⟨n,hn⟩) (natural_not_three hn)
    (h.module_le.trans inf_le_left) hT hTK P hP hA hAX S hS hVX hXV
    (le_conjugateSpanBy _ _) hshort hp hlarge (hmodel.of_mulEquiv eD.symm) h513

theorem alternating_source_prime_full_span_control_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hmodel : let D := conjugateSpanBy K X
      ClassicalGroup.IsPSL ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 2 p) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  let V := conjugateSpanBy (U K) X
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  let : IsElementaryAbelian 2 (U K) := h.block.2.1.elementary.map K.subtype
  let : IsMulCommutative V := (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
  let : IsElementaryAbelian 2 V := conjugateSpanBy_elementary_of_commutative (U K) X
  have hfull := alternating_source_theorem_5_13_knownSimple hG h hTK P hP X hA hAX hX S hS hx hnc
  have hshort : IsShort (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
    rcases hfull.2 with he | he
    · rw [he]; exact h.block.2.1
    · exact he.2.1
  have h513 := hfull.1
  have hr := noncubic_full_span_reduced K T (Or.inr (Or.inr h.block)) (alternating_not_three h.block)
    (h.module_le.trans inf_le_left) h.twoGroup hTK X hKX S hS hVC
  let : (V.subgroupOf X).Normal := hr.normal
  obtain ⟨eD⟩ := (noncubic_full_span_kernel K T X (Or.inr (Or.inr h.block)) (alternating_not_three h.block)
    (h.module_le.trans inf_le_left) h.twoGroup hTK hKX hX S hS hVC).2.2.2.1
  exact noncubic_prime_component_control K T X V (Or.inr (Or.inr h.block)) (alternating_not_three h.block)
    (h.module_le.trans inf_le_left) h.twoGroup hTK P hP hA hAX S hS hVX hXV
    (le_conjugateSpanBy _ _) hshort hp hlarge (hmodel.of_mulEquiv eD.symm) h513

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
