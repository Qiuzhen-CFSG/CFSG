module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Quotient
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.FullFixedPoint
/-!
# The full central-cover natural branch of C.5.13

I.2.3(2), proved for the actual normalizing two-group, supplies the noncentral
omega-center seed. Its K-span is all of U, including the central layer.
The resulting literal action quotient retains the original natural SL₂ model.
Source: Aschbacher–Smith C.5.13, printed p.162, and I.2.3(2), printed p.413.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {T K : Subgroup G}
/-- The genuine natural block supplies its full-Sylow noncentral seed.
The central layer is retained and may be moved by the normalizing group. -/
theorem natural_noncentral_fixed {n : ℕ} (hn : IsL2EvenBlock K n)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G)) :
    ¬ U K ⊓ omegaOneCenterAmbient T ≤ centralizer (K : Set G) := by
  obtain ⟨u,huT,huK⟩ := exists_natural_block_fixed_point hn hT hTK
  let : IsElementaryAbelian 2 (U K) := hn.2.1.elementary.map K.subtype
  have huΩ : (u : G) ∈ omegaOneCenterAmbient T :=
    (mem_omegaOneCenterAmbient_iff T u).mpr ⟨hUT u.property,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) u.property,huT⟩
  exact fun hc => huK (hc ⟨u.property,huΩ⟩)
/-- The actual natural marking supplies the entire C.5.13 span, without
an extra fixed-point or splitting premise. -/
theorem natural_source_omega_span {F : Type*} [Field F] (h : Setup T K F)
    {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    IsElementaryAbelian 2 V ∧ V ≤ N ∧ N ≤ normalizer (V : Set G) ∧
      U K ≤ V ∧ V ≤ T ∧ T ⊓ centralizer (V : Set G) = (K ⊔ T).pCoreIn 2 :=
  source_omega_span_of_noncentral_fixed K T X h.short hT hTK P hP hA hAX
    (h.natural_omegaCenter_not_le hn hT hTK)
/-- The image of K on the literal omega-center span is its original natural
SL₂ quotient over a field of the prescribed order. -/
theorem natural_source_block_image {F : Type*} [Field F] (h : Setup T K F)
    {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 2^n ∧
      Nonempty (((K.subgroupOf N).map (QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) E) := by
  obtain ⟨e⟩ := source_omega_block_quotient K T X h.short hT hTK P hP hA hAX
    (h.natural_omegaCenter_not_le hn hT hTK)
  obtain ⟨_,_,E,_,_,hc,_,hm⟩ := hn
  obtain ⟨f⟩ := hm.quotient_iso
  exact ⟨E,inferInstance,inferInstance,hc,⟨e.symm.trans f⟩⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
