module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FixedFreeImage
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NormalImage
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FullSpan
/-!
# The enlarged noncubic branch of the original C.5.12 theorem

The proved C.5.13 alternatives make every proper auxiliary enlargement
an ordinary or exceptional A₇ block. Its fixed layer vanishes, giving the
exact two-core kernel in the original quotient X/C_X(V). A.3.12 then
makes its image normal, and the existing normal-image argument proves
the literal full Sylow-normalizer bound. Thus the remaining noncubic
C.5.12 case has auxiliary span equal to the original block.
Source: Aschbacher–Smith C.5.12–13, printed pp.162–163.
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

theorem natural_source_control_or_auxiliary_eq {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
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
    conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K ∨
      X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let V := conjugateSpanBy (U K) X
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans (le_sup_left.trans hAX))
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  let : IsElementaryAbelian 2 (U K) := h.short.elementary.map K.subtype
  let : IsMulCommutative V := (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
  let : IsElementaryAbelian 2 V := conjugateSpanBy_elementary_of_commutative (U K) X
  rcases natural_source_a7_blocks hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc with he | ht
  · exact Or.inl he
  · have hnormal := noncubic_a7_source_image_normal hG hA312 K T X (Or.inl ⟨n,hn⟩)
      (natural_not_three hn) hT (h.module_le.trans inf_le_left) hTK P hP hA hAX hX S hS hVC ht.2
    exact Or.inr (noncubic_control_of_normal_span_image K T X V (Or.inl ⟨n,hn⟩)
      (natural_not_three hn) hT hTK P hP hAX hVX hXV (le_conjugateSpanBy _ _) hnormal
      (natural_source_normalizer_control hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc))

theorem alternating_source_control_or_auxiliary_eq {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
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
    conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K ∨
      X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let V := conjugateSpanBy (U K) X
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans (le_sup_left.trans hAX))
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  let : IsElementaryAbelian 2 (U K) := h.block.2.1.elementary.map K.subtype
  let : IsMulCommutative V := (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
  let : IsElementaryAbelian 2 V := conjugateSpanBy_elementary_of_commutative (U K) X
  rcases alternating_source_a7_blocks hG hA312 h hTK P hP X hA hAX hX S hS hx hnc with he | ht
  · exact Or.inl he
  · have hnormal := noncubic_a7_source_image_normal hG hA312 K T X (Or.inr (Or.inr h.block))
      (alternating_not_three h.block) h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX hX S hS hVC ht.2
    exact Or.inr (noncubic_control_of_normal_span_image K T X V (Or.inr (Or.inr h.block))
      (alternating_not_three h.block) h.twoGroup hTK P hP hAX hVX hXV (le_conjugateSpanBy _ _) hnormal
      (alternating_source_normalizer_control hG hA312 h hTK P hP X hA hAX hX S hS hx hnc))

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
