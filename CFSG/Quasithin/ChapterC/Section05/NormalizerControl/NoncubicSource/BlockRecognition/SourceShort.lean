module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.ShortStructure
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceIntrinsic
/-!
# Original C.5.13 inputs produce the auxiliary short block

Both original natural and A₅ configurations give IsShort for the literal
span of K under X ∩ N(O₂(KT)). The equality case uses the initial block;
in the enlargement case the original model selection and the proved
moved-space transport supply the quotient and invariant interval. The
universal A.3.12 implication remains the explicit earlier source input.
This does not assert the separate four- or six-dimensional module recognition.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
omit [Finite G] in
private theorem not_three_of_four {K : Subgroup G}
    (hfour : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) : ¬ IsAlternatingBlock K 3 := by
  intro h3
  have hc := EmbeddingSelection.binary_card (n := 2) (by simpa using hfour)
  norm_num at hc
  obtain ⟨e⟩ := h3.2.2.quotient_iso
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hc
  norm_num at hc
theorem natural_source_short {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
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
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    IsShort (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
  have hirr := natural_source_blockModuleIrreducible hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc
  rcases natural_source_models hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc with he | ⟨_,hfour,hmodel⟩
  · rw [he]
    exact h.short
  · exact source_short_of_interval K T X (Or.inl ⟨n,hn⟩) (not_three_of_four hfour)
      hT (h.module_le.trans inf_le_left) hTK P hP hA hAX hX S hS hmodel hirr

theorem alternating_source_short {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
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
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    IsShort (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
  have hirr := alternating_source_blockModuleIrreducible hG hA312 h hTK P hP X hA hAX hX S hS hx hnc
  rcases alternating_source_models hG hA312 h hTK P hP X hA hAX hX S hS hx hnc with he | ⟨_,hfour,hmodel⟩
  · rw [he]
    exact h.block.2.1
  · exact source_short_of_interval K T X (Or.inr (Or.inr h.block)) (not_three_of_four hfour)
      h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX hX S hS hmodel hirr

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
