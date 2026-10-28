module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.Matching.Ordinary
/-!
# The natural case of the original C.5.13 matching

The original source alternatives force the smaller field parameter to be two.
The literal source kernel and full Sylow restriction exclude an ordinary
six-dimensional A₇ block, leaving exactly the exceptional A₇ block. Together
with Matching.Alternating this proves the source's “respectively” clause.
The earlier universal A.3.12 input remains exactly as in SourceModels.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.Matching
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
theorem natural_source_matched_block {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
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
    let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
    L = K ∨ IsL2EvenBlock K 2 ∧ IsExceptionalA7Block L := by
  let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
  rcases natural_source_a7_blocks hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc with he | ⟨hK,hL⟩
  · exact Or.inl he
  have hK2 : IsL2EvenBlock K 2 := by
    rcases hK with hK | hK
    · exact hK
    · obtain ⟨F0,_,_,hF0,hPSL,_⟩ := hn.2.2
      have hn2 := EmbeddingSelection.binary_parameter_of_alternating_five (by have := hn.1; omega)
        hPSL hK.2.2.quotient_iso
      simpa only [hn2] using hn
  rcases hL with hL | hL
  · exfalso
    have h3 : ¬ IsAlternatingBlock K 3 := by
      intro h3
      obtain ⟨F0,_,_,hF0,hPSL,_⟩ := hK2.2.2
      have hc := EmbeddingSelection.binary_card hPSL
      obtain ⟨e3⟩ := h3.2.2.quotient_iso
      rw [Nat.card_congr e3.toEquiv,nat_card_alternatingGroup] at hc
      norm_num at hc
    obtain ⟨hKL,hk,hU,R,hR⟩ := source_matching_data K T X
      (Or.inl ⟨2,hK2⟩) h3 hT (h.module_le.trans inf_le_left)
      hTK P hP hA hAX hX S hS
    have hU' : (blockU K).map (inclusion hKL) ≤ blockU L := by
      rintro l ⟨k,hk,rfl⟩
      obtain ⟨l,hl,he⟩ := hU (mem_map_of_mem K.subtype hk)
      exact (Subtype.ext he : l = inclusion hKL k) ▸ hl
    exact no_natural_two_in_alternating_seven hK2 hL (inclusion hKL)
      (inclusion_injective hKL) hU' hk R (by simpa only [inclusion_range] using hR)
  · exact Or.inr ⟨hK2,hL⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.Matching
