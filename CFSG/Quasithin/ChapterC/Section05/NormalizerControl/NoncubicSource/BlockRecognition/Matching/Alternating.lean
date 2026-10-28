module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.Matching.Exceptional
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.Matching.Quotient
/-!
# The alternating case of the original C.5.13 matching

The original Sylow and two-core setup supplies the literal quotient embedding.
Its full Sylow normalizer forces the five-letter placement, excluding the
exceptional four-space by its cubic fixed vectors. The enlarged block is
therefore the ordinary alternating-seven block. Only the earlier universal
A.3.12 source input remains, exactly as in the original unpaired producer.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.Matching
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
theorem alternating_source_matched_block {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
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
    let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
    L = K ∨ IsAlternatingBlock L 7 := by
  let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
  rcases alternating_source_a7_blocks hG hA312 h hTK P hP X hA hAX hX S hS hx hnc with he | ⟨_,hL⟩
  · exact Or.inl he
  rcases hL with hL | hL
  · exact Or.inr hL
  exfalso
  have h3 : ¬ IsAlternatingBlock K 3 := by
    intro h3
    obtain ⟨e5⟩ := h.block.2.2.quotient_iso
    obtain ⟨e3⟩ := h3.2.2.quotient_iso
    have hc := Nat.card_congr (e5.symm.trans e3).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at hc
    norm_num at hc
  obtain ⟨hKL,hk,hU,R,hR⟩ := source_matching_data K T X
    (Or.inr (Or.inr h.block)) h3 h.twoGroup (h.module_le.trans inf_le_left)
    hTK P hP hA hAX hX S hS
  obtain ⟨eL⟩ := hL.2.1
  obtain ⟨Q,hQ⟩ := exists_quotient_sylow_normalizing hKL eL R hR
  apply no_alternating_five_in_exceptional h.block hL (inclusion hKL)
    (inclusion_injective hKL) _ eL hk Q hQ
  rintro l ⟨k,hk,rfl⟩
  have hh := hU (mem_map_of_mem K.subtype hk)
  obtain ⟨l,hl,he⟩ := hh
  exact (Subtype.ext he : l = inclusion hKL k) ▸ hl
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.Matching
