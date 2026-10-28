module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceEmbedding
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.EmbeddingNormality
/-!
# The noncubic embedding with source orbit normality discharged

The actual SQTK component-orbit theorem supplies relative normality, and
therefore the containing component is the original span L=⟨K^{X₁}⟩.
The source QTKE assumptions supply the two-core quotient's SQTK hypotheses.
Only the genuine earlier A.3.12 embedding classification remains explicit;
no separate A.3.8 or normality premise is used.
Source: Aschbacher–Smith C.5.13, printed p.162.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
/-- The actual conjugate-span embedding with orbit normality discharged. -/
theorem noncubic_auxiliary_embedding_of_A312 {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = T)
    (hQ : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      IsSQTK 𝒦 (N ⧸ pCore 2 N)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    (L.subgroupOf N).IsCComponent ∧
      A312Embedding ((K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))
        ((L.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  obtain ⟨hlocal,_hN,⟨S,hS⟩⟩ := noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX P hP
  have hKN : K ≤ N := hlocal.1
  have hTN : T ≤ N := hS ▸ map_subtype_le _
  have hTs : T.subgroupOf N = (S : Subgroup N) := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hTN,hS]
  have hb : K.subgroupOf N ∈ Chapter1.L N (S : Subgroup N) := by
    rw [← hTs]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTN hKN).mp hlocal
  obtain ⟨D,hD,hKD,_hu,hemb,hn⟩ := lemma_1_2_4_of_A_3_12 hA312 hQ S hb
  let : D.Normal := hn (by
    rw [← subgroupOf_normalizer_eq hKN]
    intro s hs
    exact hTK (hS ▸ mem_map_of_mem N.subtype hs))
  have hspan := normal_span_eq_component (K.subgroupOf N) D hD hKD (Chapter1.mem_L_not_isSolvable hb)
  have hm : (conjugateSpanBy (K.subgroupOf N) ⊤).map N.subtype = conjugateSpanBy K N := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hKN,← MonoidHom.range_eq_map,range_subtype]
  have he : (conjugateSpanBy K N).subgroupOf N = D := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hKN),← hm,hspan]
  change ((conjugateSpanBy K N).subgroupOf N).IsCComponent ∧ _
  rw [he]
  exact ⟨hD,hemb⟩

/-- Original QTKE data supplies the local hypotheses for the source embedding. -/
theorem noncubic_source_embedding_of_A312 {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    (L.subgroupOf N).IsCComponent ∧
      A312Embedding ((K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))
        ((L.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hlocal := (noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX P hP).1
  have hcore : A.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A) ((pCoreIn_le 2 A).trans hAN) inf_le_right
  have hNH : N ∈ Chapter1.H G := by
    intro he
    exact hlocal.2.2.2 (bot_unique (hcore.trans he.le))
  exact noncubic_auxiliary_embedding_of_A312 hA312 K T X hK h3 hTK hAX hX P hP
    (uniqueness_local_quotient_sqtk hG hNH)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
