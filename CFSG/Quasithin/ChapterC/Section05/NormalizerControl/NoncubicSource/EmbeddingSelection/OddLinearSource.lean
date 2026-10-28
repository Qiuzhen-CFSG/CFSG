module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceComponentKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Source

/-!
# The original odd PSL₂ containing-model branch in C.5.13

The actual auxiliary conjugate span is a source-derived C-component. The
proved prime and quadratic PSL₂ embedding theorems apply to its literal
quotient image and the original full Sylow. The binary smaller-model sieve
then gives exactly the original C.5.13 alternatives, with surviving models
transported to the actual action image in N/C_N(V).

This discharges the odd PSL₂ branch directly from its marked containing
model, without the universal A.3.12 premise.
Source: Aschbacher–Smith A.3.12(8), pp.47–48, and C.5.13, pp.162–163.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exact original source alternative for every odd prime or quadratic
PSL₂ containing model, retaining the actual N/C_N(V) image. -/
theorem source_embedding_selection_of_odd_linear_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hDmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      let D := ((conjugateSpanBy K N).subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
      ∃ p r : ℕ, p.Prime ∧ Odd p ∧ (r = 1 ∨ r = 2) ∧
        ClassicalGroup.IsPSL D 2 (p ^ r)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let L := conjugateSpanBy K N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let C := DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N)
    L = K ∨ (IsL2EvenBlock K 2 ∨ IsAlternatingBlock K 5) ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
      (IsAlternating C 7 ∨ IsAlternatingCover C 7 ∨ Nonempty (C ≃* Janko1.Model) ∨
      ClassicalGroup.IsPSL C 2 25 ∨ ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL C 2 p) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let L := conjugateSpanBy K N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let r := QuotientGroup.mk' (pCore 2 N)
  let B := (K.subgroupOf N).map r
  let D := (L.subgroupOf N).map r
  have hL := noncubic_source_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  obtain ⟨Q,hQ,hmem,hquasi,hNorm,hfaith,⟨eK⟩,n,hn,hmodel⟩ :=
    source_twoCore_sylow_action K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  let : IsQuasisimple B := hquasi
  have hBD : B ≤ D := map_mono (subgroupOf_mono N (le_conjugateSpanBy K N))
  let := pCore_isNilpotent (p := 2) (G := N)
  have hD : D.IsCComponent := hL.map_quotient (pCore 2 N)
  have hrows : A312Embedding B D := by
    obtain ⟨p, r, hp, ho, hr, hm⟩ := hDmodel
    rcases hr with rfl | rfl
    · exact ChapterA.Section03.SourceEmbeddings.embedding_of_primePSL2 Q hmem hD hBD
        hp ho (by simpa only [pow_one] using hm)
    · exact ChapterA.Section03.SourceEmbeddings.embedding_of_quadraticPSL2 Q hmem hD hBD hp ho hm
  have hout := select_non_rank_two_rows Q B D hn hmodel hBD hNorm hfaith hrows
    (fun hm hr => eq_of_rankTwo_parabolic_model Q hmem hD hBD hm hr)
  rcases hout with he | ⟨hn2,hm⟩
  · exact .inl (source_eq_of_twoCore_image_eq K T X hK h3 hTK hAX hX S hS hL he)
  · obtain ⟨e⟩ := source_component_image_equiv K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
    have hkfour : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 := by
      simpa [hn2] using hmodel.of_mulEquiv eK
    exact .inr ⟨noncubic_type_of_binary_four K hK h3 hkfour, hkfour,
      surviving_models_transport e hm⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
