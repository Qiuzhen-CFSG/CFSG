module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SurvivingParameters
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.BinaryLinearSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Source
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# The small finite containing models on the actual C.5.13 source

A₅, A₆ and 3.A₆ have solvable proper full-Sylow overgroups, which force
the original span to equal the block. A₈ is the literal binary PSL₄ model
and has the already proved non-enlargement property. In A₇, 3.A₇ and J₁,
the smaller binary image has field degree two. Its model and the containing
model transport to the original N/C_N(V) action image.

This covers every alternating constructor of the earlier simple and
three-cover catalogues, as well as J₁, using the source-derived setup.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
open ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- The original span equals the block in the A₅, A₆ and 3.A₆ cases. -/
theorem source_eq_of_small_alternating_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : ConjugateSource.RankOne.U K ≤ T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      let D := ((conjugateSpanBy K N).subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
      IsAlternating D 5 ∨ IsAlternating D 6 ∨ IsAlternatingCover D 6) :
    conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let r := QuotientGroup.mk' (pCore 2 N)
  let B := (K.subgroupOf N).map r
  let D := (L.subgroupOf N).map r
  have hL := noncubic_source_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  obtain ⟨Q, _hQ, hmem, _hquasi, _hNorm, _hfaith, _hK, _n, _hn, _hm⟩ :=
    source_twoCore_sylow_action K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  have hBD : B ≤ D := map_mono (subgroupOf_mono N (le_conjugateSpanBy K N))
  let := pCore_isNilpotent (p := 2) (G := N)
  have hD : D.IsCComponent := hL.map_quotient (pCore 2 N)
  have he : B = D := eq_of_small_alternating_containing_component Q hmem hD hBD hmodel
  exact source_eq_of_twoCore_image_eq K T X hK h3 hTK hAX hX S hS hL he


/-- The original selector in the three surviving finite models. -/
theorem source_embedding_selection_of_surviving_model
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      let D := ((conjugateSpanBy K N).subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
      IsAlternating D 7 ∨ IsAlternatingCover D 7 ∨ Nonempty (D ≃* Janko1.Model)) :
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
  obtain ⟨_Q, _hQ, _hmem, _hquasi, _hNorm, _hfaith, ⟨eK⟩, n, hn, hm⟩ :=
    source_twoCore_sylow_action K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  have hBD : B ≤ D := map_mono (subgroupOf_mono N (le_conjugateSpanBy K N))
  have hn2 := binary_parameter_of_surviving_containing_model B D hBD hn hm hmodel
  obtain ⟨e⟩ := source_component_image_equiv K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  have hkfour : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 := by
    simpa [hn2] using hm.of_mulEquiv eK
  apply Or.inr
  refine ⟨noncubic_type_of_binary_four K hK h3 hkfour, hkfour, surviving_models_transport e ?_⟩
  rcases hmodel with ha | ha | hj
  · exact .inl ha
  · exact .inr (.inl ha)
  · exact .inr (.inr (.inl hj))

/-- The complete small finite-model branch of the original source selector. -/
theorem source_embedding_selection_of_small_finite_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      let D := ((conjugateSpanBy K N).subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
      (∃ d, 5 ≤ d ∧ d ≤ 8 ∧ IsAlternating D d) ∨ IsAlternatingCover D 6 ∨
        IsAlternatingCover D 7 ∨ Nonempty (D ≃* Janko1.Model)) :
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
  rcases hmodel with hAlt | hCover6 | hCover7 | hJ
  · obtain ⟨d, hlo, hhi, hm⟩ := hAlt
    have hd : d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 := by omega
    rcases hd with rfl | rfl | rfl | rfl
    · exact .inl (source_eq_of_small_alternating_model hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS (.inl hm))
    · exact .inl (source_eq_of_small_alternating_model hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS (.inr (.inl hm)))
    · exact source_embedding_selection_of_surviving_model K T X hK h3 hT hUT hTK P hP hA hAX hX S hS (.inl hm)
    · apply Or.inl
      apply source_eq_of_binary_linear_four_or_five hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS (.inl rfl)
      obtain ⟨e⟩ := hm
      exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
        ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩
  · exact .inl (source_eq_of_small_alternating_model hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS (.inr (.inr hCover6)))
  · exact source_embedding_selection_of_surviving_model K T X hK h3 hT hUT hTK P hP hA hAX hX S hS (.inr (.inl hCover7))
  · exact source_embedding_selection_of_surviving_model K T X hK h3 hT hUT hTK P hP hA hAX hX S hS (.inr (.inr hJ))

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
