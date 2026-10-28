module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Rows
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SourceCoreAction
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Equality
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SurvivingTransport
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingOrbit

/-!
# The actual A.3.12 row selection in C.5.13

The original source yields a full faithful Sylow action on the binary
block image in N/O₂(N). The complete twenty-two-row sieve, including the
independent rank-two parabolic adapters, either identifies the two images
or forces degree two and the five exceptional containing models. Equal
images lift to L=K; surviving models cross the canonical map to N/C_N(V)
by its proved injectivity on L. No ambient quotient identification,
module irreducibility or chosen classification record is assumed.

The only earlier classification input is the genuine universal A.3.12
implication; the original QTKE and C.5.9–11 data supply all its local inputs.
Source: Aschbacher–Smith C.5.13, printed pp.162–163; A.3.12, pp.47–48.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The exceptional branch forces the original natural block parameter to
be two; the A₅ alternative is retained literally. -/
theorem noncubic_type_of_binary_four (K : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    IsL2EvenBlock K 2 ∨ IsAlternatingBlock K 5 := by
  rcases hK with ⟨n,hn⟩ | ha | ha
  · have hsmall : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) := by
      obtain ⟨_,_,_,_,_,_,h,_⟩ := hn
      exact h
    have hd := binary_two_valuation (by have := hn.1; omega : 0<n) hsmall
    have hf := binary_two_valuation (by decide : 0<2) (show ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^2) from by simpa using hm)
    have he : n=2 := hd.symm.trans hf
    exact .inl (he ▸ hn)
  · exact (h3 ha).elim
  · exact .inr ha

theorem source_embedding_selection {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
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
  obtain ⟨hL,hrows⟩ := noncubic_source_embedding_of_A312 hG hA312 K T X hK h3 hTK hAX hX S hS
  obtain ⟨Q,hQ,hmem,hquasi,hNorm,hfaith,⟨eK⟩,n,hn,hmodel⟩ :=
    source_twoCore_sylow_action K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  let : IsQuasisimple B := hquasi
  have hBD : B ≤ D := map_mono (subgroupOf_mono N (le_conjugateSpanBy K N))
  let := pCore_isNilpotent (p := 2) (G := N)
  have hD : D.IsCComponent := hL.map_quotient (pCore 2 N)
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
