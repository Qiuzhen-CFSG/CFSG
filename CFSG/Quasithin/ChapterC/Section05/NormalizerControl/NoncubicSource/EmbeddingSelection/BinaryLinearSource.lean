module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryLinear
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceComponentKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SourceCoreAction
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Equality

/-!
# The original binary linear quotient rows in C.5.13

The smaller quotient image in the noncubic block argument is quasisimple.
When the containing component image has either binary higher-linear model,
A.3.12's non-enlargement conclusion follows directly from the actual
full-Sylow overgroup geometry. Both subgroup images use the literal quotient
map by the ambient two-core. No embedding-list premise is used.

Source: Aschbacher–Smith C.5.13, printed p.163, using A.3.12(4–5).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- The original C.5.13 quotient application for PSL₄(2) and PSL₅(2). -/
theorem twoCore_images_eq_of_binary_linear_four_or_five
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple (B.map (QuotientGroup.mk' (pCore 2 G)))]
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hmodel : ClassicalGroup.IsPSL (L.map (QuotientGroup.mk' (pCore 2 G))) d 2) :
    B.map (QuotientGroup.mk' (pCore 2 G)) =
      L.map (QuotientGroup.mk' (pCore 2 G)) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  apply eq_of_binary_linear_four_or_five
    (T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G)))
    ?_ (hL.map_quotient (pCore 2 G)) (map_mono hBL) hd hmodel
  simpa only [Sylow.coe_mapSurjective] using
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB

/-- The actual C.5.13 span equals the original block in either binary
higher-linear containing-model case. Its component, Sylow and quasisimple
image inputs are all constructed from the original source data. -/
theorem source_eq_of_binary_linear_four_or_five
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : ConjugateSource.RankOne.U K ≤ T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      ClassicalGroup.IsPSL (((conjugateSpanBy K N).subgroupOf N).map
        (QuotientGroup.mk' (pCore 2 N))) d 2) :
    conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let r := QuotientGroup.mk' (pCore 2 N)
  let B := (K.subgroupOf N).map r
  let D := (L.subgroupOf N).map r
  have hL := noncubic_source_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  obtain ⟨Q, _hQ, hmem, hquasi, _hNorm, _hfaith, _hK, _n, _hn, _hm⟩ :=
    source_twoCore_sylow_action K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  let : IsQuasisimple B := hquasi
  have hBD : B ≤ D := map_mono (subgroupOf_mono N (le_conjugateSpanBy K N))
  let := pCore_isNilpotent (p := 2) (G := N)
  have hD : D.IsCComponent := hL.map_quotient (pCore 2 N)
  have he : B = D := eq_of_binary_linear_four_or_five Q hmem hD hBD hd hmodel
  exact source_eq_of_twoCore_image_eq K T X hK h3 hTK hAX hX S hS hL he

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
