module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceComponentKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SourceCoreAction
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Equality

/-!
# The actual Bender and even-unitary covering rows in C.5.13

The original noncubic source data construct the containing conjugate-span
component and the full Sylow action on its binary smaller image. The
rank-one Sylow-overgroup theorems identify the two images for each Bender
model and for the actual even SU₃ covers. Equality then lifts through the
original auxiliary two-core to equality of the original subgroups.

These are branches of the complete containing-model catalogue, without
an A.3.12 embedding-list assumption.
Source: Aschbacher–Smith C.5.13, pp.162–163, and A.3.12, pp.47–48.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- Literal quotient non-enlargement for all Bender models and the
special-unitary covering models over even fields. -/
theorem twoCore_images_eq_of_bender_or_even_su3
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hmodel : ClassificationModels.IsBenderModel (L.map (QuotientGroup.mk' (pCore 2 G))) ∨
      ∃ n, 0 < n ∧ Chapter1.Section02.LocalModels.IsSU
        (L.map (QuotientGroup.mk' (pCore 2 G))) 3 (2 ^ n)) :
    B.map (QuotientGroup.mk' (pCore 2 G)) =
      L.map (QuotientGroup.mk' (pCore 2 G)) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hb : B.map (QuotientGroup.mk' (pCore 2 G)) ∈ ChapterA.Section03.localCComponents S := by
    simpa only [S, Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB
  rcases hmodel with hm | ⟨n, hn, hm⟩
  · exact eq_of_bender_containing_component S hb (hL.map_quotient _) (map_mono hBL) hm
  · exact eq_of_binary_su3_containing_component S hb (hL.map_quotient _) (map_mono hBL) hn hm

/-- The actual original C.5.13 span equals K in every rank-one containing
model, with both the simple and even special-unitary covering rows retained. -/
theorem source_eq_of_bender_or_even_su3
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
      ClassificationModels.IsBenderModel D ∨
        ∃ n, 0 < n ∧ Chapter1.Section02.LocalModels.IsSU D 3 (2 ^ n)) :
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
  have he : B = D := by
    rcases hmodel with hm | ⟨n, hn, hm⟩
    · exact eq_of_bender_containing_component Q hmem hD hBD hm
    · exact eq_of_binary_su3_containing_component Q hmem hD hBD hn hm
  exact source_eq_of_twoCore_image_eq K T X hK h3 hTK hAX hX S hS hL he

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
