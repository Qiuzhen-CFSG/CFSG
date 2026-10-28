module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.TwistedRankTwo
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.Linear
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.Exceptional
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceComponentKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SourceCoreAction
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Equality

/-!
# The complete rank-two containing-model branch in C.5.13

The actual smaller image in the auxiliary two-core quotient is quasisimple,
and the conjugate-span image is a source-derived C-component. The six
untwisted or small-derived cases use their proved full-Sylow overgroup
geometry. Triality and Ree contradict the original faithful full-Sylow
action on the binary smaller image by their intrinsic ranks and orders.

This exhausts all eight constructors of the earlier rank-two catalogue,
using the literal quotient images and then recovering equality in the
original ambient group. No universal A.3.12 or whole-Borel input remains.
Source: Aschbacher–Smith C.5.13, printed pp.162–163, and A.3.12(2).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ChapterA.Section03.SourceEmbeddings Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Every rank-two containing model from the full earlier Theorem C list
makes the original C.5.13 span equal the initial block. All setup, local
component and faithful Sylow inputs come from the original source data. -/
theorem source_eq_of_rank_two_containing_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : ConjugateSource.RankOne.U K ≤ T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      RankTwoTheoremC (((conjugateSpanBy K N).subgroupOf N).map
        (QuotientGroup.mk' (pCore 2 N)))) :
    conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let r := QuotientGroup.mk' (pCore 2 N)
  let B := (K.subgroupOf N).map r
  let D := (L.subgroupOf N).map r
  have hL := noncubic_source_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  obtain ⟨Q, _hQ, hmem, hquasi, hNorm, hfaith, _hK, n, hn, hm⟩ :=
    source_twoCore_sylow_action K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  let : IsQuasisimple B := hquasi
  have hBD : B ≤ D := map_mono (subgroupOf_mono N (le_conjugateSpanBy K N))
  let := pCore_isNilpotent (p := 2) (G := N)
  have hD : D.IsCComponent := hL.map_quotient (pCore 2 N)
  have he : B = D := by
    cases hmodel with
    | linear f hf hfmodel => exact eq_of_binary_linear_three_model Q hmem hD hBD hf hfmodel
    | symplectic f hf hfmodel => exact eq_of_binary_symplectic_model Q hmem hD hBD hf hfmodel
    | g2 f hf hfmodel => exact eq_of_binary_g2_model Q hmem hD hBD hfmodel
    | triality f hf hfmodel =>
        exact (not_triality_containing Q B D (by omega) (by omega) hm hBD hNorm hfaith hfmodel).elim
    | ree f hf hfmodel =>
        exact (not_ree_containing Q B D (by omega) hf hm hBD hNorm hfaith hfmodel).elim
    | symplectic_derived hfmodel => exact eq_of_binary_symplectic_derived_model Q hmem hD hBD hfmodel
    | g2_derived hfmodel => exact eq_of_binary_g2_derived_model Q hmem hD hBD hfmodel
    | tits hfmodel => exact eq_of_tits_model Q hmem hD hBD hfmodel
  exact source_eq_of_twoCore_image_eq K T X hK h3 hTK hAX hX S hS hL he

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
