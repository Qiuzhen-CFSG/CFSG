module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SmallFiniteSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.OddLinearSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwoSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.ClassicalCoverSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SporadicSource

/-!
# The complete original auxiliary selector of C.5.13

The block and its actual auxiliary conjugate span supply their literal
images in N/O₂(N), the full Sylow, and its faithful action on the smaller
binary image. The known-simple source theorem constructs the containing
component and its complete simple or triple-cover catalogue. The proved
model branches exhaust that catalogue, including Held and J₄. Surviving
models are transported to the actual action image in N/C_N(V).

Every premise is part of the original C.5.13 setup. No universal A.3.12,
model-list conclusion or additional parabolic-placement input remains.
The later full-span quotient in X has a different action and is separate.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The complete source selector on the original auxiliary quotient, over
the full known-simple catalogue and with all setup premises discharged. -/
theorem source_embedding_selection_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
  have hcatalogue :=
    (source_twoCore_component_models_knownSimple hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS).2
  have hexclusions := source_twoCore_sporadic_exclusions K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  rcases hcatalogue with ⟨_hsimple, hmodels⟩ | ⟨_hcenter, hmodels⟩
  · cases hmodels with
    | alternating d hd hm =>
        exact source_embedding_selection_of_small_finite_model hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
          (.inl ⟨d, hd.1, hd.2, hm⟩)
    | linear_odd p e hp ho he _hsimple hm =>
        exact source_embedding_selection_of_odd_linear_model hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
          ⟨p, e, hp, ho, he, hm⟩
    | three_odd p hp ho unitary hm =>
        exact ((source_twoCore_not_odd_three K T X hK h3 hT hUT hTK P hP hA hAX hX S hS hp ho unitary).1 hm).elim
    | rank_one hm =>
        exact .inl (source_eq_of_bender_or_even_su3 hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS (.inl hm))
    | rank_two hm =>
        exact .inl (source_eq_of_rank_two_containing_model hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS hm)
    | binary_linear d hd hm =>
        exact .inl (source_eq_of_binary_linear_four_or_five hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS hd hm)
    | sporadic name hne hm => exact (hexclusions.1 name hne hm).elim
    | janko_one hm =>
        exact source_embedding_selection_of_small_finite_model hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
          (.inr (.inr (.inr hm)))
  · cases hmodels with
    | classical unitary q hq hm =>
        exact .inl (source_eq_of_classical_three_cover hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS unitary q hq hm)
    | alternating_six hm =>
        exact source_embedding_selection_of_small_finite_model hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
          (.inr (.inl hm))
    | alternating_seven hm =>
        exact source_embedding_selection_of_small_finite_model hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
          (.inr (.inr (.inl hm)))
    | mathieu hm => exact (hexclusions.2 hm).elim

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
