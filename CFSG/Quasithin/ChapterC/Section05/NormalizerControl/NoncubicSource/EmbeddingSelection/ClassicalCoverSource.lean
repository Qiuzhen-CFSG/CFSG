module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.SpecialLinear
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.BenderSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.OddThreeSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceModelsKnownSimple

/-!
# The classical three-cover branch on the original C.5.13 quotient

The source-derived containing component is quasisimple. For an even SL₃
model this permits lifting the PSL₃ proper-Sylow Fitting bound through
its actual center. The even SU₃ model already has rank-one solvable
Sylow-overgroup geometry. Odd prime linear and unitary models contradict
the actual faithful Sylow action on the binary smaller image.

These arguments exhaust the classical constructor of the full three-cover
catalogue, with the literal auxiliary quotient maps and original span.
Source: Aschbacher–Smith A.3.6(2) and C.5.13, printed pp.44–45,162–163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original source span equals the initial block when its containing
image is an even SL₃. The source-derived model theorem supplies the
quasisimplicity required for lifting through the actual center. -/
theorem source_eq_of_even_special_linear_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : ConjugateSource.RankOne.U K ≤ T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {n : ℕ} (hn : 0 < n)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      IsSL (((conjugateSpanBy K N).subgroupOf N).map
        (QuotientGroup.mk' (pCore 2 N))) 3 (2 ^ n)) :
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
  let : IsQuasisimple D :=
    (source_twoCore_component_models_knownSimple hG K T X hK h3 hT hUT hTK P hP hA hAX hX S hS).1
  have he : B = D := eq_of_binary_special_linear_three_model Q hmem hD hBD hn hmodel
  exact source_eq_of_twoCore_image_eq K T X hK h3 hTK hAX hX S hS hL he


/-- Every classical constructor in the actual three-cover catalogue
has source span equal to the original block. Even linear covers lift the
projective geometry; even unitary covers use the rank-one geometry; odd
prime models contradict the original faithful full-Sylow action. -/
theorem source_eq_of_classical_three_cover
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : ConjugateSource.RankOne.U K ≤ T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (unitary : Bool) (q : ℕ) (hq : CoverParameter unitary q)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      IsSLSign (((conjugateSpanBy K N).subgroupOf N).map
        (QuotientGroup.mk' (pCore 2 N))) unitary 3 q) :
    conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K := by
  rcases hq with ⟨n, hn, rfl, _⟩ | ⟨hp, ho⟩
  · cases unitary with
    | false =>
        exact source_eq_of_even_special_linear_three hG K T X hK h3 hT hUT hTK
          P hP hA hAX hX S hS (by omega) hmodel
    | true =>
        exact source_eq_of_bender_or_even_su3 hG K T X hK h3 hT hUT hTK
          P hP hA hAX hX S hS (.inr ⟨n, by omega, hmodel⟩)
  · exact ((source_twoCore_not_odd_three K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
      hp ho unitary).2 hmodel).elim

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
