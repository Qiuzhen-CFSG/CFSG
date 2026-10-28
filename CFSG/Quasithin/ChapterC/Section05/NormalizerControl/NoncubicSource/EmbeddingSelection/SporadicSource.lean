module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Sporadic
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SourceCoreAction

/-!
# The complete sporadic exclusion on the original C.5.13 quotient

The existing source theorem constructs the full Sylow subgroup acting
faithfully on the binary block image in the actual auxiliary two-core
quotient. The block image lies in the literal conjugate-span image, so the
proved order sieve excludes all ten Theorem C sporadic containing groups
and the M₂₂ triple cover there. All quotient maps are the source maps.

This supplies the corresponding complete rows of Aschbacher–Smith C.5.13,
printed pp.162–163; it assumes no embedding-list or local model theorem.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ClassificationModels Chapter1.Section02.LocalModels ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

/-- Every sporadic name admitted by Theorem C, and the M₂₂ triple cover,
is excluded for the image of the original auxiliary conjugate span. -/
theorem source_twoCore_sporadic_exclusions
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let D := ((conjugateSpanBy K N).subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
    (∀ name : SporadicName, name ≠ .j3 → ¬ Nonempty (D ≃* name.Carrier)) ∧
      ¬ IsM22Cover D := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let r := QuotientGroup.mk' (pCore 2 N)
  let B := (K.subgroupOf N).map r
  let D := ((conjugateSpanBy K N).subgroupOf N).map r
  obtain ⟨Q, _hQ, _hmem, _hquasi, hNorm, hfaith, _hK, n, hn, hm⟩ :=
    source_twoCore_sylow_action K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  have hBD : B ≤ D := map_mono (subgroupOf_mono N (le_conjugateSpanBy K N))
  exact ⟨fun name hne => not_sporadic_containing Q B D hBD hn hm hNorm hfaith name hne,
    not_mathieu_twentyTwo_cover_containing Q B D hBD hn hm hNorm hfaith⟩

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
