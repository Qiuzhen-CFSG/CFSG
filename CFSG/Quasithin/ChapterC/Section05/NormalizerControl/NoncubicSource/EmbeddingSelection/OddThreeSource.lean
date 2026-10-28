module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.OddThree
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SourceCoreAction

/-!
# Excluding odd degree-three rows on the actual C.5.13 quotient

The source construction supplies the full Sylow subgroup acting faithfully
on the original binary block image in `N/O₂(N)`. That image is contained in
the image of the literal conjugate span. The rank/order comparison therefore
excludes every odd-prime PSL₃, PSU₃, SL₃ and SU₃ model for this containing
image. No whole-Borel containment or embedding-list input is required.

This discharges the odd degree-three containing-model rows in
Aschbacher–Smith C.5.13, printed pp.162–163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

/-- The literal source span image has neither an odd-prime projective nor
an odd-prime special degree-three model, for either linear/unitary sign. -/
theorem source_twoCore_not_odd_three
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let D := ((conjugateSpanBy K N).subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
    ¬ IsPSLSign D unitary 3 p ∧ ¬ IsSLSign D unitary 3 p := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let r := QuotientGroup.mk' (pCore 2 N)
  let B := (K.subgroupOf N).map r
  let D := ((conjugateSpanBy K N).subgroupOf N).map r
  obtain ⟨Q, _hQ, _hmem, _hquasi, hNorm, hfaith, _hK, n, hn, hm⟩ :=
    source_twoCore_sylow_action K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  have hBD : B ≤ D := map_mono (subgroupOf_mono N (le_conjugateSpanBy K N))
  exact ⟨not_odd_three_projective_containing Q B D hBD hn hm hNorm hfaith hp ho unitary,
    not_odd_three_special_containing Q B D hBD hn hm hNorm hfaith hp ho unitary⟩

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
