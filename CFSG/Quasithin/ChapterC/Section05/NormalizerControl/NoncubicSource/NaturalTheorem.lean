module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.Matching.Natural
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalNormalizer
/-!
# The original natural case of C.5.13

The genuine normalizer calculation and the natural-plane restriction
matching give both assertions on the original auxiliary span. A proper
enlargement forces the original natural field to have order four and the
larger block to be the exceptional A₇ type. The universal earlier A.3.12
classification remains explicit.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
theorem natural_source_theorem_5_13 {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
    ((X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (U K : Set G)) ∧ (L = K ∨ IsL2EvenBlock K 2 ∧ IsExceptionalA7Block L) := by
  exact ⟨natural_source_normalizer_control hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc,
    Matching.natural_source_matched_block hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
