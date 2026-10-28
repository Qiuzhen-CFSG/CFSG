module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.LocalFamily
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.AlternatingSevenMaximal.Source
/-!
# The original A₇-image consumer with local membership discharged

The actual auxiliary span is placed in L(X,T) by the source producer, so
its A₇-image normality no longer assumes local membership. The remaining
model is explicitly on the image in X/O₂(X). Models of L/O₂(L) or of the
auxiliary action image cannot replace it without a core-kernel comparison.
Source: Aschbacher–Smith C.5.12–13, printed pp.162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
/-- The source local-family input is proved; only the genuine A₇ model of
the literal larger-X image remains for the quotient-placement argument. -/
theorem source_larger_A7_image_normal {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      IsAlternating (((conjugateSpanBy K N).subgroupOf X).map
        (QuotientGroup.mk' (pCore 2 X))) 7) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    (((conjugateSpanBy K N).subgroupOf X).map
      (QuotientGroup.mk' (pCore 2 X))).Normal := by
  exact AlternatingSevenMaximal.source_image_normal hG hA312 K T X hAX hX S hS
    (source_larger_local_family hG hA312 K T X hK h3 hTK hAX hX S hS).1 hmodel
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
