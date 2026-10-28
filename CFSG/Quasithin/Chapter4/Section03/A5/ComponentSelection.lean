module
public import CFSG.Quasithin.Chapter4.Section03.A5.SourceModule
public import CFSG.Quasithin.Chapter4.Section03.A5.Reciprocal
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ComponentEscape
/-!
# The exact A₅ source splits into component and reciprocal branches

Starting from failure of uniqueness over L, the original block-layer
identity makes the C.2.8 module exactly V. The completed C.2.11 component
selection either gives an escaping actual C-component normalized by L,
with its genuine quasisimple quotient and ordinary/constrained alternatives,
or retains the reciprocal core and preimage escape supplied by A.4.4.
The original maximal counterexample J, its core and its muStar membership
remain in the output; neither branch is assumed away.

Source: Aschbacher–Smith 4.2.5–12 and the start of 4.3.2, pp.609–613,
using C.2.11–13, p.148.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open Chapter4 ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The actual failure of uniqueness supplies precisely the two remaining source branches. -/
theorem source_component_or_reciprocal
    (hV : (ChapterC.blockU L).map L.subtype = V)
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    ∃ J H : Subgroup G,
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L L) ∧
      L ≤ J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ H ⊓ normalizer (L : Set G) < H ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        L (J.pCoreIn 2) V ∧
      ((H.pCoreIn 2 = (H ⊓ normalizer (L : Set G)).pCoreIn 2 ∧
          characteristicNormalizerIn (normalizer (L : Set G)) (H.pCoreIn 2) ≤
            H ⊓ normalizer (L : Set G) ∧
          ¬ twoGeneralizedFittingPreimage (normalizer (L : Set G)) ≤ H) ∨
        ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
          ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
          L ≤ normalizer (K.map H.subtype : Set G) ∧
          (IsComponent H K ∨ generalizedFitting K = pCore 2 K)) := by
  obtain ⟨J,H,hJ,hLJ,hH,hJH,hout,hlt,hC⟩ := d.source_C28_module_of_blockU hV hnot
  refine ⟨J,H,hJ,hLJ,hH,hJH,hout,hlt,hC,?_⟩
  rcases hC.component_source_alternative with hp | ⟨K,hK,hq,he,hn,ht⟩
  · apply Or.inl
    apply d.source_reciprocal_core_data hH hout
    rintro x ⟨y,hy,rfl⟩
    exact (hp hy).2
  · apply Or.inr
    have hspan : conjugateSpanBy L (H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy L _)
    rw [hspan] at hn
    exact ⟨K,hK,hq,he,hn,ht⟩
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
