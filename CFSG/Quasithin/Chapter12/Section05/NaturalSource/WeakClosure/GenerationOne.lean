module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Transfers
public import CFSG.Quasithin.Chapter3.Defs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.WeakClosure.Generation

/-!
# Excluding generation one using the actual weak closures

E.3.19 at i = 0 and j = 1 expresses H as the join of its C₁-centralizer
and W₀-normalizer. The bounds from 12.5.7 and 12.5.10 put both in M,
contradicting membership in the original H-star family. The literal
relative Sylow map is identified with the supplied ambient T.

Source: Aschbacher--Smith, 12.5.11(1), printed p.821. The weak-closure
bounds and s = 3 remain inputs from their independent source arguments.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The E.3.19 deduction in 12.5.11(1) on the original H-star family. -/
theorem generation_ne_one (a : ExteriorMarking D)
    (hs : let := D.elementary; ChapterE.globalS V = 3)
    (hN : normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ a.M)
    (hC : centralizer (ChapterE.weakCentralizer V (T : Subgroup G) 1 : Set G) ≤ a.M)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) a.M) :
    ChapterE.generationParameter H ≠ 1 := by
  let := D.elementary
  have hT : ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H).map H.subtype =
      (T : Subgroup G) := map_subgroupOf_eq_of_le hH.1.1.2
  intro hn
  apply hH.1.2
  apply ChapterE.RankOneWeakClosure.le_of_parameter_eq_one (V := V) (T.subtype hH.1.1.2) hn
  · rw [hs]
    decide
  · rw [hT]
    exact hC
  · rw [hT]
    exact hN

/-- Apply the W₁ fixed-space consequence to the original H-star consumer. -/
theorem generation_ne_one_of_V₆_fixed (a : ExteriorMarking D)
    (hs : let := D.elementary; ChapterE.globalS V = 3)
    (hN : normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ a.M)
    (hG₆ : a.Gi 6 ≤ a.M)
    (hW₁ : ChapterE.indexedWeakClosure V (T : Subgroup G) 1 ≤
      centralizer (a.Vi 6 : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) a.M) :
    ChapterE.generationParameter H ≠ 1 :=
  generation_ne_one a hs hN (centralizer_weakCentralizer_one_le a hG₆ hW₁) hH

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
