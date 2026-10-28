module

public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedPositiveStar
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.GuardedCounterexample

/-!
# The original positive starred family in the F.9 setup

F.9.1 supplies the actual standing outside-local witness at every maximal
normalizer. The guarded 3.2.13 and 13.1.5 arguments therefore apply to the
original Sylow subgroup: each positive starred radical centralizes its
reduced module, and the whole family has one common maximal normalizer.
Only the genuine guarded 3.1.8 implication remains an earlier source input.
No starred membership is inferred merely from maximality of a normalizer.

Source: Aschbacher--Smith 13.1.5, p.868, applied in 13.7.4, pp.936--938.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion Chapter1 Section01
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The original positive starred radical centralizes its actual reduced
subgroup, with the standing condition discharged by the F.9 source pair. -/
theorem source_positive_star_centralizes_reduced
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    {X : Subgroup G} (hX : X ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T) :
    X ≤ centralizer ((reducedTwoSubgroup
      (X ⊔ (T : Subgroup G) : Subgroup G)).map
        (X ⊔ (T : Subgroup G)).subtype : Set G) :=
  GuardedPositiveStar.positive_star_centralizes_reduced d.counterexample.qtke h318 T
    (fun N hN hTN => h.hasMaximalOutside N hN hTN) hX

/-- All original positive starred radicals share the maximal local uniquely
containing the centralizer of the original Sylow omega-center. -/
theorem source_positive_star_common_normalizer
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hne : (Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T).Nonempty) :
    ∃ N : Subgroup G, IsMaximalTwoLocal N ∧
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ N ∧
      (∀ N' : Subgroup G, IsMaximalTwoLocal N' →
        centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ N' → N' = N) ∧
      ∀ X ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T,
        X ≤ N ∧ normalizer (X : Set G) = N :=
  GuardedPositiveStar.positive_star_common_normalizer d.counterexample.qtke h318 T
    (fun N hN hTN => h.hasMaximalOutside N hN hTN) hne

end CFSG.Quasithin.Chapter13.Section07.PlusAction
