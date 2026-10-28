module

public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimaryRadical
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.GuardedRatio
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.PositiveRadical

/-!
# The original higher primary radical obstruction in the plus setup

For a maximal nonquasisimple local component I, use the actual
J=O^{p′}(O∞(I)) included in G. Its quotient is the original odd prime
core and it is two-perfect, characteristic in I, and contains Ξ_p(I).
The previously constructed canonical starred radical supplies the genuine
uniqueness hypothesis. The original F.9 pair supplies the standing guard.
Thus any original reduced module for JT with the exact source Sylow
centralizer contradicts the higher homocyclic case: A.1.30 gives p>5,
while guarded 3.1.8 and D.2.13 give p=3 or5.

This intermediate implication retains the reduced module and its Sylow
centralizer explicitly. The companion `SolvableRadical` consumer discharges
both through the full primary-action and intrinsic-module constructions. No prime bound, radical shape, core quotient, normality,
starred membership or two-perfectness is assumed for J.
Source: Aschbacher--Smith 3.2.14, p.585, used in 13.1.4(5), p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion Section01 Chapter1 Chapter1.Section02
open Chapter1.RadicalExclusions.ModelReduction Chapter3.RadicalCentralization
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_higher_primary_radical_obstruction
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ (S : Sylow 2 A) (B : Subgroup A),
        B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    {I : Subgroup G} (hI : I ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient I)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient I)))
    (hexp : ¬ ∀ x : primaryRadical p I ⧸ pCore 2 (primaryRadical p I), x ^ p = 1)
    (W : Subgroup (primaryRadical p I ⊔ (T : Subgroup G) : Subgroup G))
    (hW : IsPReduced 2 W)
    (hc : (T : Subgroup G).subgroupOf (primaryRadical p I ⊔ (T : Subgroup G)) ⊓
      centralizer (W : Set (primaryRadical p I ⊔ (T : Subgroup G) : Subgroup G)) =
        pCore 2 (primaryRadical p I ⊔ (T : Subgroup G) : Subgroup G)) : False := by
  have hstar := (GuardedPositiveStar.maximal_radical_positive_star
    d.counterexample.qtke T hA312 source hI hn ho hd).2
  obtain ⟨hq,he,hm⟩ := RadicalConjugateRigidity.maximal_radical_structure
    d.counterexample.qtke T hI hn ho hd
  have hXI := XiP_le_primaryRadical I hq
  have hIM : primaryRadical p I ≤ normalizer (XiP p I : Set G) := by
    rw [he]
    exact (map_subtype_le _).trans I.le_normalizer
  have hnorm : normalizer (XiP p I : Set G) ≤ normalizer (primaryRadical p I : Set G) := by
    rw [he]
    exact normalizer_le_normalizer_primaryRadical I p
  have hout := h.hasMaximalOutside _ (he.symm ▸ hm) hstar.1.invariant
  have hp := (primaryRadical_higher_structure d.counterexample.qtke T hI.1 hn ho hexp).1
  have hsmall := prime_restriction_of_guarded_star d.counterexample.qtke T h318
    hstar hXI hIM hnorm (primaryRadical_twoPerfect I ho) hout ho
    (primaryRadical_quotient_isPGroup d.counterexample.qtke T hI.1 ho) W hW hc
  rcases hsmall with he | he <;> omega

end CFSG.Quasithin.Chapter13.Section07.PlusAction
