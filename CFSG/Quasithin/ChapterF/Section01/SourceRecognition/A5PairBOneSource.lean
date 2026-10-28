module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Linear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Symplectic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.IntrinsicBOne.Recognition

/-!
# Original A5-pair core control in the intrinsic b=1 source branch

The intrinsic DGS noncommuting b=1 source constructs a literal reduced
linear or symplectic amalgam from the critical pair.  Applying the native
linear/symplectic A5 calculations to that actual comparison gives the two
original join-core equalities and both one-Borel containments.  The theorem
keeps the original F.1.1 pair and its whole odd Borel; it does not assume a
`ReducedAlternatives` witness or a global A5-pair contract.

The b=2 branch and the universal source construction remain separate source
obligations.  This file therefore records a genuine branch result rather than
claiming the full F.1.12 implication.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source
open A5PairCatalogue
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.IntrinsicBOne

variable {G : Type*} [Group G] [Finite G]
  {K R S : Subgroup G}

/-- The actual intrinsic noncommuting b=1 source branch proves both original
join-core equalities and both containments from the unchanged A5/A5 pair
hypotheses.  The reduced comparison is constructed internally from the
critical source pair; no reduced-catalogue premise is supplied by the caller.
-/
theorem a5_pair_core_and_containment_of_critical_bOne
    (h : HypothesisF11 ![K,R] S)
    (a : ∀ i, Nonempty ((![K,R] i ⧸ pCore 2 (![K,R] i)) ≃*
      alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (![K,R] j) S ≤ normalizer (S : Set G))
    {v w : Vertex (reducedFamily ![K,R] S)}
    (hc : IsCriticalPair (reducedFamily ![K,R] S) v w)
    (hne : ⁅Z (reducedFamily ![K,R] S) v,
      Z (reducedFamily ![K,R] S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily ![K,R] S) = 1) :
    (∀ i, twoCore (![K,R] i ⊔ S) = twoCore (![K,R] i)) ∧
      (∀ i, S ≤ ![K,R] i) := by
  obtain ⟨F, _, _, _, m, hm, hF, ha⟩ :=
    IntrinsicBOne.small_comparison_of_critical_bOne h hc hne hb
  rcases ha with ⟨point, e⟩ | ⟨point, e⟩
  · exact A5PairCatalogue.linear_core_and_containment h a hnorm F hF hm point e.some
  · exact A5PairCatalogue.Symplectic.core_and_containment F h a hnorm hF hm point e.some

end CFSG.Quasithin.ChapterF.Source
