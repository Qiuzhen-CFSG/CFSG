module
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.SmallSupport
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.TwoCentralizerRank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Descent
/-!
# The outer A₆–C₃ branch of B.5.13

The specified normal cubic factor lies in the Fitting subgroup. Offender
generation bounds its centralizer by two-rank two. If the Fitting subgroup
moves the dual module, the B.1 minimal-plane bound applies; otherwise the
minimal offenders centralize it and have rank at most two. Either route
bounds the original quadratic ratio without a whole-module splitting.

Source: Aschbacher--Smith B.5.13, printed p.110, on the literal
`OuterSixThreeShape` supplied by the adequate B.5 classification.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceB513
open SourceInduction
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
/-- The original outer source case supplies its numerical conclusion. -/
theorem quadraticRatio_le_two_of_outerSixThree_source (ρ : Representation (ZMod 2) D V)
    {K : GroupClass} (h : FFHypothesis K ρ.dual) (c : OuterSixThreeShape D) :
    quadraticRatio ρ ≤ 2 := by
  let : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide : 1 < 360) c.card_ge)
  have hNF : c.second ≤ fittingSubgroup D := by
    let : c.second.Normal := c.second_normal
    have hp : IsPGroup 3 c.second := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_congr c.secondEquiv.toEquiv]
      simp)
    exact (le_sSup ⟨inferInstance, hp⟩ : c.second ≤ pCore 3 D).trans (pCore_le_fitting D 3)
  exact quadraticRatio_le_two_of_fitting_centralizer_rank ρ h.faithful h.twoCore
    (h.isFFModule ρ.dual) c.second hNF (c.second_centralizer_twoRank_le ρ.dual h.generated)
end CFSG.Quasithin.ChapterB.SourceB513
