module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.OddRankOne
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.OddLinearFF
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.G2Binary
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.SourceApplication

/-!
# The complete odd-characteristic family of B.4.2

Odd PSL₂ quotients reduce to their actual alternating and binary SL₃
coincidences, with all other parameters excluded on the original action.
Odd PSL₃ has no FF-module. The odd unitary calculation forces PSU₃(3),
whose marked central quotient is the actual derived G₂(2) group; the proved
binary G₂ source theorem supplies its full marked ambient action and offenders.

Thus all three constructors of the literal odd Theorem C family are resolved
without additional classification or parameter premises.
Source: Aschbacher–Smith B.4.2 and K.2, printed pp.86 and 453.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem odd_unitary_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU (L ⧸ center L) 3 p) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨e⟩ := ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.source_g2Derived_of_cubicRatio_le_two
    ρ L ⟨h.sqtk,h.fitting.symm,h.quasisimple,h.faithful,h.irreducible⟩ hp ho hm h.smallCubic
  exact g2_binary_case h hff e

theorem odd_case (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (hm : ChapterA.Section02.IsTheoremCOddModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  cases hm with
  | linear_two p e hp ho he hm => exact odd_pslTwo_theoremC_case h hff hp ho he hm
  | linear_three p hp ho hm => exact (not_ff_odd_psl3 h hp ho hm hff).elim
  | unitary_three p hp ho hm => exact odd_unitary_case h hff hp ho hm

theorem odd_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : ChapterA.Section02.IsTheoremCOddModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  odd_case (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA) ⟨A,hA.isOffender ρ⟩ hm
end CFSG.Quasithin.ChapterB.SourceClassification
