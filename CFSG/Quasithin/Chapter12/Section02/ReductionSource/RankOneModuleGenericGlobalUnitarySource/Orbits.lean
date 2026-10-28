module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Orbits
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource

/-!
# The two inner unitary involution classes for the original chosen module

The actual whole-reduced Chapter12 module supplies all original hypotheses.
The source producer constructs both native parabolic orbits, transports them
through the compatible ordinary or degree-two comparison, and separates them
in the ambient group. Every involution in the reduced common Sylow belongs
to one of those two classes. This retains both orientations and does not
identify the reduced common Sylow with the original ambient T.

Source: Aschbacher–Smith F.4.35 and 5.3.3, printed pp.292,659 of
`refs/quasithin.pdf`. Outer transfer and the subsequent centralizer and
order comparisons remain further source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The reduced common Sylow has exactly two ambient involution classes,
with representatives in the original O₂(L). -/
theorem rankOne_unitary_inner_two_classes
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm) :
    ∃ z ∈ L.pCoreIn 2, ∃ t ∈ L.pCoreIn 2,
      orderOf z = 2 ∧ orderOf t = 2 ∧ ¬ IsConj z t ∧
        ∀ x ∈ (T : Subgroup G) ⊓ L, orderOf x = 2 → IsConj x z ∨ IsConj x t := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_inner_two_classes hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
