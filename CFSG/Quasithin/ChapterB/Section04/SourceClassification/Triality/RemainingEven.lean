module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.ExceptionalRemainder
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Triality.OddSource
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.ReeF4.Source

/-!
# The sole remaining source family in B.4.2

The complete sporadic and Ree exclusions, and the original odd-exponent
triality exclusion, leave only even-exponent triality on the actual component
quotient. All other original source actions have their proved classification
row. The even proper-extension displacement has its independent producer.
Source: Aschbacher--Smith B.4.2 and Guralnick--Malle II, Section 8.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem case_or_even_triality
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (hm : ChapterA.Section02.IsTheoremCModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨
      ∃ n : ℕ, 0<n ∧ Even n ∧ Triality.Standard.IsTrialityGroupAt (2^n) (L ⧸ center L) := by
  rcases case_or_remaining_exceptional h hff hm with hc | hm
  · exact Or.inl hc
  · cases hm with
    | ree m hm he => exact (reeF4_excluded h hff hm (Classical.choice he)).elim
    | triality n hn hm =>
      rcases Nat.even_or_odd n with he | ho
      · exact Or.inr ⟨n,hn,he,hm⟩
      · exact (triality_odd_not_ff h n hn ho hm hff).elim

end CFSG.Quasithin.ChapterB.SourceClassification
