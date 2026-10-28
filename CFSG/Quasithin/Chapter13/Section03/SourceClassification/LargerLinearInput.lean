module

public import CFSG.Quasithin.Chapter12.Section09.SourceInputs
public import CFSG.Quasithin.Chapter13.Section01.SourceHypotheses

/-!
# The actual larger-linear input to the Chapter 13 classification

Hypothesis 13.1.1 discharges the ambient exclusions needed in 12.9.
The original chosen V is retained. The conditional assembly excludes the
five-dimensional row first, then applies that exclusion as the preferred
choice in the four-dimensional natural branch. The two module reductions
12.5.1 and 12.6.34 and the local/fusion input remain explicit obligations.
This adapter does not prove the unconditional source theorem.

Source: Aschbacher--Smith, 12.9.1 and 13.1.2(3), printed pp.857 and866.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section09 Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {I V : Subgroup G} {n : ℕ}

/-- Apply the natural reduction to the unchanged maximal faithful member.
The PSL₆ obstruction is discharged by quasithinness in the source setup. -/
theorem largerLinear_higherRank_of_natural
    (h : Hypothesis1311 T) (hi : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (D : ChosenModule T I V) (hn : n = 4 ∨ n = 5)
    (hq : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) n 2)
    (hnatural : NaturalModule D n) :
    Nonempty (HigherRankHypothesis KnownSimple.IsKnownSimple T I V n) :=
  higherRank_of_natural hi D hn hq hnatural
    (h.no_linear 5 (Or.inr rfl)) h.no_A9 h.no_M24

/-- The exact larger-linear consumer contract, conditional on the two
module reductions and the remaining natural-branch source construction.
The latter is applied first in dimension five; its exclusion then supplies
the preferred-choice hypothesis in dimension four. -/
theorem largerLinear_excluded_of_source_inputs
    (h : Hypothesis1311 T)
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (five : NaturalReduction KnownSimple.IsKnownSimple.{u} 5)
    (natural : NaturalBranchInput KnownSimple.IsKnownSimple.{u})
    (hi : Hypothesis1223 KnownSimple.IsKnownSimple T I) (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL (I ⧸ pCore 2 I) n 2 := by
  have exclude_five : ∀ J : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 5 2 := by
    intro J hj hq
    obtain ⟨⟨W, ⟨D⟩⟩⟩ := (earlier.structural G T J hj).2.1
    obtain ⟨hs⟩ := largerLinear_higherRank_of_natural h hj D (Or.inr rfl) hq
      (five G T J W hj D hq)
    exact natural_branch_contradiction natural earlier four hs (Or.inr rfl)
      (by intro he; omega)
  rcases hn with rfl | rfl
  · intro hq
    obtain ⟨⟨W, ⟨D⟩⟩⟩ := (earlier.structural G T I hi).2.1
    obtain ⟨hs⟩ := largerLinear_higherRank_of_natural h hi D (Or.inl rfl) hq
      (four G T I W hi D hq)
    exact natural_branch_contradiction natural earlier four hs (Or.inl rfl)
      (fun _ => exclude_five)
  · exact exclude_five I hi

end CFSG.Quasithin.Chapter13.Section03.SourceClassification
