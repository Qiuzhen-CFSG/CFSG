module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.QuotientAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.PrimeReduction

/-!+# Intermediate five-primary factors on the actual quotient

These contracts connect the D.2.17 factor construction to the final local
geometry in 13.8.13. The factors are subgroups of the supplied P, and their
supports are their actual moved subgroups on U_H/V₁ through H/O₂(H).
Thus neither the actors nor their four-dimensional summands can be replaced
by unrelated group or module labels.

`Factorization` and `RankOneFactors` do not assert existence. In particular,
the rank-one conclusion is a construction target, not an additional premise
of the requested five-primary exclusion. Its owner must eliminate the
rank-two alternative using F.9.16(2) before constructing `RankOneFactors`.
The geometric calculation may proceed independently with that result as
an explicit intermediate input; final assembly must construct it.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the two paragraphs beginning “We have reduced” and
“Therefore”. Cardinalities 16 and 4 express binary dimensions four and two.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Subgroup
variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

/-- One or two actual cyclic-five factors and their disjoint moved spaces. -/
structure Factorization (a : StarAction H UH V₁) (P : Subgroup G) where
  count : ℕ
  count_pos : 0 < count
  count_le_two : count ≤ 2
  factor : Fin count → Subgroup G
  factor_le : ∀ i, factor i ≤ P
  factor_card : ∀ i, Nat.card (factor i) = 5
  star_card : ∀ i, Nat.card (Source.starImage H (factor i)) = 5
  generated : P = ⨆ i, factor i
  commute : ∀ i j, i ≠ j → ⁅factor i, factor j⁆ = ⊥
  disjoint : ∀ i j, i ≠ j → Disjoint (factor i) (factor j)
  support_card : ∀ i, Nat.card
    (commutatorAction (a.actors (factor i)) (UH ⧸ V₁.subgroupOf UH)) = 16
  support_disjoint : ∀ i j, i ≠ j →
    Disjoint (commutatorAction (a.actors (factor i)) (UH ⧸ V₁.subgroupOf UH))
      (commutatorAction (a.actors (factor j)) (UH ⧸ V₁.subgroupOf UH))

namespace Factorization

/-- The ith summand is defined by its action, not supplied as a free space. -/
def support {a : StarAction H UH V₁} {P : Subgroup G}
    (f : Factorization a P) (i : Fin f.count) : Subgroup (UH ⧸ V₁.subgroupOf UH) :=
  commutatorAction (a.actors (f.factor i)) (UH ⧸ V₁.subgroupOf UH)

end Factorization

/-- The factor calculation after exclusion of the rank-two alternative.
Factor zero is moved, and the other factor, when present, is centralized. -/
structure RankOneFactors (a : StarAction H UH V₁) (P Uγ : Subgroup G) where
  factors : Factorization a P
  actor_card : Nat.card (Source.starImage H Uγ) = 2
  first_moved : ⁅Source.starImage H Uγ,
    Source.starImage H (factors.factor ⟨0, factors.count_pos⟩)⁆ ≠ ⊥
  remaining_fixed : ∀ i : Fin factors.count, i.val ≠ 0 →
    ⁅Source.starImage H Uγ, Source.starImage H (factors.factor i)⁆ = ⊥
  moved_card : Nat.card (commutatorAction (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)) = 4

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
