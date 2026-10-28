module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.InnerAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Linear
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.RankOneOuter
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Unitary

/-!
# Inner action in the S₃ branch of 15.3.43

`Local` preserves the genuine component, Sylow, theta, normalizer and invariant
subgroup inputs. It places every constructed invariant characteristic-two
Borel together with its diagonal actor in M ∩ I, where clause (a) bounds its
three-rank by one.

Alternative (i) gives inner action by commuting distinct components.
In alternative (ii), `RankOneOuter` proves that the actual outer group is
abelian, including for central two-covers. The S₃ shadow and theta generation
then kill the outer action.

In alternative (iii), `Linear` constructs the invariant Borel and uses the
index-three assertion to put the diagonal actor in L, contradicting its
outer action on the actual quotient. `Unitary` constructs the invariant
Borel and uses the earlier plane action to force fixed-field degree two,
contradicting the signed congruence. These give direct contradictions in
place of the printed three-rank argument; no assertion that a PSL₃(4)
Borel alone has three-rank greater than one is used.

The assembly below excludes all diagonal alternatives and proves literal
inner action on L, both as containment in L C_G(L) with normalization and
as elementwise implementation by elements of L. The inputs are the earlier
local and plane facts and the authorized alternatives; their construction
belongs to the earlier source assembly. No rank-two assumption on Y₊,
nontrivial intersection residual, or component containment is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the paragraph
between 15.3.43(d) and (e), printed p.1139; compare 15.3.37 on p.1135.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion

variable {G : Type*} [Group G] [Finite G]

/-- The two signed diagonal families and the central-two-cover PSL₃(4)
case are all excluded by the genuine earlier local and plane inputs. -/
theorem LocalSetup.not_diagonal_alternative (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (hp : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂) :
    ¬ Candidates.DiagonalAlternative15343 d.Yplus L (localSpan L d.S) := by
  rintro ⟨horbit, y, hy, hy3, hlinear | hunitary | hfour⟩
  · exact h.linear_diagonal_impossible horbit hy hy3 (Or.inl hlinear)
  · obtain ⟨n, hn, hmod, hmodel, hact⟩ := hunitary
    exact h.not_unitary_diagonal d hp horbit hy hy3 hn hmod hmodel hact
  · exact h.not_linear_diagonal_four horbit hy hy3 hfour

/-- The alternatives reduce to source cases (i) and (ii), retaining every
model, rank, theta and component-orbit clause of those alternatives. -/
theorem LocalSetup.contained_or_rankOne_of_alternatives
    (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (hp : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S)) :
    (d.Yplus ≤ theta I ∧ theta I = localSpan L d.S) ∨
      (L = localSpan L d.S ∧ primeRank 3 L = 1 ∧ Candidates.RankOneQuotientModel L) := by
  rcases halt with hcontained | hrank | hdiagonal
  · exact Or.inl hcontained
  · exact Or.inr hrank
  · exact (h.not_diagonal_alternative d hp hdiagonal).elim

/-- The inner-action conclusion between 15.3.43(d) and (e), on the actual
component rather than only its quotient. The alternatives are the explicit
output of the preceding source reduction, not an inner-action premise. -/
theorem LocalSetup.inner_of_alternatives (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (hp : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S)) :
    d.Yplus ≤ L ⊔ centralizer (L : Set G) ∧ d.Yplus ≤ normalizer (L : Set G) := by
  rcases h.contained_or_rankOne_of_alternatives d hp halt with
    hcontained | ⟨horbit, hrank, hmodel⟩
  · exact inner_of_contained_alternative h hcontained
  · have hi := h.inner_of_rankOneQuotientModel horbit hrank hmodel
    exact ⟨hi, normalizes_of_le_inner hi⟩

/-- Every element of Y₊ acts on L by conjugation by an element of L.
This is literal inner action, including for a nontrivial central two-cover. -/
theorem LocalSetup.implements_inner_of_alternatives (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (hp : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S)) :
    ∀ y ∈ d.Yplus, ∃ l ∈ L, ∀ x ∈ L, y * x * y⁻¹ = l * x * l⁻¹ :=
  (le_inner_iff_implemented d.Yplus L).mp (h.inner_of_alternatives d hp halt).1

end CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
