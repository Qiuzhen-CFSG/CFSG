module
public import CFSG.Quasithin.Chapter12.Section09.SourceAt.Localized.Implementation
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt

/-!
# The original natural branch from the earlier sources at the same G,T

The invariant flag, escaping conjugator, abelian point span, fusion and terminal
commutator contradiction are all constructed on the original source. The
natural marking already present in HigherRankHypothesis is retained. No
natural reduction on other chosen modules or ambient groups is required.

Source: Aschbacher--Smith 12.9.1--9, printed pp.857--864, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.SourceAt
open Section02 Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The actual marked higher-rank source is impossible in degrees four and five.
The earlier source implications concern only the original ambient group and Sylow. -/
theorem natural_branch_contradiction_from_source
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (previous : Theorem12213At KnownSimple.IsKnownSimple T) : False := by
  obtain ⟨_,F,_,_,_,_,g,hgP,hgH⟩ := h.exists_flag_geometry_at structural
  have hab := point_span_abelian_from_source modules h hn preferred structural previous
    F g hgP hgH
  exact abelian_contradiction_from_source h hn structural previous F hab

end CFSG.Quasithin.Chapter12.Section09.SourceAt
