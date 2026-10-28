module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.Remaining
public import Theory.Representation.Mathieu.M24SmallFF

/-!
# The original M24 source action has no FF offenders

The source central-cover theorem and innerness of M24 automorphisms identify
the whole original actor with M24. Its original vector space carries a faithful
irreducible FF action of degree at most twenty-four. The native point-induction
and Golay-filtration theorem excludes precisely this action. No recognition,
small-degree, or local-action assumption is added to the source hypotheses.

Source: Aschbacher--Smith B.4.2 and K.4, printed pp.86 and 457--459.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Subgroup Representation Representation.BinaryOffender
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The last sporadic source branch has no additional representation premise. -/
theorem not_ff_m24 (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier)) :
    ¬ IsFFModule ρ := by
  apply not_ff_m24_of_native_small ?_ h he
  intro σ hf hi hd
  let := hi
  exact Representation.Mathieu.M24SmallFF.not_isFFModule σ hf hd
end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
