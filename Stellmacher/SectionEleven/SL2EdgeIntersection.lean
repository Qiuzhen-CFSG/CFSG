module

public import Stellmacher.SectionNine.CubicLocalAction

/-!
# The intersection at an SL₂(2) edge is a two-group

In an actual Section Seven coset graph, if one vertex stabilizer modulo its
two-core is SL₂(2), then its intersection with every adjacent stabilizer is a
two-group. This supplies the Sylow-intersection input for the source-local
realizations of (9.1) and the first alternative of (10.1).

The proved cubic local action gives edge order twice the order of the selected
vertex's two-core. That core is the injective ambient image of a two-core, so
its order is a power of two; the edge therefore has power-of-two order. The
cubic action theorem already proves edge properness from actual edge generation,
nontrivial local cores and trivial global two-core. No quotient condition on
the opposite vertex, critical-path assumption, or ambient Hypothesis 2 is used.

Source: Stellmacher, Section 7's edge data and the cubic local-action
calculation preceding (9.3), as proved in
`Stellmacher.SectionNine.CubicLocalAction`; the result is used in Section 11's
source-local type realizations.
-/

namespace Stellmacher.SectionEleven

open Later SectionsFiveToSeven CosetGraphContext

universe u v

/-- An SL₂(2) local quotient forces every genuine incident edge intersection
to be a two-group. -/
public theorem edge_intersection_isPGroup_of_SL2
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext.{u,v} G S P1 P2)
    {a b : Γ.Vertex} (hab : Γ.adjacent a b)
    (hmodel : QuotientIsModel (GAt Γ a) (QAt Γ a) SL2Two) :
    IsPGroup 2 (GAt Γ a ⊓ GAt Γ b : Subgroup G) := by
  have hedge :=
    (SectionNine.cubic_local_action_of_sl2Two_quotient Γ h7 a hmodel).edge_card b hab
  have hcore : IsPGroup 2 (QAt Γ a) := by
    change IsPGroup 2 (Γ.twoCoreAt a)
    rw [Γ.twoCoreAt_def]
    exact pCore_isPGroup.map _
  obtain ⟨power, hpower⟩ := hcore.exists_card_eq
  apply IsPGroup.of_card (n := power + 1)
  rw [hedge, hpower, pow_succ, mul_comm]

end Stellmacher.SectionEleven
