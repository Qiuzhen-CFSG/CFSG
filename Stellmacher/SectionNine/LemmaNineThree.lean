module
public import Stellmacher.SectionNine.NineThreeFinalContradiction
public import Stellmacher.SectionNine.NineThreeAssembly
public import Stellmacher.SectionNine.NineThreeSourceNativeThompsonAction

/-!
# Stellmacher (9.3): classification along the initial vertex orbit

When the commuting critical pair has distance greater than one, every
vertex conjugate to the initial vertex has center of order four and
stabilizer modulo its two-core is SL₂(2). The ambient implementation retains
Hypothesis Two in H and the graph on its embedded group G; the legacy
statement is recovered through the unchanged ambient-context adapter.

An initial center larger than four supplies the two prescribed-actor
extractions and their simultaneous normalization. The proved mixed-commutator
argument forces native Thompson action, giving the canonical order-sixteen
rank-two configuration. Its actual mixed centralizer has a faithful core
Frattini action. The core-intersection bound and (1.7) then force the first
extracted residual into the odd-core layer, contradicting its geometric
exclusion. The existing lower bound therefore makes the center order exactly
four; (9.2) identifies the core quotient and conjugation transports both
conclusions along the vertex orbit.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.3), printed pp.48–50
of `refs/files/stellmacher-n-group.pdf`. Only the proved prescribed-actor and
supplied-edge-Sylow portions of (7.8) are used; the unresolved uniform
same-subgroup clause and the unrestricted (1.6) are not dependencies.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven
universe u

/-- The ambient-retaining form of Stellmacher (9.3). -/
public theorem lemma_nine_three_ambient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) :
    ∀ l : ctx.Γ.Vertex,
      IsConjugateVertex ctx.Γ ctx.criticalPath.a l →
      QuotientIsModel (GAt ctx.Γ l) (QAt ctx.Γ l) SL2Two ∧
        Nat.card (ZAt ctx.Γ l) = 4 := by
  apply nine_three_ambient_of_center_card_le_four ctx
  by_contra hnot
  have hlarge := Nat.lt_of_not_ge hnot
  obtain ⟨first⟩ := nine_three_first_configuration ctx hb hlarge
  obtain ⟨second⟩ := nine_three_second_configuration ctx hb first
  obtain ⟨config⟩ := nine_three_normalized_geometry ctx hb hlarge first second
  have hnative := nine_three_source_native_thompson_action ctx hb hlarge first second config
  have rank := nine_three_native_action_rank_data ctx hb hlarge first second config hnative
  exact nine_three_large_center_false ctx hb hlarge first second config rank

/-- **Stellmacher (9.3).** Initial-orbit vertices have SL₂(2) quotient and center of order four. -/
public theorem lemma_nine_three
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hb : 1 < ctx.criticalPath.length) :
    ∀ l : ctx.Γ.Vertex,
      IsConjugateVertex ctx.Γ ctx.criticalPath.a l →
      QuotientIsModel (GAt ctx.Γ l) (QAt ctx.Γ l) SL2Two ∧
        Nat.card (ZAt ctx.Γ l) = 4 := by
  exact lemma_nine_three_ambient ctx.toAmbientContext hb

end Stellmacher.SectionNine
