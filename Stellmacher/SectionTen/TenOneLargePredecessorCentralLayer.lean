module
public import Stellmacher.SectionTen.TenOneLargePredecessorFirstCentralizer
public import Stellmacher.SectionTen.TenOneLargeCommonModuleCentralizerAction

/-!
# The predecessor intersection has central residual action

Retain the actual Section Ten predecessor packet: adjacency to the initial
vertex, distinctness from firstStep, and both endpoint center-core escapes.
The intersection C2 of Q_previous with the terminal module centralizer in
Q_terminal has [C2,O₂(E_terminal)]≤Z_terminal. No commutator conclusion,
predecessor containment, or final core-index bound is assumed.

The predecessor first-centralizer theorem uses actual two-arc transport and
the two distinct reflection images to show that C2 centralizes V_first.
It already centralizes V_terminal by definition. The common-module centralizer
pairing theorem then gives the claimed central action on the residual core.
Both results keep the same ambient context and no-transvection hypothesis.

Source: Stellmacher (10.1), Journal of Algebra190 (1997), printed p.65,
the final C₂ commutator step. The complete predecessor packet is retained
for the following containment and index argument; this commutator proof uses
the reverse center escape through the first-centralizer theorem.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_predecessor_central_layer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (previous:ctx.Γ.Vertex) (hadj:ctx.Γ.adjacent ctx.criticalPath.a previous)
    (hne:previous≠ctx.criticalPath.firstStep)
    (_hforward:¬ZAt ctx.Γ ctx.criticalPath.a'≤QAt ctx.Γ previous)
    (hreverse:¬ZAt ctx.Γ previous≤QAt ctx.Γ ctx.criticalPath.a') :
    ⁅((QAt ctx.Γ ctx.criticalPath.a'⊓centralizer (VAt ctx.Γ ctx.criticalPath.a':Set G))⊓QAt ctx.Γ previous),
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆≤ZAt ctx.Γ ctx.criticalPath.a':=by
  exact ten_one_large_common_module_centralizer_action ctx middle hpath hno _ inf_le_left
    (ten_one_large_predecessor_centralizes_first ctx middle hpath hno previous hadj hne hreverse)
end Stellmacher.SectionTen
