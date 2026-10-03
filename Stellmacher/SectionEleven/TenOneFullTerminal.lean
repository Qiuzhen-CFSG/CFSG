module
public import Stellmacher.MainType.TenOne
public import Stellmacher.SectionEleven.MultipleTenOneRealization
public import Stellmacher.SectionEleven.SL2EdgeIntersection
public import Stellmacher.SectionEleven.SylowTerminalEdgePair
public import Stellmacher.SectionTen.AmbientTenOne

/-!
# Both Section Ten terminal local types

A commuting Sylow terminal context of critical length three gives either the
source-local M12 configuration or the source-local twisted F4(2)' configuration.
All Section Ten calculations retain the actual graph on the generated join,
and the type witnesses retain an ambient Sylow and its actual local pair.
No solvability assumption on every ambient two-local is imposed.

Apply the complete ambient (10.1) at the actual offset-two vertex. Its large
alternative already has the established exceptional-type realization. In the
small alternative, the SL2(2) local quotient makes the shifted edge a two-group;
edge conjugacy identifies its image as a conjugate of the supplied ambient
Sylow. The actual edge generates the graph group, so its mapped join has
trivial two-core. The order bound transfers to that ambient Sylow, and every
common equation and small-case structural field is retained, including the
full nonsolvable ambient involution centralizer.

Source: Stellmacher (10.1), its type definitions on printed p.65, and the
Theorem 1 assembly in Section Eleven, Journal of Algebra190 (1997).
-/

namespace Stellmacher.SectionEleven
open Later SectionsFiveToSeven SectionNine
universe u

public theorem multiple_ten_one_full_terminal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥)
    (hlength : ctx.criticalPath.length = 3) :
    IsOfMathieuTwelveType H ∨ IsOfTwistedF4TwoDerivedType H := by
  let tenCtx := ctx.toSectionTenContext hcomm hlength
  let middle := ctx.criticalPath.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ middle)
  let Wnext := GeneratedNeighborhoodV ctx.Γ middle
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext
  have hc := SectionTen.ambient_lemma_ten_one tenCtx middle W W0 Wnext hpath rfl rfl rfl
  cases hc.alternative with
  | a horders hquot hmiddle hfirst hobstruction =>
    have hadj := ten_one_offset_adjacent_firstStep ctx.Γ ctx.criticalPath hlength middle hpath
    have htwo := edge_intersection_isPGroup_of_SL2 ctx.sectionSeven ctx.Γ hadj hquot.2
    obtain ⟨sylow, hintersection, hcore, hSylow⟩ := sylow_terminal_edge_pair ctx hadj htwo
    have hcard : Nat.card ((S0 : Subgroup H).subgroupOf (P1 ⊔ P2)) = Nat.card S0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctx.sylow_le_join).toEquiv
    refine Or.inl ⟨{
      toEmbeddedLocalTypeGraph := {
        K := (P1 ⊔ P2 : Subgroup H)
        embedding := (P1 ⊔ P2).subtype
        embedding_injective := (P1 ⊔ P2).subtype_injective
        sylowIntersection := sylow
        S := (S0 : Subgroup H).subgroupOf (P1 ⊔ P2)
        P1 := P1.subgroupOf (P1 ⊔ P2)
        P2 := P2.subgroupOf (P1 ⊔ P2)
        Γ := ctx.Γ
        criticalPath := ctx.criticalPath }
      aPlus2 := middle
      intersection_eq := hintersection
      join_twoCore_eq_bot := hcore
      W := W
      W0 := W0
      Wnext := Wnext
      caseA := {
        critical_length := hlength
        path_offset := hpath
        definitions := hc.definitions
        derived_intersection := hc.derived_intersection
        index_conclusions := hc.index_conclusions
        card_S := ?_
        local_quotients := hquot
        middle_structure := hmiddle
        first_step_structure := hfirst
        nonsolvable_centralizer := hobstruction } }⟩
    simpa only [hcard, hSylow] using horders
  | b horders hquot hfirst hindices =>
    apply Or.inr
    apply multiple_ten_one_of_case_b ctx middle W W0 Wnext
    exact {
      critical_length := hlength
      path_offset := hpath
      definitions := hc.definitions
      derived_intersection := hc.derived_intersection
      index_conclusions := hc.index_conclusions
      card_S := horders
      local_quotients := hquot
      first_step_structure := hfirst
      remaining_indices := hindices }

end Stellmacher.SectionEleven
