module

public import Stellmacher.MainType.NineOne
public import Stellmacher.SectionNine.LemmaNineOne
public import Stellmacher.SectionEleven.SylowTerminalEdgePair
public import Stellmacher.SectionEleven.SL2EdgeIntersection

/-!
# The distance-one local type in the actual Sylow terminal context

The commuting critical pair at distance one supplies every conclusion of
Stellmacher (9.1), including its full ambient normalizer witness. The SL2
quotient at the endpoint makes the adjacent intersection a two-group.
The proved edge-pair theorem identifies the mapped intersection as an ambient
Sylow with the same order as the supplied Sylow and transports the trivial
join two-core. At distance one the endpoint is the first step, so this is
the exact pair in the source definition. Its order128 transfers directly
from the original ambient (9.1) conclusion.

This realizes the source-local Ω6+(2) configuration without a hypothesis
that all ambient two-locals are solvable and without a model-recognition
assumption. Source: Stellmacher (9.1), its definition on printed p.48,
and the Theorem 1 assembly in Section 11.
-/

namespace Stellmacher.SectionEleven

open Later SectionsFiveToSeven SectionNine

universe u

public theorem multiple_nine_one_type
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥)
    (hlength : ctx.criticalPath.length = 1) :
    IsOfOmegaSixPlusTwoType H := by
  obtain ⟨hfirst, hsecond, hcard, hcore, hVstar, hwitness⟩ :=
    lemma_nine_one_ambient (ctx.toSectionNineContext hcomm) hlength
  have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hlength
  have hadj : ctx.Γ.adjacent ctx.criticalPath.a ctx.criticalPath.a' := by
    rw [hend]
    exact ctx.criticalPath.firstStep_adj
  have hedge : IsPGroup 2
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.a' :
        Subgroup (P1 ⊔ P2 : Subgroup H)) := by
    change QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2Two at hsecond
    rw [inf_comm]
    exact edge_intersection_isPGroup_of_SL2
      ctx.sectionSeven ctx.Γ (ctx.Γ.adjacent_symm hadj) hsecond
  obtain ⟨R, hmapintersection, hmapcore, hRcard⟩ :=
    sylow_terminal_edge_pair ctx hadj hedge
  exact ⟨{
    K := (P1 ⊔ P2 : Subgroup H)
    embedding := (P1 ⊔ P2).subtype
    embedding_injective := Subtype.val_injective
    sylowIntersection := R
    S := (S0 : Subgroup H).subgroupOf (P1 ⊔ P2)
    P1 := P1.subgroupOf (P1 ⊔ P2)
    P2 := P2.subgroupOf (P1 ⊔ P2)
    Γ := ctx.Γ
    criticalPath := ctx.criticalPath
    intersection_eq := hmapintersection
    join_twoCore_eq_bot := hmapcore
    Vstar := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    caseData := {
      critical_length := hlength
      definition := rfl
      local_quotients := ⟨hfirst, hsecond⟩
      card_S := hRcard.trans hcard
      initial_core := hcore
      vstar_structure := hVstar
      normalizer_witness := hwitness } }⟩

end Stellmacher.SectionEleven
