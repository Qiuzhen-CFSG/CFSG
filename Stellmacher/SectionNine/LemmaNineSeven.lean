module

public import Stellmacher.SectionNine.NineSevenInitialModel
public import Stellmacher.SectionNine.NineSevenNeighborJoinTransport
public import Stellmacher.SectionNine.NineSevenTerminalNormalityCases
public import Stellmacher.SectionNine.NineSevenGoldschmidt

/-!
# Stellmacher (9.7): the index-two module intersection forces distance three

In the commuting critical-path context with distance greater than one, an
index-two intersection of the first and third modules forces critical length
three, an order-eight first module, and an SL₂(2) first local quotient. The
ambient version retains Hypothesis Two on H while the graph remains on G;
the original public statement follows via the existing ambient adapter.

The proved initial-model packet uses (9.5) and the backward index transport
to obtain the order-eight and SL₂(2) data. Initial-orbit (9.3) and endpoint
transport supply the remaining local data. The common commutator geometry
excludes length seven; the source neighborhood transport and the two terminal
normality cases exclude every larger length. The Goldschmidt four-path
argument excludes length five. Oddness from (7.5) leaves exactly three.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.7), printed pp.53–55 /
PDF pp.43–45. The proof uses the full source argument and preserves the
original index hypothesis and legacy wrapper.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- The ambient-retaining form of Stellmacher (9.7). -/
public theorem lemma_nine_seven_ambient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (aPlus3 : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 aPlus3)
    (hindex : QuotientCardEq
      (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ aPlus3) 2) :
    ctx.criticalPath.length = 3 ∧
      Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2 ^ 3 ∧
      QuotientIsModel
        (GAt ctx.Γ ctx.criticalPath.firstStep)
        (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two := by
  obtain ⟨hfirstCard,hfirstModel⟩ := nine_seven_initial_model ctx hb aPlus3 hpath hindex
  have hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^3 :=
    (nine_seven_endpoint_module_card ctx.toLocalContext).symm.trans hfirstCard
  have hendModel := (nine_seven_endpoint_quotient_model_iff ctx.toLocalContext).mp hfirstModel
  have hstartData := lemma_nine_three_ambient ctx hb
  have hnotFive := nine_seven_length_ne_five ctx hb aPlus3 hpath hindex hfirstCard
    hfirstModel hendCard hendModel hstartData
  have hleSeven : ctx.criticalPath.length ≤ 7 := by
    by_contra! hlarge
    have hU := nine_seven_initial_neighbor_join_le_penultimate ctx hb aPlus3 hpath hindex
      hfirstCard hfirstModel hendCard hendModel hstartData hlarge
    exact nine_seven_no_large_distance_of_neighbor_join_le_penultimate ctx hb aPlus3 hpath hindex
      hfirstCard hfirstModel hendCard hendModel hstartData hlarge hU
  have hnotSeven : ctx.criticalPath.length ≠ 7 := by
    intro hseven
    exact (nine_seven_commutator_geometry ctx hb aPlus3 hpath hindex hfirstCard
      hfirstModel hendCard hendModel hstartData (by omega)).2.2.2.2.2 hseven
  obtain ⟨half,hhalf⟩ := (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
    ctx.commutator_eq).odd_distance
  exact ⟨by omega,hfirstCard,hfirstModel⟩

/-- **Stellmacher (9.7).**  If the index in (9.6) is two, then the critical
distance is three, `|V_{a+1}|=8`, and the quotient is `SL₂(2)`. -/
public theorem lemma_nine_seven
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hb : 1 < ctx.criticalPath.length)
    (aPlus3 : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 aPlus3)
    (hindex : QuotientCardEq
      (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ aPlus3) 2) :
    ctx.criticalPath.length = 3 ∧
      Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2 ^ 3 ∧
      QuotientIsModel
        (GAt ctx.Γ ctx.criticalPath.firstStep)
        (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two := by
  exact lemma_nine_seven_ambient ctx.toAmbientContext hb aPlus3 hpath hindex

end Stellmacher.SectionNine
