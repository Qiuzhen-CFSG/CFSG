module
public import Stellmacher.SectionTen.TenOneSmallResidualQuotientCard
public import Stellmacher.SectionNine.NineInitialEdgeCoreProduct

/-!
# The lower Sylow bound in the small case of (10.1)

The actual distinguished graph Sylow subgroup has at least sixty-four
elements when the first module has order eight and its local quotient
is SL2(2).

The first residual core has order thirty-two and lies in the first core.
The cubic first quotient makes the adjacent edge twice as large as that
core. The initial adjacent-core product, together with the distinguished
Sylow containments, identifies this entire edge with the supplied Sylow T.
Thus the bound is on the original graph Sylow, not a replacement subgroup.

Source: Stellmacher (10.1)(a), printed pp.59–61, the lower bound in
2^6≤|S|≤2^7, `refs/files/stellmacher-n-group.pdf`. The upper bound is the
separate middle residual/odd-centralizer calculation.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_sylow_card_lower
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    64 ≤ Nat.card T := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Q := QAt Γ cp.firstStep
  let R := twoCoreIn (EAt Γ cp.firstStep)
  have hRcard : Nat.card R = 32 := ten_one_small_residual_core_card ctx middle hpath hsmall hmodel
  have hRQ : R ≤ Q := by
    change twoCoreIn (Γ.twoResidualAt cp.firstStep) ≤ Γ.twoCoreAt cp.firstStep
    rw [Γ.twoResidualAt_def, Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hQcard : 32 ≤ Nat.card Q := hRcard ▸ Subgroup.card_le_of_le hRQ
  have hb : 1 < cp.length := by have := ctx.critical_length; change 1 < ctx.criticalPath.length; omega
  have hjoin := (nine_initial_edge_core_product ctx.toAmbientSectionNineContext hb).1
  have hcores := local_cores_le_edge_sylow ctx.sectionSeven Γ cp
  have hTedge : T = GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    le_antisymm cp.S_le_edge_stabilizers (hjoin ▸ sup_le hcores.1 hcores.2)
  have hcard : Nat.card T = 2 * Nat.card Q := by
    rw [hTedge, inf_comm]
    exact (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.firstStep hmodel).edge_card
      cp.a (Γ.adjacent_symm cp.firstStep_adj)
  rw [hcard]
  omega
end Stellmacher.SectionTen
