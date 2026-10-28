module
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionEight.EightFourEdgeFixedTransport

/-!
# The actual star family lies in the neighbor module

For the same edge-fixed family F used in Stellmacher (8.4), the join of
F(d,l) over first vertices d lies in the neighbor-center module V_l. Only
the family's containment and exact transporter formula are needed; no new
family or vertex action is chosen. The proof works in the pure local
Section Eight context, with the original canonical API preserved by a wrapper.

If d is adjacent to l, F(d,l) lies in Z_d, which is one of the subgroups
in the defining join for V_l. Otherwise the transporter formula has no terms:
any transporting actor would carry the initial edge to (d,l), contradicting
nonadjacency because the graph action preserves edges. Taking the join over
d proves the containment, including vertices outside the original orbit.

This is the Vstar_l≤V_l inclusion used in source (7) of Stellmacher (8.4),
Journal of Algebra190 (1997), printed p39, `refs/files/stellmacher-n-group.pdf`.
It supports the nearby-center centralization argument for the actual star
family without adding an extra geometric hypothesis.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
/-- The star join of the transported edge-fixed family lies in the neighbor-center join. -/
public theorem eight_four_star_le_neighbor_module_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹) :
    ∀ l, (⨆ d, F d l) ≤ VAt ctx.Γ l := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  intro l
  apply iSup_le
  intro d
  by_cases hadj : Γ.adjacent d l
  · have hn : d ∈ neighborhood Γ l :=
      (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hadj)
    have hz : z Γ d ≤ v Γ l := by
      change Γ.zAt d ≤ Γ.vAt l
      rw [Γ.vAt_def]
      exact le_sSup ⟨d,hn,rfl⟩
    exact ((hsub d l).trans inf_le_left).trans hz
  · rw [hformula]
    apply iSup_le
    intro g
    apply iSup_le
    intro hg
    have ha := adjacent_act Γ g cp.firstStep_adj
    rw [hg.1,hg.2] at ha
    exact (hadj ha).elim

/-- Canonical-context wrapper retaining the original graph and edge family. -/
public theorem eight_four_star_le_neighbor_module
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹) :
    ∀ l, (⨆ d, F d l) ≤ VAt ctx.Γ l := by
  exact eight_four_star_le_neighbor_module_local ctx.toLocalContext w F hsub hformula

end Stellmacher.SectionEight
