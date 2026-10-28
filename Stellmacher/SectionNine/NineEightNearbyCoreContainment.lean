module
public import Stellmacher.SectionNine.NineEightReorientation
public import Stellmacher.SectionNine.NineEightNeighborhood

/-!
# Transporting (9.8) to a nearby center contained in an abelian module

Assuming the ambient (9.8) bound, let a center be contained in an abelian
V-module at distance less than the critical length. Then that module lies
in the center vertex's core. Otherwise one of its generating neighboring
centers escapes the core. Critical minimality makes that neighbor and the
center vertex an actual critical pair, with the module vertex as prescribed
first step. Both centers commute inside the abelian module, so the proved
prescribed-edge transport applies the ambient bound and gives a contradiction.

The bound remains an explicit premise. This handles the second use of (9.8)
in (9.9), printed p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`, without
assuming an unproved shifted-context or first-edge identity.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_eight_nearby_core_of_center_containment
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (bound : ∀ shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B,
      ZAt shifted.Γ shifted.criticalPath.a' ≤
        VAt shifted.Γ shifted.criticalPath.firstStep → shifted.criticalPath.length ≤ 3)
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (moduleVertex centerVertex : ctx.Γ.Vertex)
    (hdistance : ctx.Γ.distance moduleVertex centerVertex < ctx.criticalPath.length)
    (habelian : IsMulCommutative (VAt ctx.Γ moduleVertex))
    (hcontain : ZAt ctx.Γ centerVertex ≤ VAt ctx.Γ moduleVertex) :
    VAt ctx.Γ moduleVertex ≤ QAt ctx.Γ centerVertex := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hab : VAt Γ moduleVertex ≤ Subgroup.centralizer (VAt Γ moduleVertex : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr habelian
  change v Γ moduleVertex ≤ q Γ centerVertex
  rw [v, Γ.vAt_def]
  apply sSup_le
  rintro center ⟨neighbor, hneighbor, rfl⟩
  by_contra hnot
  have hadj : Γ.adjacent neighbor moduleVertex :=
    Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)
  have hupper := nine_eight_adjacent_distance_le Γ hadj (target := centerVertex)
  have hlower : cp.length ≤ Γ.distance neighbor centerVertex := by
    by_contra hlt
    exact hnot (critical_minimality Γ cp (by omega))
  have hdistance' : Γ.distance neighbor centerVertex = cp.length := by
    change Γ.distance moduleVertex centerVertex < cp.length at hdistance
    omega
  have hcritical : IsCriticalPair Γ neighbor centerVertex := by
    refine ⟨?_, hnot⟩
    rw [hdistance', ← cp.endpoint_distance]
    exact cp.critical.1
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ moduleVertex := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hcomm : ⁅ZAt Γ neighbor, ZAt Γ centerVertex⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hneighborV.trans (hab.trans (Subgroup.centralizer_le hcontain)))
  have hpath : Γ.distance neighbor centerVertex = Γ.distance moduleVertex centerVertex + 1 := by
    change Γ.distance moduleVertex centerVertex < cp.length at hdistance
    omega
  have hbound := nine_eight_critical_pair_of_ambient_bound bound ctx
    neighbor centerVertex moduleVertex hcritical hadj hpath hcomm hcontain
  omega

end Stellmacher.SectionNine
