module

public import Stellmacher.SectionNine.NineEightReorientation
public import Stellmacher.SectionNine.NineEightNeighborhood
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs

/-!
# The reversed (9.8) application in Stellmacher (9.9)

Assuming the normalized ambient (9.8) bound, terminal V lies in first-step Q
under the (9.9) containment hypothesis and critical length greater than three.
If a terminal neighbor center escaped that core, minimality and the reversed
tail distance would make it a critical partner of the first step. The two
centers commute inside elementary abelian terminal V. Prescribed-neighbor
normalization then applies (9.8) without swapping a normalized CriticalPath.

The bound is an explicit premise, not a proof of the unfinished (9.8).
Source: printed p.56 / PDF p.46, opening of (9.9), in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_nine_terminal_core_of_eight_bound
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (bound : ∀ shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B,
      ZAt shifted.Γ shifted.criticalPath.a' ≤
        VAt shifted.Γ shifted.criticalPath.firstStep → shifted.criticalPath.length ≤ 3)
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      VAt ctx.Γ ctx.criticalPath.a') :
    VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlong : 1 < cp.length := by change 3 < cp.length at hb; omega
  have htail : Γ.distance cp.firstStep cp.a' ≤ cp.length - 1 := by
    have hpath := path_distance_le Γ cp 1 cp.length (by omega) le_rfl
    simpa only [cp.path_first, cp.path_end] using hpath
  have hstart := nine_eight_adjacent_distance_le Γ cp.firstStep_adj
    (target := cp.a')
  rw [cp.endpoint_distance] at hstart
  have htailEq : Γ.distance cp.a' cp.firstStep + 1 = cp.length := by
    rw [Γ.distance_symm]
    omega
  let _ : IsElementaryAbelian 2 (VAt Γ cp.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hlong).2.2.1
  have hab : VAt Γ cp.a' ≤ Subgroup.centralizer (VAt Γ cp.a' : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  change v Γ cp.a' ≤ q Γ cp.firstStep
  rw [v, Γ.vAt_def]
  apply sSup_le
  rintro center ⟨neighbor, hneighbor, rfl⟩
  by_contra hnot
  have hadj : Γ.adjacent neighbor cp.a' :=
    Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)
  have hupper := nine_eight_adjacent_distance_le Γ hadj (target := cp.firstStep)
  have hlower : cp.length ≤ Γ.distance neighbor cp.firstStep := by
    by_contra hlt
    exact hnot (critical_minimality Γ cp (by omega))
  have hdistance : Γ.distance neighbor cp.firstStep = cp.length := by omega
  have hcritical : IsCriticalPair Γ neighbor cp.firstStep := by
    refine ⟨?_, hnot⟩
    rw [hdistance, ← cp.endpoint_distance]
    exact cp.critical.1
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hcomm : ⁅ZAt Γ neighbor, ZAt Γ cp.firstStep⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hneighborV.trans (hab.trans (Subgroup.centralizer_le hcontain)))
  have hbound := nine_eight_critical_pair_of_ambient_bound bound ctx
    neighbor cp.firstStep cp.a' hcritical hadj
    (hdistance.trans htailEq.symm) hcomm hcontain
  omega

end Stellmacher.SectionNine
