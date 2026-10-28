module

public import Stellmacher.SectionNine.NineTenActorCommutatorMembership
public import Stellmacher.SectionNine.NineTenTerminalCenterThirdCentralization

/-!
# The same extracted actor supplies the geometric inputs of (9.4)

For the actual second geometric extraction, retain its prescribed actor in
an arbitrary terminal-neighbor center. The third vertex has distance two
from the first step; the actor lies in the first stabilizer, centralizes
the third module, and lies outside the first core. The same inverse
conjugator lies in the actor commutator of the first residual and hence
in the first stabilizer.

The tail of the critical path rules out distances zero and one. A terminal
neighbor center belongs to terminal V, which lies in the first stabilizer.
The extracted actor avoids the new edge stabilizer, whereas the first core
lies in it. Short-distance center-core containments give centralization,
and the actual residual actor bound gives the conjugator membership.

This assembles the geometric inputs in Stellmacher (9.10), printed p.57,
for the later application of (9.4) at r=a+3. It neither changes the actor
nor assumes the common-neighbor generation or the conclusion of (9.4).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix

public theorem nine_ten_prescribed_actor_geometry
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (third second neighbor : ctx.Γ.Vertex)
    (hthird : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hactor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorComm : twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆) :
    ctx.Γ.distance third ctx.criticalPath.firstStep = 2 ∧
      (actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
        actor ∈ Subgroup.centralizer (VAt ctx.Γ third : Set G)) ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      data.x⁻¹ ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers actor⁆ ∧
      data.x⁻¹ ∈ GAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 3 ≤ cp.length := by
    obtain ⟨index, hindex, _⟩ := hthird
    change 3 ≤ ctx.criticalPath.length
    omega
  have htail : Γ.distance third cp.a' ≤ cp.length - 3 := by
    obtain ⟨index, hindex, rfl⟩ := hthird
    have hh := path_distance_le Γ cp 3 cp.length hlength le_rfl
    have heq : (⟨3, by omega⟩ : Fin (cp.length + 1)) = index := Fin.ext hindex.symm
    rwa [heq, cp.path_end] at hh
  have hupper : Γ.distance cp.firstStep third ≤ 2 := by
    obtain ⟨index, hindex, rfl⟩ := hthird
    have hh := path_distance_le Γ cp 1 3 (by omega) hlength
    have heq : (⟨3, by omega⟩ : Fin (cp.length + 1)) = index := Fin.ext hindex.symm
    rwa [heq, cp.path_first] at hh
  have hdistance : Γ.distance third cp.firstStep = 2 := by
    rw [Γ.distance_symm]
    have hprefix := nine_eight_adjacent_distance_le Γ (target := cp.a') cp.firstStep_adj
    rw [cp.endpoint_distance] at hprefix
    by_cases hzero : Γ.distance cp.firstStep third = 0
    · have heq := (Γ.distance_zero_iff _ _).mp hzero
      rw [heq] at hprefix
      omega
    by_cases hone : Γ.distance cp.firstStep third = 1
    · have hh := nine_eight_adjacent_distance_le Γ (target := cp.a')
        ((adjacent_iff_distance_eq_one Γ).mpr hone)
      omega
    omega
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hactorP : actor ∈ GAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2 (hneighborV hactor)
  have hcentral : actor ∈ Subgroup.centralizer (VAt Γ third : Set G) :=
    nine_ten_terminal_neighbor_center_centralizes_third ctx third neighbor
      hthird hneighbor hactor
  have hcore : QAt Γ cp.firstStep ≤ GAt Γ (Γ.act data.x⁻¹ second) :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.firstStep
      (Γ.act data.x⁻¹ second) data.neighbor default).2.2
  have hactorNot : actor ∉ QAt Γ cp.firstStep := fun ha => data.actor_outside (hcore ha)
  have hxE : data.x ∈ E := twoResidualIn_le E data.residual_mem
  exact ⟨hdistance, ⟨hactorP, hcentral⟩, hactorNot,
    nine_ten_conjugator_mem_actor_commutator Γ cp.firstStep second
      (VAt Γ cp.a') E A0 actor data hactorComm,
    (GAt Γ cp.firstStep).inv_mem (data.group_le hxE)⟩

end Stellmacher.SectionNine
