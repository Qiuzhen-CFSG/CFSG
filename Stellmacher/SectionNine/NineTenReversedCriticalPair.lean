module

public import Stellmacher.SectionNine.NineTenExtractedPredecessor
public import Stellmacher.SectionNine.NineTenPredecessorCoreExclusion

/-!
# The reversed critical pair after predecessor noncommutation

For the same normalized geometric extraction and retained terminal
neighbor, noncommutation of predecessor V with the penultimate center
gives the reversed critical pair. Its centers commute, so it is suitable
for the subsequent Section Nine argument with the roles interchanged.

The extracted-predecessor theorem gives the critical-pair-or-core
alternative and adjacency. The preceding core-exclusion theorem removes
that alternative using the retained noncommuting neighbor center.
Critical minimality places the penultimate center in the original
initial core, while the predecessor center lies in the initial center.
The center/core centralization therefore proves their commutation.

This is Stellmacher (9.10)(5), printed p.57 of
`refs/files/stellmacher-n-group.pdf`, conditional on exactly the module
noncommutation established in the source paragraph immediately before it.
The theorem preserves the actual extraction and does not assume a new
critical pair or use a pending numbered result.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_reversed_critical_pair_of_noncommutation
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hnew : ctx.Γ.act data.x⁻¹ second = ctx.criticalPath.a)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcenters : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (hmodules : ⁅VAt ctx.Γ (ctx.Γ.act data.x⁻¹ (ctx.criticalPath.path ⟨3,by omega⟩)),
      ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ ≠ ⊥) :
    let predecessor := ctx.Γ.act data.x⁻¹ (ctx.criticalPath.path ⟨3,by omega⟩)
    let penultimate := ctx.criticalPath.path
      ⟨ctx.criticalPath.length - 1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    IsCriticalPair ctx.Γ penultimate predecessor ∧
      ⁅ZAt ctx.Γ penultimate, ZAt ctx.Γ predecessor⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let predecessor := Γ.act data.x⁻¹ (cp.path ⟨3,by change 4 < cp.length at hb; omega⟩)
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  obtain ⟨hpred, _, halt⟩ := nine_ten_extracted_predecessor_alternative Γ cp
    (by change 4 < cp.length at hb; omega) second actor E A0 data hsecond hnew
  have hexcluded := nine_ten_predecessor_core_exclusion ctx hb predecessor neighbor
    hpred hneighbor hcenters hmodules
  refine ⟨halt.resolve_left hexcluded, ?_⟩
  have hZpenQ : ZAt Γ penultimate ≤ QAt Γ cp.a := by
    have hdist := path_distance_le Γ cp 0 (cp.length-1) (Nat.zero_le _) (Nat.sub_le _ _)
    change Γ.distance (cp.path 0) penultimate ≤ cp.length-1-0 at hdist
    rw [cp.path_start,Nat.sub_zero] at hdist
    apply critical_minimality Γ cp
    rw [Γ.distance_symm]
    change 4 < cp.length at hb
    omega
  have hZpredZa : ZAt Γ predecessor ≤ ZAt Γ cp.a :=
    ((nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩).2 predecessor
      ((mem_neighborhood_iff_adjacent Γ).mpr hpred)).2
  have hZaCore := ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hcoreZa : QAt Γ cp.a ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) :=
    Subgroup.le_centralizer_iff.mpr hZaCore
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hZpenQ.trans (hcoreZa.trans (Subgroup.centralizer_le hZpredZa)))

end Stellmacher.SectionNine
