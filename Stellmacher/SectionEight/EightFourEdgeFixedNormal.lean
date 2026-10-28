module
public import Stellmacher.SectionEight.EightFourOppositeClosureImage
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# The barred fixed subgroup is normal in the full initial edge

In the nontrivial-closure branch of Stellmacher (8.4), the barred fixed
subgroup is normal in the intersection of the initial two stabilizers.
Source (3) identifies it with the initial center intersected with the
centralizer of the opposite-center closure. The edge normalizes the first
factor through its initial stabilizer and the second through its next
stabilizer. The local center/core containments put the fixed subgroup inside
the actual edge, completing normality.

The result holds over the exact local context; the canonical theorem remains
an exact wrapper preserving the supplied graph, witness and fixed subgroup.
This makes the transported edge-fixed subgroups used before source (7)
well-defined. It retains the faithful witness and does not assert that the
next stabilizer normalizes the initial center. Source: Stellmacher (8.4),
Journal of Algebra190 (1997), printed p.39 / PDF p.29 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_edge_fixed_normal_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    NormalIn (w.oneJFixedPoints S)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let F := w.oneJFixedPoints S
  let K := oppositeClosureLocal ctx
  let P := GAt Γ cp.firstStep
  let h := ctx.sectionSeven
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hZaQ : ZAt Γ cp.a ≤ QAt Γ cp.a :=
    ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
      (Subgroup.map_subtype_le _)
  have hFedge : F ≤ GAt Γ cp.a ⊓ P :=
    (Subgroup.map_subtype_le _).trans (hZaQ.trans
      ((SevenSix.local_cores_le_edge_sylow h Γ cp).1.trans cp.S_le_edge_stabilizers))
  have hFeq : F = ZAt Γ cp.a ⊓ Subgroup.centralizer (K : Set H) :=
    fixed_center_eq_opposite_closure_centralizer_of_image_local ctx w
      (eight_four_opposite_closure_image_local ctx hcenter w hbranch)
  have hKn : NormalIn K P := opposite_closure_normal_next_local ctx
  have hPK : P ≤ Subgroup.normalizer (K : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKn.1).mp hKn.2
  refine ⟨hFedge, (Subgroup.normal_subgroupOf_iff_le_normalizer hFedge).mpr ?_⟩
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor point hpoint
  rw [hFeq] at hpoint ⊢
  refine ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp
      (stabilizer_le_normalizer_z Γ cp.a hactor.1) point).mp hpoint.1
  · change actor * point * actor⁻¹ ∈ Subgroup.centralizer (K : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hconj : actor⁻¹ * k * actor ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hPK (P.inv_mem hactor.2)) k).mp hk
    have heq := Subgroup.mem_centralizer_iff.mp hpoint.2 (actor⁻¹ * k * actor) hconj
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel_right, mul_inv_cancel, mul_one] using
      congrArg (fun y => actor * y * actor⁻¹) heq


/-- Canonical specialization through the unchanged local graph and witness. -/
public theorem eight_four_edge_fixed_normal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    NormalIn (w.oneJFixedPoints S)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) := by
  exact eight_four_edge_fixed_normal_local ctx.toLocalContext hcenter w hbranch

end Stellmacher.SectionEight
