module
public import Stellmacher.SectionEight.EightTwoDistanceTwoDefs
public import Stellmacher.SectionEight.EightTwoEdgeQuadraticAction
public import Stellmacher.SectionFiveToSeven.VertexCenterNeighborJoin

/-!
# The central supplement at the second backward vertex of (8.2)

Let m be the actual backward neighbor of a and n a neighbor of m forming
an actual critical pair (n,a). For critical length greater than one, the
source subgroup V0 = Va ∩ Qm ∩ Qfirst equals Za joined with V0 ∩ Qn.
This is the instance of the source's neighbor-core supplement needed for
its final distance-two Frattini transfer.

The vertex-center normal-closure comparison puts Za in Va, while critical
minimality puts it in both neighboring cores, hence in V0. Noncommutation
of the critical endpoint centers forces Za outside Qn, since Qn centralizes
Zn. The actual edge stabilizer Gm ∩ Gn contains V0, and Qn has index two
there by the odd-dihedral core quotient. Its two cosets give the supplement.
No centrality, normality or index-four premise on V0 is needed for this
containment step; centrality is used by the subsequent Frattini comparison.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), printed p.38,
`refs/latex/stellmacher-n-group.tex`, specialized to k = a-2 in the
sentence V0 = Za (V0 ∩ Qk). The vertices remain in the supplied local graph.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_vzero_central_supplement_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 1 < ctx.criticalPath.length)
    (m n : ctx.Γ.Vertex)
    (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hn : n ∈ neighborhood ctx.Γ m)
    (hcritical : IsCriticalPair ctx.Γ n ctx.criticalPath.a) :
    distanceTwoVZero ctx m = ZAt ctx.Γ ctx.criticalPath.a ⊔
      (distanceTwoVZero ctx m ⊓ QAt ctx.Γ n) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V0 := distanceTwoVZero ctx m
  let A := z Γ cp.a
  let B := q Γ n
  let W := stabilizer Γ m ⊓ stabilizer Γ n
  change 1 < cp.length at hlen
  have hadj := (SevenSix.mem_neighborhood_iff_adjacent Γ).mp hn
  have hZV0 : A ≤ V0 := by
    have hZm : z Γ cp.a ≤ q Γ m := by
      apply SevenSix.critical_minimality Γ cp
      have hd := (SevenSix.adjacent_iff_distance_eq_one Γ).mp
        ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hm)
      change Γ.distance cp.a m = 1 at hd
      omega
    have hZfirst : z Γ cp.a ≤ q Γ cp.firstStep := by
      apply SevenSix.critical_minimality Γ cp
      have hd := (SevenSix.adjacent_iff_distance_eq_one Γ).mp cp.firstStep_adj
      omega
    exact le_inf (le_inf
      (vertex_center_le_neighbor_join ctx.sectionSeven Γ cp.a m hm) hZm) hZfirst
  have hV0W : V0 ≤ W := by
    have hV0m : V0 ≤ q Γ m := inf_le_left.trans inf_le_right
    have hQmGm : q Γ m ≤ stabilizer Γ m := by
      rw [q, Γ.twoCoreAt_def]
      exact SevenSix.twoCoreIn_le _
    have hQmGn : q Γ m ≤ stabilizer Γ n :=
      ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core m n hn
        (default : Sylow 2 ↥W)).2.2
    exact hV0m.trans (le_inf hQmGm hQmGn)
  have hindex : B.relIndex W = 2 := by
    have hSyl := eight_two_adjacent_intersection_is_sylow_local ctx hcenter n m
      (Γ.adjacent_symm hadj)
    rw [inf_comm] at hSyl
    rw [show B = twoCoreIn (stabilizer Γ n) from Γ.twoCoreAt_def n]
    exact eight_two_core_relIndex_two _ W hSyl
      (eight_two_dihedral_core_local ctx hcenter n)
  have hnot : ¬ A ≤ B := by
    intro hAB
    have hnrev : m ∈ neighborhood Γ n :=
      (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hadj)
    have hZnC : z Γ n ≤ Subgroup.centralizer (q Γ n : Set G) :=
      ((lemma_seven_three ctx.sectionSeven Γ).center_core n m hnrev).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _))
    apply eight_two_critical_pair_commutator_ne_local ctx hcenter n cp.a hcritical
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hZnC.trans (Subgroup.centralizer_le hAB))
  change V0 = A ⊔ (V0 ⊓ B)
  apply le_antisymm
  · obtain ⟨a, ha, haB⟩ := SetLike.not_le_iff_exists.mp hnot
    intro x hx
    by_cases hxB : x ∈ B
    · exact (le_sup_right : V0 ⊓ B ≤ A ⊔ (V0 ⊓ B)) ⟨hx, hxB⟩
    · have hxa : x * a⁻¹ ∈ B := by
        exact ((B.subgroupOf W).mul_mem_iff_of_index_two hindex).mpr
          (show (⟨x, hV0W hx⟩ : W) ∈ B.subgroupOf W ↔
              (⟨a, hV0W (hZV0 ha)⟩ : W)⁻¹ ∈ B.subgroupOf W by
            change x ∈ B ↔ a⁻¹ ∈ B
            simp [hxB, haB])
      have hxaV : x * a⁻¹ ∈ A ⊔ (V0 ⊓ B) :=
        (le_sup_right : V0 ⊓ B ≤ A ⊔ (V0 ⊓ B)) ⟨V0.mul_mem hx (V0.inv_mem (hZV0 ha)), hxa⟩
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using
        (A ⊔ (V0 ⊓ B)).mul_mem hxaV ((le_sup_left : A ≤ A ⊔ (V0 ⊓ B)) ha)
  · exact sup_le hZV0 inf_le_left

end Stellmacher.SectionEight
