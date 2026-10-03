module
public import Stellmacher.SectionEight.EightTwoDistanceTwoDefs
public import Stellmacher.SectionEight.EightTwoEdgeQuadraticAction
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore
public import Theory.GroupTheory.TwoIndexTwoIntersections

/-!
# The common subgroup has index four at critical distance two

In the noncentral case of Stellmacher (8.2), suppose the critical length
is two and m is a backward neighbor of a such that (m,firstStep) is
critical. The two neighboring centers, together with
V0=Va intersect Qm intersect Qfirst, generate Va, and V0 has index four
in Va. The statement uses the actual local graph and the shared
`distanceTwoVZero` definition.

Critical minimality puts Va inside Qa, hence in both adjacent edge
intersections by (7.3). The edge theorem makes those intersections Sylow,
and the odd-dihedral core quotients give each neighboring core relative
index two there. Inside Va these indices remain at most two. Criticality
and the nonzero critical commutator give the two opposite outside
directions, so both restricted indices are exactly two. Apply the generic
two-index-two-intersections theorem to obtain the generating equality and
index four. Normality and centrality of V0 belong to the separate
center-structure argument.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), printed p.38,
the V0 paragraph in `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_distance_two_index_structure_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : ctx.criticalPath.length = 2)
    (m : ctx.Γ.Vertex) (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hcritical : IsCriticalPair ctx.Γ m ctx.criticalPath.firstStep) :
    VAt ctx.Γ ctx.criticalPath.a =
      ZAt ctx.Γ m ⊔ ZAt ctx.Γ ctx.criticalPath.firstStep ⊔ distanceTwoVZero ctx m ∧
    (distanceTwoVZero ctx m).relIndex (VAt ctx.Γ ctx.criticalPath.a) = 4 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Va := v Γ cp.a
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hVaQa : Va ≤ q Γ cp.a :=
    SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
      (by change 1 < ctx.criticalPath.length; omega) cp.a
  have hVaGa : Va ≤ stabilizer Γ cp.a := by
    refine hVaQa.trans ?_
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZVa (d : Γ.Vertex) (hd : d ∈ neighborhood Γ cp.a) : z Γ d ≤ Va := by
    dsimp [Va]
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨d, hd, rfl⟩
  have hZcore (d : Γ.Vertex) (hd : d ∈ neighborhood Γ cp.a) :
      z Γ d ≤ omegaOneCenter (q Γ d) := by
    apply (lemma_seven_three ctx.sectionSeven Γ).center_core d cp.a
    exact (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hd))
  have hZmQm : z Γ m ≤ q Γ m :=
    (hZcore m hm).trans ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
      (Subgroup.map_subtype_le _))
  have hZfirstQfirst : z Γ cp.firstStep ≤ q Γ cp.firstStep :=
    (hZcore cp.firstStep hfirst).trans ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
      (Subgroup.map_subtype_le _))
  have hZmOut : ¬ z Γ m ≤ q Γ cp.firstStep := hcritical.2
  have hZfirstOut : ¬ z Γ cp.firstStep ≤ q Γ m := by
    intro hle
    apply eight_two_critical_pair_commutator_ne_local ctx hcenter m cp.firstStep hcritical
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((hZcore m hm).trans ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((SevenSix.centerAmbient_le_centralizer _).trans (Subgroup.centralizer_le hle))))
  have hindex (d : Γ.Vertex) (hd : d ∈ neighborhood Γ cp.a)
      (hout : ¬ Va ≤ q Γ d) : (q Γ d).relIndex Va = 2 := by
    let edge := stabilizer Γ d ⊓ stabilizer Γ cp.a
    have hVaedge : Va ≤ edge := by
      refine le_inf ?_ hVaGa
      let T : Sylow 2 ↥(stabilizer Γ cp.a ⊓ stabilizer Γ d) := default
      exact hVaQa.trans ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a d hd T).2.2
    have hSylow : IsSylowTwoIn edge (stabilizer Γ d) :=
      eight_two_adjacent_intersection_is_sylow_local ctx hcenter d cp.a
        (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hd))
    have hidx : (q Γ d).relIndex edge = 2 := by
      rw [q, Γ.twoCoreAt_def]
      exact eight_two_core_relIndex_two (stabilizer Γ d) edge hSylow
        (eight_two_dihedral_core_local ctx hcenter d)
    have hle := Subgroup.relIndex_le_of_le_right (H := q Γ d) hVaedge
      (by omega : (q Γ d).relIndex edge ≠ 0)
    have hne0 : (q Γ d).relIndex Va ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hne1 : (q Γ d).relIndex Va ≠ 1 := fun heq => hout (Subgroup.relIndex_eq_one.mp heq)
    omega
  have hQm : (q Γ m).relIndex Va = 2 :=
    hindex m hm (fun hle => hZfirstOut ((hZVa cp.firstStep hfirst).trans hle))
  have hQfirst : (q Γ cp.firstStep).relIndex Va = 2 :=
    hindex cp.firstStep hfirst (fun hle => hZmOut ((hZVa m hm).trans hle))
  exact Subgroup.sup_intersection_eq_and_relIndex_four Va (z Γ m) (z Γ cp.firstStep)
    (q Γ m) (q Γ cp.firstStep) (hZVa m hm) (hZVa cp.firstStep hfirst)
    hZmQm hZfirstQfirst hZmOut hZfirstOut hQm hQfirst

end Stellmacher.SectionEight
