module
public import Stellmacher.SectionEight.EightTwoBackwardNeighbor
public import Stellmacher.SectionEight.EightTwoBackwardNoncontainment
public import Stellmacher.SectionEight.EightTwoShiftNormalization
public import Stellmacher.SectionEight.EightTwoCriticalPairTransport

/-!
# Two backward critical pairs in the original graph

In the noncentral case of Stellmacher (8.2), a critical path of length greater
than one admits two successive generating backward neighbors. Both vertices
and both opposite endpoints belong to the original coset graph and selected
path. The first opposite endpoint is the original penultimate vertex, and
the second is the original antepenultimate vertex.

Choose the first generating neighbor and use backward noncontainment to
shift the critical path. Path-preserving normalization anchors that exact
shift at the distinguished edge. Noncentrality and endpoint noncommutation
supply the genuine local context for a second choice. Pull this neighbor
back by the inverse actor; covariance transports its generating equality
and noncontainment. The retained path formula identifies the second endpoint.
An inverse-transported shortest path and critical minimality prove the
second critical pair in the original graph.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), printed pp.37–38,
refs/latex/stellmacher-n-group.tex, the choices of a-1 and a-2. This provides
the shared geometric input for both remaining critical-distance cases.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_exists_two_backward_shifts_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 1 < ctx.criticalPath.length) :
    ∃ m n : ctx.Γ.Vertex,
      m ∈ neighborhood ctx.Γ ctx.criticalPath.a ∧
      n ∈ neighborhood ctx.Γ m ∧
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) ⊔
        ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a ∧
      (GAt ctx.Γ m ⊓ GAt ctx.Γ n) ⊔
        ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩) =
          GAt ctx.Γ m ∧
      IsCriticalPair ctx.Γ m
        (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩) ∧
      IsCriticalPair ctx.Γ n
        (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2, by omega⟩) ∧
      (¬ ZAt ctx.Γ m ≤ GAt ctx.Γ ctx.criticalPath.a') ∧
      (¬ ZAt ctx.Γ n ≤ GAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩)) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let last := cp.path ⟨cp.length - 1, by omega⟩
  let beforeLast := cp.path ⟨cp.length - 2, by omega⟩
  change 1 < cp.length at hlen
  obtain ⟨m, hm, hgen⟩ := eight_two_exists_backward_neighbor_local ctx hcenter
  have hout := eight_two_backward_neighbor_not_le_local ctx hcenter m hm hgen
  have hcrit := eight_two_shifted_critical_pair_of_not_le ctx.sectionSeven Γ cp m hm hout
  obtain ⟨actor, shifted, hstart, hend, hfirst, hlength, hpath⟩ :=
    eight_two_exists_path_preserving_backward_shift ctx.sectionSeven Γ cp m hm hout
  let shiftedCtx : SectionEightLocalContext G S P1 P2 :=
    { sectionSeven := ctx.sectionSeven
      sixThree := ctx.sixThree
      Γ := Γ
      criticalPath := shifted
      commutator_ne := eight_two_critical_pair_commutator_ne_local ctx hcenter
        shifted.a shifted.a' shifted.critical }
  have hshiftedCenter : ¬ ZAt Γ shifted.firstStep ≤
      CenterAmbient (GAt Γ shifted.firstStep) :=
    eight_two_all_vertex_centers_noncentral_local ctx hcenter shifted.firstStep
  obtain ⟨back, hback, hbackGen⟩ :=
    eight_two_exists_backward_neighbor_local shiftedCtx hshiftedCenter
  have hbackOut := eight_two_backward_neighbor_not_le_local
    shiftedCtx hshiftedCenter back hback hbackGen
  have hbackCritical := eight_two_shifted_critical_pair_of_not_le
    ctx.sectionSeven Γ shifted back hback hbackOut
  let n := Γ.act actor⁻¹ back
  have hinverse (vertex : Γ.Vertex) : Γ.act actor⁻¹ (Γ.act actor vertex) = vertex := by
    rw [← Γ.act_mul, mul_inv_cancel, Γ.act_one]
  have hnact : Γ.act actor n = back := by
    dsimp only [n]
    rw [← Γ.act_mul, inv_mul_cancel, Γ.act_one]
  have hn : n ∈ neighborhood Γ m := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    have hadj := adjacent_act Γ actor⁻¹
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hback)
    change Γ.adjacent (Γ.act actor⁻¹ shifted.a) n at hadj
    simpa only [hstart, hinverse] using hadj
  have hgen2 : (stabilizer Γ m ⊓ stabilizer Γ n) ⊔ z Γ last = stabilizer Γ m := by
    apply Subgroup.map_injective (f := (MulAut.conj actor⁻¹).toMonoidHom)
      (MulAut.conj actor⁻¹).injective
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective]
    change (stabilizer Γ shifted.a ⊓ stabilizer Γ back) ⊔ z Γ shifted.a' =
      stabilizer Γ shifted.a at hbackGen
    rw [hstart, hend, ← hnact, stabilizer_act, stabilizer_act, z_act] at hbackGen
    exact hbackGen
  have hout2 : ¬ z Γ n ≤ stabilizer Γ last := by
    intro hle
    apply hbackOut
    change z Γ back ≤ stabilizer Γ shifted.a'
    rw [hend, ← hnact, z_act, stabilizer_act]
    exact Subgroup.map_mono hle
  have hpenult : shifted.path
      ⟨shifted.length - 1, by have := shifted.length_pos; omega⟩ =
        Γ.act actor beforeLast := by
    have heq := hpath ⟨cp.length - 1, by omega⟩ (by dsimp; omega)
    have hindex : Fin.cast (congrArg (· + 1) hlength.symm)
        (⟨cp.length - 1, by omega⟩ : Fin (cp.length + 1)) =
        ⟨shifted.length - 1, by have := shifted.length_pos; omega⟩ := by
      apply Fin.ext
      exact congrArg (fun length => length - 1) hlength.symm
    rw [hindex] at heq
    simpa only [beforeLast, Nat.sub_sub, Nat.reduceAdd] using heq
  have hnot2 : ¬ z Γ n ≤ q Γ beforeLast := by
    intro hle
    apply hbackCritical.2
    change z Γ back ≤ q Γ (shifted.path
      ⟨shifted.length - 1, by have := shifted.length_pos; omega⟩)
    rw [hpenult, ← hnact, z_act, SevenSix.q_act]
    exact Subgroup.map_mono hle
  have hnormalizedDistance : Γ.distance back
      (shifted.path ⟨shifted.length - 1, by have := shifted.length_pos; omega⟩) =
        cp.length := hbackCritical.1.trans (cp.critical.1.symm.trans cp.endpoint_distance)
  have hdist : Γ.distance n beforeLast ≤ cp.length := by
    obtain ⟨path, hzero, hfinal, hadj⟩ := Γ.distance_path back
      (shifted.path ⟨shifted.length - 1, by have := shifted.length_pos; omega⟩)
    have hbound := Γ.distance_le_of_path _ (fun i => Γ.act actor⁻¹ (path i))
      (fun i => adjacent_act Γ actor⁻¹ (hadj i))
    rw [hzero, hfinal] at hbound
    rw [hpenult, hinverse] at hbound
    rw [hpenult] at hnormalizedDistance
    exact hbound.trans_eq hnormalizedDistance
  have hcrit2 : IsCriticalPair Γ n beforeLast := by
    have heq : Γ.distance n beforeLast = cp.length := by
      apply le_antisymm hdist
      by_contra hlt
      exact hnot2 (SevenSix.critical_minimality Γ cp (by omega))
    refine ⟨?_, hnot2⟩
    rw [heq, ← cp.endpoint_distance]
    exact cp.critical.1
  exact ⟨m, n, hm, hn, hgen, hgen2, hcrit, hcrit2, hout, hout2⟩

end Stellmacher.SectionEight
