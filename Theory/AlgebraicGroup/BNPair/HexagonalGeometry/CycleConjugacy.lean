module

public import Theory.AlgebraicGroup.BNPair.HexagonalGeometry

/-!
# Apartment conjugacy from the cycle bound

Assume the normalizer apartment of a marked hexagonal Tits system is a simple
twelve-cycle and that the coset incidence graph has no shorter cycle. Then
every simple twelve-cycle is a translate of that apartment under the given
group action.

Bruhat coverage puts the edges at positions 5 and 11 in one apartment translate.
The two intervening five-edge paths must lie in that apartment: an apartment
supplies a path of length at most six between their endpoints, and two
different such paths would produce a cycle of length at most eleven. These
arcs cover the twelve vertices. Equality follows since both simple cycles
have twelve distinct vertices.

This is the conditional geometric step in the rank-two BN-pair construction
associated to GLS3 §§2.3 and 2.6, `refs/KGroup/GLS3/chapter2.tex`. The standard
apartment cycle and the lower bound on cycle lengths remain explicit premises.
-/

namespace Theory.AlgebraicGroup.TitsSystem.HexagonalGeometry

open DihedralGeometry

open SimpleGraph Subgroup
open scoped Pointwise

namespace CycleConjugacy
variable {V : Type*} {G : SimpleGraph V}

/-- Distinct short paths would give a cycle below the assumed bound. -/
private theorem short_paths_eq
    (hG : ∀ v (p : G.Walk v v), p.IsCycle → 12 ≤ p.length)
    {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < 12) : p = q := by
  by_contra hne
  obtain ⟨w, _, _, c, hc, hcl⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := hG w c hc
  omega

/-- One of the two arcs of a twelve-step loop has length at most six. -/
private theorem short_walk_in_loop {a u v : V} (c : G.Walk a a)
    (hlen : c.length = 12) (hu : u ∈ c.support) (hv : v ∈ c.support) :
    ∃ q : G.Walk u v, q.length ≤ 6 ∧ q.support ⊆ c.support := by
  classical
  let r := c.rotate u hu
  have hvr : v ∈ r.support := (c.mem_support_rotate_iff u hu).mpr hv
  have hr : r.support ⊆ c.support := fun _ h =>
    (c.mem_support_rotate_iff u hu).mp h
  have hsum : (r.takeUntil v hvr).length + (r.dropUntil v hvr).length = 12 := by
    rw [← Walk.length_append, r.take_spec hvr]
    simpa only [r, Walk.length_rotate] using hlen
  by_cases hle : (r.takeUntil v hvr).length ≤ 6
  · exact ⟨r.takeUntil v hvr, hle,
      fun _ h => hr (r.support_takeUntil_subset_support hvr h)⟩
  · refine ⟨(r.dropUntil v hvr).reverse, ?_, ?_⟩
    · rw [Walk.length_reverse]
      omega
    · intro w hw
      apply hr
      apply r.support_dropUntil_subset_support hvr
      simpa only [Walk.support_reverse, List.mem_reverse] using hw

private theorem short_path_support_subset
    (hG : ∀ v (p : G.Walk v v), p.IsCycle → 12 ≤ p.length)
    {a u v : V} {p : G.Walk u v} (hp : p.IsPath) (hlen : p.length ≤ 5)
    (c : G.Walk a a) (hc : c.length = 12)
    (hu : u ∈ c.support) (hv : v ∈ c.support) : p.support ⊆ c.support := by
  classical
  obtain ⟨q, hql, hqs⟩ := short_walk_in_loop c hc hu hv
  have hpeq : p = q.bypass := short_paths_eq hG hp q.bypass_isPath (by
    have := q.length_bypass_le_length
    omega)
  rw [hpeq]
  exact fun _ h => hqs (q.support_bypass_subset_support h)

private theorem cycle_card_support [DecidableEq V] {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    p.support.toFinset.card = p.length := by
  classical
  have heq : p.support.toFinset = p.support.tail.toFinset := by
    ext w
    simp only [List.mem_toFinset, p.mem_support_iff]
    constructor
    · rintro (rfl | hw)
      · exact p.end_mem_tail_support hp.not_nil
      · exact hw
    · exact Or.inr
  rw [heq, List.toFinset_card_of_nodup hp.support_nodup, List.length_tail, Walk.length_support]
  omega

/-- Four vertices bounding the complementary five-edge arcs determine the support. -/
private theorem cycle_support_eq_of_opposite_edges
    (hG : ∀ v (p : G.Walk v v), p.IsCycle → 12 ≤ p.length)
    {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsCycle) (hpl : p.length = 12)
    (hq : q.IsCycle) (hql : q.length = 12)
    (h0 : a ∈ q.support) (h5 : p.getVert 5 ∈ q.support)
    (h6 : p.getVert 6 ∈ q.support) (h11 : p.getVert 11 ∈ q.support) :
    {w | w ∈ p.support} = {w | w ∈ q.support} := by
  classical
  have hfirst : (p.take 5).support ⊆ q.support :=
    short_path_support_subset hG (hp.isPath_take (by omega))
      (by simp [Walk.take_length, hpl]) q hql h0 h5
  have hlast : ((p.drop 6).take 5).support ⊆ q.support :=
    short_path_support_subset hG ((hp.isPath_drop (by decide : 0 < 6)).take 5)
      (by simp [Walk.take_length, Walk.drop_length, hpl]) q hql h6
      (by simpa only [Walk.drop_getVert] using h11)
  have hsub : p.support ⊆ q.support := by
    intro w hw
    obtain ⟨n, rfl, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hw
    by_cases hsmall : n ≤ 5
    · apply hfirst
      have := (p.take 5).getVert_mem_support n
      simpa only [Walk.take_getVert, Nat.min_eq_right hsmall] using this
    · by_cases hend : n = 12
      · simpa only [hend, ← hpl, Walk.getVert_length] using h0
      · apply hlast
        have := ((p.drop 6).take 5).getVert_mem_support (n - 6)
        simpa only [Walk.take_getVert, Walk.drop_getVert,
          Nat.min_eq_right (show n - 6 ≤ 5 by omega),
          Nat.add_sub_of_le (show 6 ≤ n by omega)] using this
  have heq : p.support.toFinset = q.support.toFinset :=
    Finset.eq_of_subset_of_card_le (by
      intro w hw
      exact List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hw))) (by
      rw [cycle_card_support hp, cycle_card_support hq, hpl, hql])
  ext w
  exact (List.mem_toFinset (a := w)).symm.trans
    (heq ▸ List.mem_toFinset)

end CycleConjugacy

variable {X I : Type*} [Group X]
variable {T : TitsSystem (X := X)} {F : I → Subgroup X}

namespace HexagonalDatum

/-- Every simple twelve-cycle is an actual translate of the normalizer apartment,
provided that the standard apartment is a twelve-cycle and all cycles have
length at least twelve. The conclusion is equality of vertex support sets in
the given coset action. No finiteness assumption is needed. -/
public theorem apartment_translates_of_cycle_bound (D : HexagonalDatum T F)
    (hA : StandardApartmentCycle T F)
    (hG : ∀ v (p : (graph F).Walk v v), p.IsCycle → 12 ≤ p.length)
    (v : CosetGeometry.Vertex F) (p : (graph F).Walk v v)
    (hp : p.IsCycle) (hlen : p.length = 12) :
    ∃ g : X, g • apartment T F = {w | w ∈ p.support} := by
  classical
  obtain ⟨g, h5, h6, h11, h12⟩ := exists_apartment_for_edges F T D.borel_le
    (p.adj_getVert_succ (i := 5) (by omega))
    (p.adj_getVert_succ (i := 11) (by omega))
  obtain ⟨a, c, hc, hcl, hcs⟩ := hA
  let q := c.map (smulHom F g)
  have hq : q.IsCycle := Walk.IsCycle.map (MulAction.injective g) hc
  have hql : q.length = 12 := by simpa only [q, Walk.length_map] using hcl
  have hqs : {w | w ∈ q.support} = g • apartment T F := by
    rw [← hcs]
    ext w
    change w ∈ (c.map (smulHom F g)).support ↔ _
    rw [Walk.support_map]
    simp only [List.mem_map, Set.mem_smul_set, Set.mem_ofPred_eq, smulHom_apply]
  have hs : {w | w ∈ p.support} = {w | w ∈ q.support} :=
    CycleConjugacy.cycle_support_eq_of_opposite_edges hG hp hlen hq hql
      (by
        change v ∈ {w | w ∈ q.support}
        rw [hqs]
        simpa only [show 11 + 1 = p.length by omega, Walk.getVert_length] using h12)
      (by change p.getVert 5 ∈ {w | w ∈ q.support}; rwa [hqs])
      (by change p.getVert 6 ∈ {w | w ∈ q.support}; rwa [hqs])
      (by change p.getVert 11 ∈ {w | w ∈ q.support}; rwa [hqs])
  exact ⟨g, hqs.symm.trans hs.symm⟩

end HexagonalDatum
end Theory.AlgebraicGroup.TitsSystem.HexagonalGeometry
