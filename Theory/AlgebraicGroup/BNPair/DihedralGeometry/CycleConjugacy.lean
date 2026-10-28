module

public import Theory.AlgebraicGroup.BNPair.DihedralGeometry

/-!
# Apartment conjugacy from the cycle bound

Assume the normalizer apartment of a marked octagonal Tits system is a simple
sixteen-cycle and that the coset incidence graph has no shorter cycle. Then
every simple sixteen-cycle is a translate of that apartment under the given
group action.

Bruhat coverage puts the edges at positions 7 and 15 in one apartment translate.
The two intervening seven-edge paths must lie in that apartment: an apartment
supplies a path of length at most eight between their endpoints, and two
different such paths would produce a cycle of length at most fifteen. These
arcs cover the sixteen vertices. Equality follows since both simple cycles
have sixteen distinct vertices.

This is the conditional geometric step in the rank-two BN-pair construction
associated to GLS3 §§2.3 and 2.6, `refs/KGroup/GLS3/chapter2.tex`. The standard
apartment cycle and the lower bound on cycle lengths remain explicit premises.
-/

namespace Theory.AlgebraicGroup.TitsSystem.DihedralGeometry

open SimpleGraph Subgroup
open scoped Pointwise

namespace CycleConjugacy
variable {V : Type*} {G : SimpleGraph V}

/-- Distinct short paths would give a cycle below the assumed bound. -/
private theorem short_paths_eq
    (hG : ∀ v (p : G.Walk v v), p.IsCycle → 16 ≤ p.length)
    {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < 16) : p = q := by
  by_contra hne
  obtain ⟨w, _, _, c, hc, hcl⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := hG w c hc
  omega

/-- One of the two arcs of a sixteen-step loop has length at most eight. -/
private theorem short_walk_in_loop {a u v : V} (c : G.Walk a a)
    (hlen : c.length = 16) (hu : u ∈ c.support) (hv : v ∈ c.support) :
    ∃ q : G.Walk u v, q.length ≤ 8 ∧ q.support ⊆ c.support := by
  classical
  let r := c.rotate u hu
  have hvr : v ∈ r.support := (c.mem_support_rotate_iff u hu).mpr hv
  have hr : r.support ⊆ c.support := fun _ h =>
    (c.mem_support_rotate_iff u hu).mp h
  have hsum : (r.takeUntil v hvr).length + (r.dropUntil v hvr).length = 16 := by
    rw [← Walk.length_append, r.take_spec hvr]
    simpa only [r, Walk.length_rotate] using hlen
  by_cases hle : (r.takeUntil v hvr).length ≤ 8
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
    (hG : ∀ v (p : G.Walk v v), p.IsCycle → 16 ≤ p.length)
    {a u v : V} {p : G.Walk u v} (hp : p.IsPath) (hlen : p.length ≤ 7)
    (c : G.Walk a a) (hc : c.length = 16)
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

/-- Four vertices bounding the complementary seven-edge arcs determine the support. -/
private theorem cycle_support_eq_of_opposite_edges
    (hG : ∀ v (p : G.Walk v v), p.IsCycle → 16 ≤ p.length)
    {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsCycle) (hpl : p.length = 16)
    (hq : q.IsCycle) (hql : q.length = 16)
    (h0 : a ∈ q.support) (h7 : p.getVert 7 ∈ q.support)
    (h8 : p.getVert 8 ∈ q.support) (h15 : p.getVert 15 ∈ q.support) :
    {w | w ∈ p.support} = {w | w ∈ q.support} := by
  classical
  have hfirst : (p.take 7).support ⊆ q.support :=
    short_path_support_subset hG (hp.isPath_take (by omega))
      (by simp [Walk.take_length, hpl]) q hql h0 h7
  have hlast : ((p.drop 8).take 7).support ⊆ q.support :=
    short_path_support_subset hG ((hp.isPath_drop (by decide : 0 < 8)).take 7)
      (by simp [Walk.take_length, Walk.drop_length, hpl]) q hql h8
      (by simpa only [Walk.drop_getVert] using h15)
  have hsub : p.support ⊆ q.support := by
    intro w hw
    obtain ⟨n, rfl, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hw
    by_cases hsmall : n ≤ 7
    · apply hfirst
      have := (p.take 7).getVert_mem_support n
      simpa only [Walk.take_getVert, Nat.min_eq_right hsmall] using this
    · by_cases hend : n = 16
      · simpa only [hend, ← hpl, Walk.getVert_length] using h0
      · apply hlast
        have := ((p.drop 8).take 7).getVert_mem_support (n - 8)
        simpa only [Walk.take_getVert, Walk.drop_getVert,
          Nat.min_eq_right (show n - 8 ≤ 7 by omega),
          Nat.add_sub_of_le (show 8 ≤ n by omega)] using this
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

namespace OctagonalDatum

/-- Every simple sixteen-cycle is an actual translate of the normalizer apartment,
provided that the standard apartment is a sixteen-cycle and all cycles have
length at least sixteen. The conclusion is equality of vertex support sets in
the given coset action. No finiteness assumption is needed. -/
public theorem apartment_translates_of_cycle_bound (D : OctagonalDatum T F)
    (hA : StandardApartmentCycle T F)
    (hG : ∀ v (p : (graph F).Walk v v), p.IsCycle → 16 ≤ p.length)
    (v : CosetGeometry.Vertex F) (p : (graph F).Walk v v)
    (hp : p.IsCycle) (hlen : p.length = 16) :
    ∃ g : X, g • apartment T F = {w | w ∈ p.support} := by
  classical
  obtain ⟨g, h7, h8, h15, h16⟩ := exists_apartment_for_edges F T D.borel_le
    (p.adj_getVert_succ (i := 7) (by omega))
    (p.adj_getVert_succ (i := 15) (by omega))
  obtain ⟨a, c, hc, hcl, hcs⟩ := hA
  let q := c.map (smulHom F g)
  have hq : q.IsCycle := Walk.IsCycle.map (MulAction.injective g) hc
  have hql : q.length = 16 := by simpa only [q, Walk.length_map] using hcl
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
        simpa only [show 15 + 1 = p.length by omega, Walk.getVert_length] using h16)
      (by change p.getVert 7 ∈ {w | w ∈ q.support}; rwa [hqs])
      (by change p.getVert 8 ∈ {w | w ∈ q.support}; rwa [hqs])
      (by change p.getVert 15 ∈ {w | w ∈ q.support}; rwa [hqs])
  exact ⟨g, hqs.symm.trans hs.symm⟩

end OctagonalDatum
end Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
