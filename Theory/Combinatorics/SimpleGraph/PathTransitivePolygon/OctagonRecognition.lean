module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths

/-!
# Octagon geometry from two-type nine-path transitivity and smallness

A distance-eight witness gives a geodesic of every shorter length on its
vertex orbit. Rooted path transitivity makes all corresponding nonbacktracking
walks geodesic. Rotating any short cycle to this orbit and comparing its two
arcs proves girth at least sixteen. Two distinct eight-edge geodesics then
produce a sixteen-cycle. Its nine-edge prefix has a complementary seven-edge
arc. The two vertex orbits and path transitivity give this endpoint bound for
every nine-walk, excluding any geodesic longer than eight.

Both vertex types are retained throughout; transitivity at just one root is
not a substitute for the hypothesis here. No finiteness, diameter or girth
conclusion is assumed. This is the source octagon step of Aschbacher–Smith
F.4.8, using F.3.5, printed pp.271 and 278.
-/

public noncomputable section
namespace SimpleGraph.PathTransitivePolygon.OctagonRecognition
open SimpleGraph
variable {V A : Type*} {G : SimpleGraph V} [Group A] [MulAction A V]

private theorem even_length_iff (color : V → Bool)
    (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    {u v : V} (p : G.Walk u v) : Even p.length ↔ color u = color v := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    rw [Walk.length_cons, Nat.even_add_one, ih]
    have hne := hcolor h
    cases hu : color u <;> cases hv : color v <;> cases hw : color w <;> simp_all

private theorem color_eq_of_two_ne (color : V → Bool) {x y z : V}
    (hy : color x ≠ color y) (hz : color x ≠ color z) : color y = color z := by
  cases hx : color x <;> cases hy' : color y <;> cases hz' : color z <;> simp_all

/-- A geodesic of length at least `i` supplies an endpoint at distance exactly `i`. -/
theorem exists_distance_of_le (hconn : G.Connected) {x y : V} {i : ℕ}
    (hi : i ≤ G.dist x y) : ∃ z, G.dist x z = i := by
  obtain ⟨p, _, hp⟩ := hconn.exists_path_of_dist x y
  have hgeo := length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  have hlen : (p.take i).length = i := by rw [Walk.take_length, hp, Nat.min_eq_left hi]
  exact ⟨p.getVert i, hgeo.symm.trans hlen⟩

private theorem short_geodesic_on_orbit
    (hact : GraphAction G A) (hconn : G.Connected) (hdeg : BasedWalk.HasTwoNeighbors G)
    (ht : ∀ v, RootPathTransitive G A v 9) (color : V → Bool)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    {x y : V} (hxy : G.dist x y = 8)
    {v : V} (hv : color v = color x) {i : ℕ} (hi : i ≤ 8)
    (p : BasedWalk G i v) (hp : p.Nonbacktracking) : G.dist v p.endpoint = i := by
  obtain ⟨z, hz⟩ := exists_distance_of_le hconn (x := x) (y := y) (i := i) (by omega)
  obtain ⟨a, ha⟩ := horbit hv.symm
  have hd : G.dist v (a • z) = i := by
    rw [← ha, hact.dist_smul, hz]
  obtain ⟨q, hq, he⟩ := BasedWalk.exists_geodesic (hconn v (a • z))
  let q' : BasedWalk G i v := hd ▸ q
  have hq' : q'.Nonbacktracking := (BasedWalk.nonbacktracking_cast hd q).mpr hq
  have hqe : G.dist v q'.endpoint = i := by
    simpa only [q', BasedWalk.endpoint_cast, he] using hd
  exact ((ht v).mono hdeg (by omega)).geodesic_of_exists hact ⟨q', hq', hqe⟩ p hp

private theorem cycle_bound_on_orbit
    (hact : GraphAction G A) (hconn : G.Connected) (hdeg : BasedWalk.HasTwoNeighbors G)
    (ht : ∀ v, RootPathTransitive G A v 9) (color : V → Bool)
    (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    {x y : V} (hxy : G.dist x y = 8)
    (v : V) (hv : color v = color x) (c : G.Walk v v) (hc : c.IsCycle) :
    16 ≤ c.length := by
  by_contra hn
  obtain ⟨k, hk⟩ := (even_length_iff color hcolor c).mpr rfl
  have hthree := hc.three_le_length
  have hk2 : 2 ≤ k := by omega
  have hk7 : k ≤ 7 := by omega
  have hpath := hc.isPath_take (n := k + 1) (by omega)
  have hlen : (c.take (k + 1)).length = k + 1 := by
    rw [Walk.take_length, Nat.min_eq_left (by omega)]
  let p : BasedWalk G (k + 1) v := hlen ▸ BasedWalk.ofWalk (c.take (k + 1))
  have hp : p.Nonbacktracking := (BasedWalk.nonbacktracking_cast hlen _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ hpath)
  have hgeo := short_geodesic_on_orbit hact hconn hdeg ht color horbit hxy hv (by omega) p hp
  have hend : p.endpoint = c.getVert (k + 1) := by
    simp only [p, BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk]
  rw [hend] at hgeo
  have hshort := SimpleGraph.dist_le (c.drop (k + 1)).reverse
  rw [Walk.length_reverse, Walk.drop_length] at hshort
  omega

/-- The distance-eight source witness already excludes every cycle shorter than sixteen. -/
theorem cycle_bound_of_distance_eight
    (hact : GraphAction G A) (hconn : G.Connected) (hdeg : BasedWalk.HasTwoNeighbors G)
    (ht : ∀ v, RootPathTransitive G A v 9) (color : V → Bool)
    (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    {x y : V} (hxy : G.dist x y = 8)
    (v : V) (c : G.Walk v v) (hc : c.IsCycle) : 16 ≤ c.length := by
  classical
  by_cases hv : color v = color x
  · exact cycle_bound_on_orbit hact hconn hdeg ht color hcolor horbit hxy v hv c hc
  · have hs : color c.snd = color x := color_eq_of_two_ne color
      (hcolor (c.adj_snd hc.not_nil)) hv
    have hm : c.snd ∈ c.support := c.getVert_mem_support 1
    have hh := cycle_bound_on_orbit hact hconn hdeg ht color hcolor horbit hxy c.snd hs
      (c.rotate c.snd hm) (hc.rotate hm)
    simpa only [Walk.length_rotate] using hh

/-- Nonuniqueness of the source eight-geodesic produces an actual sixteen-cycle. -/
theorem exists_cycle_sixteen_of_distinct_geodesics
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    {x y : V} (hxy : G.dist x y = 8)
    (p q : G.Walk x y) (hp : p.length = 8) (hq : q.length = 8) (hpq : p ≠ q) :
    ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 16 := by
  obtain ⟨v, _, _, c, hc, hl⟩ :=
    (p.isPath_of_length_eq_dist (hp.trans hxy.symm)).exists_isCycle_length_le_add_of_ne
      (q.isPath_of_length_eq_dist (hq.trans hxy.symm)) hpq
  exact ⟨v, c, hc, by have hh := hg v c hc; omega⟩

private theorem nine_prefix_of_cycle {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (hlen : c.length = 16) :
    ∃ p : BasedWalk G 9 v, p.Nonbacktracking ∧ G.dist v p.endpoint ≤ 7 := by
  have hl : (c.take 9).length = 9 := by rw [Walk.take_length, hlen]; rfl
  let p : BasedWalk G 9 v := hl ▸ BasedWalk.ofWalk (c.take 9)
  refine ⟨p, (BasedWalk.nonbacktracking_cast hl _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hc.isPath_take (by omega))), ?_⟩
  have hd := SimpleGraph.dist_le (c.drop 9).reverse
  rw [Walk.length_reverse, Walk.drop_length, hlen] at hd
  simpa only [p, BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk] using hd

/-- An actual sixteen-cycle supplies a short-ended nine-walk at every vertex of both orbits. -/
theorem exists_short_nine_walk
    (hact : GraphAction G A) (color : V → Bool)
    (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    (hex : ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 16) (u : V) :
    ∃ p : BasedWalk G 9 u, p.Nonbacktracking ∧ G.dist u p.endpoint ≤ 7 := by
  classical
  obtain ⟨v, c, hc, hl⟩ := hex
  have hsame : ∃ w, color w = color u ∧
      ∃ d : G.Walk w w, d.IsCycle ∧ d.length = 16 := by
    by_cases hv : color v = color u
    · exact ⟨v, hv, c, hc, hl⟩
    · have hs : color c.snd = color u := color_eq_of_two_ne color
        (hcolor (c.adj_snd hc.not_nil)) hv
      have hm : c.snd ∈ c.support := c.getVert_mem_support 1
      exact ⟨c.snd, hs, c.rotate c.snd hm, hc.rotate hm, by simpa using hl⟩
  obtain ⟨w, hw, d, hd, hdl⟩ := hsame
  obtain ⟨p, hp, hpdist⟩ := nine_prefix_of_cycle d hd hdl
  obtain ⟨a, rfl⟩ := horbit hw
  refine ⟨p.map (hact.hom a), (hact.nonbacktracking_map_iff a p).mpr hp, ?_⟩
  have he : (p.map (hact.hom a)).endpoint = a • p.endpoint :=
    BasedWalk.endpoint_map (hact.hom a) p
  exact (congrArg (G.dist (a • w)) he).le.trans
    ((hact.dist_smul a w p.endpoint).le.trans hpdist)

/-- Nine-path transitivity transfers the complementary seven-arc bound to every nine-walk. -/
theorem nine_endpoint_bound
    (hact : GraphAction G A) (ht : ∀ v, RootPathTransitive G A v 9)
    (color : V → Bool) (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    (hex : ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 16)
    {v : V} (p : BasedWalk G 9 v) (hp : p.Nonbacktracking) : G.dist v p.endpoint ≤ 7 := by
  obtain ⟨q, hq, hqd⟩ := exists_short_nine_walk hact color hcolor horbit hex v
  exact ((ht v).distance_eq hact p q hp hq).le.trans hqd

/-- A geodesic cannot have a nine-edge prefix once every such nonbacktracking walk has a shortcut. -/
theorem diameter_bound_of_nine_endpoint_bound (hconn : G.Connected)
    (hshort : ∀ v (p : BasedWalk G 9 v), p.Nonbacktracking → G.dist v p.endpoint ≤ 7)
    (v w : V) : G.dist v w ≤ 8 := by
  by_contra hn
  obtain ⟨p, hp, hl⟩ := hconn.exists_path_of_dist v w
  have hlen : (p.take 9).length = 9 := by
    rw [Walk.take_length, hl, Nat.min_eq_left (by omega)]
  let q : BasedWalk G 9 v := hlen ▸ BasedWalk.ofWalk (p.take 9)
  have hq : q.Nonbacktracking := (BasedWalk.nonbacktracking_cast hlen _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hp.take 9))
  have hd := hshort v q hq
  have hgeo := length_eq_dist_of_subwalk hl (p.isSubwalk_take 9)
  have hqend : q.endpoint = p.getVert 9 := by
    simp only [q, BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk]
  rw [hqend, ← hgeo, hlen] at hd
  omega

/-- Full source octagon geometry from the original distinct eight-geodesics. -/
theorem octagon_of_small
    (hact : GraphAction G A) (hconn : G.Connected) (hdeg : BasedWalk.HasTwoNeighbors G)
    (ht : ∀ v, RootPathTransitive G A v 9) (color : V → Bool)
    (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    (hsmall : ∃ x y, G.dist x y = 8 ∧
      ∃ p q : G.Walk x y, p.length = 8 ∧ q.length = 8 ∧ p ≠ q) :
    (∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length) ∧
      (∀ v w, G.dist v w ≤ 8) ∧
      (∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 16) := by
  obtain ⟨x, y, hxy, p, q, hp, hq, hpq⟩ := hsmall
  have hg := cycle_bound_of_distance_eight hact hconn hdeg ht color hcolor horbit hxy
  have hex := exists_cycle_sixteen_of_distinct_geodesics hg hxy p q hp hq hpq
  refine ⟨hg, diameter_bound_of_nine_endpoint_bound hconn ?_, hex⟩
  intro v r hr
  exact nine_endpoint_bound hact ht color hcolor horbit hex r hr

end SimpleGraph.PathTransitivePolygon.OctagonRecognition
