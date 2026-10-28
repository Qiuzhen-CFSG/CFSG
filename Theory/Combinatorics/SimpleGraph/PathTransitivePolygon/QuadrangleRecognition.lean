module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Quadrangle metric recognition from rooted five-path transitivity

A distance-four witness makes all short paths on its vertex orbit geodesic.
Rotating cycles to that orbit excludes cycles shorter than eight. Two distinct
four-geodesics then supply an eight-cycle; its complementary three-arc gives
the endpoint bound for every five-walk, hence diameter at most four.

Source: Aschbacher–Smith F.3.5 and F.4.4, printed pp.271 and278.
-/

public noncomputable section
namespace SimpleGraph.PathTransitivePolygon.QuadrangleRecognition
open SimpleGraph
variable {V A : Type*} {G : SimpleGraph V} [Group A] [MulAction A V]

theorem even_length_iff (color : V → Bool)
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

theorem short_geodesic_on_orbit
    (hact : GraphAction G A) (hconn : G.Connected) (hdeg : BasedWalk.HasTwoNeighbors G)
    (ht : ∀ v, RootPathTransitive G A v 5) (color : V → Bool)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    {x y : V} (hxy : G.dist x y = 4)
    {v : V} (hv : color v = color x) {i : ℕ} (hi : i ≤ 4)
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
    (ht : ∀ v, RootPathTransitive G A v 5) (color : V → Bool)
    (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    {x y : V} (hxy : G.dist x y = 4)
    (v : V) (hv : color v = color x) (c : G.Walk v v) (hc : c.IsCycle) :
    8 ≤ c.length := by
  by_contra hn
  obtain ⟨k, hk⟩ := (even_length_iff color hcolor c).mpr rfl
  have hthree := hc.three_le_length
  have hk2 : 2 ≤ k := by omega
  have hk7 : k ≤ 3 := by omega
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

/-- The distance-four source witness already excludes every cycle shorter than eight. -/
theorem cycle_bound_of_distance_four
    (hact : GraphAction G A) (hconn : G.Connected) (hdeg : BasedWalk.HasTwoNeighbors G)
    (ht : ∀ v, RootPathTransitive G A v 5) (color : V → Bool)
    (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    {x y : V} (hxy : G.dist x y = 4)
    (v : V) (c : G.Walk v v) (hc : c.IsCycle) : 8 ≤ c.length := by
  classical
  by_cases hv : color v = color x
  · exact cycle_bound_on_orbit hact hconn hdeg ht color hcolor horbit hxy v hv c hc
  · have hs : color c.snd = color x := color_eq_of_two_ne color
      (hcolor (c.adj_snd hc.not_nil)) hv
    have hm : c.snd ∈ c.support := c.getVert_mem_support 1
    have hh := cycle_bound_on_orbit hact hconn hdeg ht color hcolor horbit hxy c.snd hs
      (c.rotate c.snd hm) (hc.rotate hm)
    simpa only [Walk.length_rotate] using hh

/-- Nonuniqueness of the source four-geodesic produces an actual eight-cycle. -/
theorem exists_cycle_eight_of_distinct_geodesics
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 8 ≤ c.length)
    {x y : V} (hxy : G.dist x y = 4)
    (p q : G.Walk x y) (hp : p.length = 4) (hq : q.length = 4) (hpq : p ≠ q) :
    ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 8 := by
  obtain ⟨v, _, _, c, hc, hl⟩ :=
    (p.isPath_of_length_eq_dist (hp.trans hxy.symm)).exists_isCycle_length_le_add_of_ne
      (q.isPath_of_length_eq_dist (hq.trans hxy.symm)) hpq
  exact ⟨v, c, hc, by have hh := hg v c hc; omega⟩

private theorem five_prefix_of_cycle {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (hlen : c.length = 8) :
    ∃ p : BasedWalk G 5 v, p.Nonbacktracking ∧ G.dist v p.endpoint ≤ 3 := by
  have hl : (c.take 5).length = 5 := by rw [Walk.take_length, hlen]; rfl
  let p : BasedWalk G 5 v := hl ▸ BasedWalk.ofWalk (c.take 5)
  refine ⟨p, (BasedWalk.nonbacktracking_cast hl _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hc.isPath_take (by omega))), ?_⟩
  have hd := SimpleGraph.dist_le (c.drop 5).reverse
  rw [Walk.length_reverse, Walk.drop_length, hlen] at hd
  simpa only [p, BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk] using hd

/-- An actual eight-cycle supplies a short-ended five-walk at every vertex of both orbits. -/
theorem exists_short_five_walk
    (hact : GraphAction G A) (color : V → Bool)
    (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    (hex : ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 8) (u : V) :
    ∃ p : BasedWalk G 5 u, p.Nonbacktracking ∧ G.dist u p.endpoint ≤ 3 := by
  classical
  obtain ⟨v, c, hc, hl⟩ := hex
  have hsame : ∃ w, color w = color u ∧
      ∃ d : G.Walk w w, d.IsCycle ∧ d.length = 8 := by
    by_cases hv : color v = color u
    · exact ⟨v, hv, c, hc, hl⟩
    · have hs : color c.snd = color u := color_eq_of_two_ne color
        (hcolor (c.adj_snd hc.not_nil)) hv
      have hm : c.snd ∈ c.support := c.getVert_mem_support 1
      exact ⟨c.snd, hs, c.rotate c.snd hm, hc.rotate hm, by simpa using hl⟩
  obtain ⟨w, hw, d, hd, hdl⟩ := hsame
  obtain ⟨p, hp, hpdist⟩ := five_prefix_of_cycle d hd hdl
  obtain ⟨a, rfl⟩ := horbit hw
  refine ⟨p.map (hact.hom a), (hact.nonbacktracking_map_iff a p).mpr hp, ?_⟩
  have he : (p.map (hact.hom a)).endpoint = a • p.endpoint :=
    BasedWalk.endpoint_map (hact.hom a) p
  exact (congrArg (G.dist (a • w)) he).le.trans
    ((hact.dist_smul a w p.endpoint).le.trans hpdist)

/-- Nine-path transitivity transfers the complementary three-arc bound to every five-walk. -/
theorem five_endpoint_bound
    (hact : GraphAction G A) (ht : ∀ v, RootPathTransitive G A v 5)
    (color : V → Bool) (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    (hex : ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 8)
    {v : V} (p : BasedWalk G 5 v) (hp : p.Nonbacktracking) : G.dist v p.endpoint ≤ 3 := by
  obtain ⟨q, hq, hqd⟩ := exists_short_five_walk hact color hcolor horbit hex v
  exact ((ht v).distance_eq hact p q hp hq).le.trans hqd

/-- A geodesic cannot have a five-edge prefix once every such nonbacktracking walk has a shortcut. -/
theorem diameter_bound_of_five_endpoint_bound (hconn : G.Connected)
    (hshort : ∀ v (p : BasedWalk G 5 v), p.Nonbacktracking → G.dist v p.endpoint ≤ 3)
    (v w : V) : G.dist v w ≤ 4 := by
  by_contra hn
  obtain ⟨p, hp, hl⟩ := hconn.exists_path_of_dist v w
  have hlen : (p.take 5).length = 5 := by
    rw [Walk.take_length, hl, Nat.min_eq_left (by omega)]
  let q : BasedWalk G 5 v := hlen ▸ BasedWalk.ofWalk (p.take 5)
  have hq : q.Nonbacktracking := (BasedWalk.nonbacktracking_cast hlen _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hp.take 5))
  have hd := hshort v q hq
  have hgeo := length_eq_dist_of_subwalk hl (p.isSubwalk_take 5)
  have hqend : q.endpoint = p.getVert 5 := by
    simp only [q, BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk]
  rw [hqend, ← hgeo, hlen] at hd
  omega

/-- Full source quadrangle geometry from the original distinct four-geodesics. -/
theorem quadrangle_of_small
    (hact : GraphAction G A) (hconn : G.Connected) (hdeg : BasedWalk.HasTwoNeighbors G)
    (ht : ∀ v, RootPathTransitive G A v 5) (color : V → Bool)
    (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    (hsmall : ∃ x y, G.dist x y = 4 ∧
      ∃ p q : G.Walk x y, p.length = 4 ∧ q.length = 4 ∧ p ≠ q) :
    (∀ v (c : G.Walk v v), c.IsCycle → 8 ≤ c.length) ∧
      (∀ v w, G.dist v w ≤ 4) ∧
      (∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 8) := by
  obtain ⟨x, y, hxy, p, q, hp, hq, hpq⟩ := hsmall
  have hg := cycle_bound_of_distance_four hact hconn hdeg ht color hcolor horbit hxy
  have hex := exists_cycle_eight_of_distinct_geodesics hg hxy p q hp hq hpq
  refine ⟨hg, diameter_bound_of_five_endpoint_bound hconn ?_, hex⟩
  intro v r hr
  exact five_endpoint_bound hact ht color hcolor horbit hex r hr

/-- More vertices in one color class than the origin and all two-walks
force an actual distance-four witness. No diameter bound is assumed. -/
theorem exists_distance_four_of_card (hconn : G.Connected)
    (color : V → Bool) (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (x : V) [Finite {p : BasedWalk G 2 x // p.Nonbacktracking}]
    (hc : 1 + Nat.card {p : BasedWalk G 2 x // p.Nonbacktracking} <
      Nat.card {y : V // color y = color x}) :
    ∃ y, G.dist x y = 4 := by
  classical
  by_contra hno
  have hdist (y : V) : G.dist x y < 4 := by
    by_contra h
    exact hno (exists_distance_of_le hconn (x := x) (y := y) (i := 4) (by omega))
  let f : Option {p : BasedWalk G 2 x // p.Nonbacktracking} →
      {y : V // color y = color x} := fun p => match p with
    | none => ⟨x,rfl⟩
    | some p => ⟨p.val.endpoint, ((even_length_iff color hcolor p.val.toWalk).mp
        (by simp only [BasedWalk.length_toWalk]; decide)).symm⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨p,hp,hlen⟩ := hconn.exists_path_of_dist x y.val
    have heven : Even (G.dist x y.val) := by
      rw [← hlen]
      exact (even_length_iff color hcolor p).mpr y.property.symm
    obtain ⟨k,hk⟩ := heven
    have hcases : G.dist x y.val = 0 ∨ G.dist x y.val = 2 := by
      have := hdist y.val
      omega
    rcases hcases with hz | ht
    · refine ⟨none,Subtype.ext ?_⟩
      exact hconn.dist_eq_zero_iff.mp hz
    · have hl : p.length = 2 := hlen.trans ht
      let q : BasedWalk G 2 x := hl ▸ BasedWalk.ofWalk p
      refine ⟨some ⟨q,?_⟩,Subtype.ext ?_⟩
      · exact (BasedWalk.nonbacktracking_cast hl _).mpr
          (BasedWalk.nonbacktracking_ofWalk_of_isPath p hp)
      · change q.endpoint = y.val
        simp only [q,BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]
  have hh := Nat.card_le_card_of_surjective f hf
  have hopt : Nat.card (Option {p : BasedWalk G 2 x // p.Nonbacktracking}) =
      Nat.card {p : BasedWalk G 2 x // p.Nonbacktracking} + 1 := by
    let := Fintype.ofFinite {p : BasedWalk G 2 x // p.Nonbacktracking}
    simp only [Nat.card_eq_fintype_card,Fintype.card_option]
  rw [hopt] at hh
  omega

/-- A four-walk census larger than the whole vertex set forces the source
nonuniqueness of opposite four-geodesics. -/
theorem small_of_four_path_card [Finite V]
    {x : V} (hgeo : ∀ p : BasedWalk G 4 x, p.Nonbacktracking → G.dist x p.endpoint = 4)
    (hc : Nat.card V < Nat.card {p : BasedWalk G 4 x // p.Nonbacktracking}) :
    ∃ y, G.dist x y = 4 ∧ ∃ p q : G.Walk x y,
      p.length = 4 ∧ q.length = 4 ∧ p ≠ q := by
  classical
  have hn : ¬ Function.Injective (fun p : {p : BasedWalk G 4 x // p.Nonbacktracking} =>
      p.val.endpoint) := by
    intro hi
    have hh := Nat.card_le_card_of_injective _ hi
    omega
  obtain ⟨p,q,he,hne⟩ := Function.not_injective_iff.mp hn
  refine ⟨p.val.endpoint,hgeo p.val p.property,p.val.toWalk,
    q.val.toWalk.copy rfl he.symm,BasedWalk.length_toWalk _,?_,?_⟩
  · simp only [Walk.length_copy,BasedWalk.length_toWalk]
  · intro hh
    apply hne
    apply Subtype.ext
    apply BasedWalk.vertices_injective 4 x
    have hs := congrArg Walk.support hh
    simpa only [Walk.support_copy,BasedWalk.support_toWalk] using hs

end SimpleGraph.PathTransitivePolygon.QuadrangleRecognition
