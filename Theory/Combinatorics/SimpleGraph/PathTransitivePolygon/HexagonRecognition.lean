module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth

/-!
# Hexagon metrics from seven-path transitivity and a twelve-cycle

The seven-edge prefix of a twelve-cycle has a complementary five-edge arc.
The two vertex orbits and rooted path transitivity transfer this distance
bound to every seven-walk. Thus no geodesic can have length greater than six.
No uniqueness of the hexagon or its automorphism group is asserted.

Source: Aschbacher–Smith F.3.5 and F.4.8, printed pp.271 and 278.
-/




@[expose] public noncomputable section
namespace SimpleGraph.PathTransitivePolygon.HexagonRecognition
open SimpleGraph
variable {V A : Type*} {G : SimpleGraph V} [Group A] [MulAction A V]

private theorem color_eq_of_two_ne (color : V → Bool) {x y z : V}
    (hy : color x ≠ color y) (hz : color x ≠ color z) : color y = color z := by
  cases hx : color x <;> cases hy' : color y <;> cases hz' : color z <;> simp_all

private theorem seven_prefix_of_cycle {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (hlen : c.length = 12) :
    ∃ p : BasedWalk G 7 v, p.Nonbacktracking ∧ G.dist v p.endpoint ≤ 5 := by
  have hl : (c.take 7).length = 7 := by rw [Walk.take_length, hlen]; rfl
  let p : BasedWalk G 7 v := hl ▸ BasedWalk.ofWalk (c.take 7)
  refine ⟨p, (BasedWalk.nonbacktracking_cast hl _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hc.isPath_take (by omega))), ?_⟩
  have hd := SimpleGraph.dist_le (c.drop 7).reverse
  rw [Walk.length_reverse, Walk.drop_length, hlen] at hd
  simpa only [p, BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk] using hd

/-- An actual twelve-cycle supplies a short-ended seven-walk at every vertex of both orbits. -/
theorem exists_short_seven_walk
    (hact : GraphAction G A) (color : V → Bool)
    (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    (hex : ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 12) (u : V) :
    ∃ p : BasedWalk G 7 u, p.Nonbacktracking ∧ G.dist u p.endpoint ≤ 5 := by
  classical
  obtain ⟨v, c, hc, hl⟩ := hex
  have hsame : ∃ w, color w = color u ∧
      ∃ d : G.Walk w w, d.IsCycle ∧ d.length = 12 := by
    by_cases hv : color v = color u
    · exact ⟨v, hv, c, hc, hl⟩
    · have hs : color c.snd = color u := color_eq_of_two_ne color
        (hcolor (c.adj_snd hc.not_nil)) hv
      have hm : c.snd ∈ c.support := c.getVert_mem_support 1
      exact ⟨c.snd, hs, c.rotate c.snd hm, hc.rotate hm, by simpa using hl⟩
  obtain ⟨w, hw, d, hd, hdl⟩ := hsame
  obtain ⟨p, hp, hpdist⟩ := seven_prefix_of_cycle d hd hdl
  obtain ⟨a, rfl⟩ := horbit hw
  refine ⟨p.map (hact.hom a), (hact.nonbacktracking_map_iff a p).mpr hp, ?_⟩
  have he : (p.map (hact.hom a)).endpoint = a • p.endpoint :=
    BasedWalk.endpoint_map (hact.hom a) p
  exact (congrArg (G.dist (a • w)) he).le.trans
    ((hact.dist_smul a w p.endpoint).le.trans hpdist)

/-- Seven-path transitivity transfers the complementary five-arc bound to every seven-walk. -/
theorem seven_endpoint_bound
    (hact : GraphAction G A) (ht : ∀ v, RootPathTransitive G A v 7)
    (color : V → Bool) (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (horbit : ∀ {v w}, color v = color w → ∃ a : A, a • v = w)
    (hex : ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 12)
    {v : V} (p : BasedWalk G 7 v) (hp : p.Nonbacktracking) : G.dist v p.endpoint ≤ 5 := by
  obtain ⟨q, hq, hqd⟩ := exists_short_seven_walk hact color hcolor horbit hex v
  exact ((ht v).distance_eq hact p q hp hq).le.trans hqd

/-- A geodesic cannot have a seven-edge prefix once every such nonbacktracking walk has a shortcut. -/
theorem diameter_bound_of_seven_endpoint_bound (hconn : G.Connected)
    (hshort : ∀ v (p : BasedWalk G 7 v), p.Nonbacktracking → G.dist v p.endpoint ≤ 5)
    (v w : V) : G.dist v w ≤ 6 := by
  by_contra hn
  obtain ⟨p, hp, hl⟩ := hconn.exists_path_of_dist v w
  have hlen : (p.take 7).length = 7 := by
    rw [Walk.take_length, hl, Nat.min_eq_left (by omega)]
  let q : BasedWalk G 7 v := hlen ▸ BasedWalk.ofWalk (p.take 7)
  have hq : q.Nonbacktracking := (BasedWalk.nonbacktracking_cast hlen _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hp.take 7))
  have hd := hshort v q hq
  have hgeo := length_eq_dist_of_subwalk hl (p.isSubwalk_take 7)
  have hqend : q.endpoint = p.getVert 7 := by
    simp only [q, BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk]
  rw [hqend, ← hgeo, hlen] at hd
  omega

end SimpleGraph.PathTransitivePolygon.HexagonRecognition
