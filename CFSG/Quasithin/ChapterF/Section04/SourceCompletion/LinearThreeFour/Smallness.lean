module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.Smallness.NativeFour
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth
public import Theory.GroupAction.DihedralPolygon

/-!
# The geometric smallness criterion for PSL₃(4) completions

The native four-edge path action transfers through the common amalgam cover.
Thickness then excludes cycles of length at most four, giving unique geodesics
below three. The two specified endpoint involutions construct an actual hexagon.
Its four-edge arcs have complementary two-edge shortcuts; four-path transitivity
and connectedness force diameter at most three.

Together with the whole-overlap and degree-five calculations, this proves the
four geometric premises consumed by the independent plane-action comparison.
The Borel retains its odd torus, and no ambient order, simplicity, or additional
generation premise is imposed. The proof also works for infinite ambient groups.

Source: Aschbacher–Smith F.3.6, F.4.6 and F.4.26, printed pp.272, 276–278, 288.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (c : Completion G)

theorem graphAction : GraphAction c.graph G where
  map_adj g := (translationGraphIso c.family g).toHom.map_adj

/-- Thickness in the literal graph, as required by path-extension arguments. -/
theorem thick (v a b : c.Vertex) : ∃ z, c.graph.Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hc : 2 < Nat.card (c.graph.neighborSet v) := by
    rw [card_neighbors c v]
    decide
  have : Finite (c.graph.neighborSet v) := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite (c.graph.neighborSet v)
  rw [Nat.card_eq_fintype_card] at hc
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hc
  by_contra hh
  push Not at hh
  have hx : x.val = a ∨ x.val = b := by
    by_cases ha : x.val = a
    · exact Or.inl ha
    · exact Or.inr (hh x.val x.property ha)
  have hy : y.val = a ∨ y.val = b := by
    by_cases ha : y.val = a
    · exact Or.inl ha
    · exact Or.inr (hh y.val y.property ha)
  have hz : z.val = a ∨ z.val = b := by
    by_cases ha : z.val = a
    · exact Or.inl ha
    · exact Or.inr (hh z.val z.property ha)
  have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val ≠ z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    rcases hz with hz | hz <;> simp_all


theorem hasTwoNeighbors : BasedWalk.HasTwoNeighbors c.graph := by
  intro v a
  obtain ⟨z,hz,hza,_⟩ := c.thick v a a
  exact ⟨z,hz,hza⟩

theorem four_transitive (v : c.Vertex) : RootPathTransitive c.graph G v 4 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.family v
  have hb := (c.rootPathTransitive_iff_model v.type 4).mpr (Native.four_path_transitive v.type)
  simpa only [hg] using RootPathTransitive.smul c.graphAction hb g

theorem cycle_length_gt_four (v : c.Vertex) (p : c.graph.Walk v v) (hp : p.IsCycle) :
    4 < p.length :=
  cycle_bound_of_root_transitivity c.graphAction c.thick c.four_transitive v p hp

theorem uniqueGeodesicsBelow_three : c.graph.UniqueGeodesicsBelow 3 := by
  intro x y p q hp hq hd
  by_contra hh
  obtain ⟨v,_,_,r,hr,hlen⟩ := (p.isPath_of_length_eq_dist hp).exists_isCycle_length_le_add_of_ne
    (q.isPath_of_length_eq_dist hq) hh
  have hb := c.cycle_length_gt_four v r hr
  omega

def bipartiteAction : GroupAction.DihedralPolygon.BipartiteAction G c.graph where
  color := (·.type)
  adjacent_color h := h.1
  smul_adj := c.graphAction.map_adj
  smul_color _ _ := rfl

theorem exists_six_cycle_of_involutions (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^3=1) :
    ∃v,∃p : c.graph.Walk v v,p.IsCycle ∧ p.length=6 := by
  have hsx : s • RankTwo.base c.family false=RankTwo.base c.family false := by
    change s∈stabilizer c.family (RankTwo.base c.family false)
    simpa only [stabilizer,RankTwo.base,stabilizer_base,family_false] using hs
  have htl : t • RankTwo.base c.family true=RankTwo.base c.family true := by
    change t∈stabilizer c.family (RankTwo.base c.family true)
    simpa only [stabilizer,RankTwo.base,stabilizer_base,family_true] using ht
  have hsl : s • RankTwo.base c.family true≠RankTwo.base c.family true := by
    intro hh
    have hh' : s∈c.right.range := by
      change s∈stabilizer c.family (RankTwo.base c.family true) at hh
      simpa only [stabilizer,RankTwo.base,stabilizer_base,family_true] using hh
    exact hsout (c.overlap ▸ show s∈c.left.range⊓c.right.range from ⟨hs,hh'⟩)
  have htx : t • RankTwo.base c.family false≠RankTwo.base c.family false := by
    intro hh
    have hh' : t∈c.left.range := by
      change t∈stabilizer c.family (RankTwo.base c.family false) at hh
      simpa only [stabilizer,RankTwo.base,stabilizer_base,family_false] using hh
    exact htout (c.overlap ▸ show t∈c.left.range⊓c.right.range from ⟨hh',ht⟩)
  let e : cycleGraph 6 ↪g c.graph := GroupAction.DihedralPolygon.edgeEmbedding c.bipartiteAction
    (by decide : 1<3) c.uniqueGeodesicsBelow_three (by decide : 0<3) le_rfl
    ⟨Bool.false_ne_true,incident_base c.family false true⟩ hs2 ht2 hsx hsl htl htx
    (by rw [hst,one_smul]) (by rw [hst,one_smul])
  exact (cycleGraph_isContained_iff (by decide : 2<6)).mp ⟨e.toCopy⟩

private theorem four_prefix_of_cycle {v : c.Vertex} (r : c.graph.Walk v v)
    (hr : r.IsCycle) (hlen : r.length = 6) :
    ∃ p : BasedWalk c.graph 4 v, p.Nonbacktracking ∧ c.graph.dist v p.endpoint ≤ 2 := by
  have hl : (r.take 4).length = 4 := by rw [Walk.take_length, hlen]; rfl
  let p : BasedWalk c.graph 4 v := hl ▸ BasedWalk.ofWalk (r.take 4)
  refine ⟨p, (BasedWalk.nonbacktracking_cast hl _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hr.isPath_take (by omega))), ?_⟩
  have hd := SimpleGraph.dist_le (r.drop 4).reverse
  rw [Walk.length_reverse, Walk.drop_length, hlen] at hd
  simpa only [p, BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk] using hd

private theorem short_four_walk
    (hex : ∃ v, ∃ r : c.graph.Walk v v, r.IsCycle ∧ r.length = 6) (u : c.Vertex) :
    ∃ p : BasedWalk c.graph 4 u, p.Nonbacktracking ∧ c.graph.dist u p.endpoint ≤ 2 := by
  classical
  obtain ⟨v,r,hr,hl⟩ := hex
  have hsame : ∃ w : c.Vertex, w.type = u.type ∧
      ∃ d : c.graph.Walk w w, d.IsCycle ∧ d.length = 6 := by
    by_cases hv : v.type = u.type
    · exact ⟨v,hv,r,hr,hl⟩
    · have hn := (r.adj_snd hr.not_nil).1
      have hs : r.snd.type = u.type := by
        cases h1 : v.type <;> cases h2 : r.snd.type <;> cases h3 : u.type <;> simp_all
      have hm : r.snd ∈ r.support := r.getVert_mem_support 1
      exact ⟨r.snd,hs,r.rotate r.snd hm,hr.rotate hm,by simpa using hl⟩
  obtain ⟨w,hw,d,hd,hdl⟩ := hsame
  obtain ⟨p,hp,hpd⟩ := four_prefix_of_cycle c d hd hdl
  obtain ⟨a,rfl⟩ := (same_orbit_iff c.family w u).mpr hw
  refine ⟨p.map (c.graphAction.hom a), (c.graphAction.nonbacktracking_map_iff a p).mpr hp, ?_⟩
  have he : (p.map (c.graphAction.hom a)).endpoint = a • p.endpoint :=
    BasedWalk.endpoint_map (c.graphAction.hom a) p
  exact (congrArg (c.graph.dist (a • w)) he).le.trans
    ((c.graphAction.dist_smul a w p.endpoint).le.trans hpd)

theorem diameter_le_three_of_six_cycle
    (hex : ∃ v, ∃ r : c.graph.Walk v v, r.IsCycle ∧ r.length = 6)
    (v w : c.Vertex) : c.graph.dist v w ≤ 3 := by
  have hshort (u : c.Vertex) (p : BasedWalk c.graph 4 u) (hp : p.Nonbacktracking) :
      c.graph.dist u p.endpoint ≤ 2 := by
    obtain ⟨q,hq,hqd⟩ := short_four_walk c hex u
    exact ((c.four_transitive u).distance_eq c.graphAction p q hp hq).le.trans hqd
  by_contra hn
  obtain ⟨p,hp,hl⟩ := c.connected.exists_path_of_dist v w
  have hlen : (p.take 4).length = 4 := by
    rw [Walk.take_length,hl,Nat.min_eq_left (by omega)]
  let q : BasedWalk c.graph 4 v := hlen ▸ BasedWalk.ofWalk (p.take 4)
  have hq : q.Nonbacktracking := (BasedWalk.nonbacktracking_cast hlen _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hp.take 4))
  have hd := hshort v q hq
  have hgeo := length_eq_dist_of_subwalk hl (p.isSubwalk_take 4)
  have hqend : q.endpoint = p.getVert 4 := by
    simp only [q,BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]
  rw [hqend,←hgeo,hlen] at hd
  omega

/-- The full geometric smallness conclusion under exactly the two marked
involution hypotheses, retaining the full Borel intersection. -/
theorem smallness_of_involutions (s t : G)
    (hs : s ∈ c.left.range) (ht : t ∈ c.right.range)
    (hsout : s ∉ c.middle.range) (htout : t ∉ c.middle.range)
    (hs2 : orderOf s = 2) (ht2 : orderOf t = 2) (hst : orderOf (s*t) = 3) :
    c.left.range ⊓ c.right.range = c.middle.range ∧
    c.graph.UniqueGeodesicsBelow 3 ∧
    (∀ v w, c.graph.dist v w ≤ 3) ∧
    (∀ v, Nat.card (c.graph.neighborSet v) = 5) := by
  have hex := c.exists_six_cycle_of_involutions s t hs ht hsout htout
    (hs2 ▸ pow_orderOf_eq_one s) (ht2 ▸ pow_orderOf_eq_one t)
    (hst ▸ pow_orderOf_eq_one (s*t))
  exact ⟨c.overlap,c.uniqueGeodesicsBelow_three,c.diameter_le_three_of_six_cycle hex,
    c.card_neighbors⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
