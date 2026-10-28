module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.ShortPaths
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.HexagonRecognition
public import Theory.GroupAction.DihedralPolygon

/-!
# The hexagon relation forces small triality completion geometry

Two endpoint involutions outside the whole Borel, whose product has sixth
power one, give a twelve-cycle. Seven-path transitivity propagates its short
complementary arcs and bounds the diameter by six. This is the specialized
smallness argument of Aschbacher--Smith F.3.6 and F.4.8, pp.272,278.

The Weyl relation remains an explicit premise here. Its derivation from the
original ambient centralizer hypotheses belongs to qt-e-14315-eight-borel-exclusion.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open HexagonRecognition
variable {G : Type*} [Group G] (c : Completion G)
theorem uniqueGeodesicsBelow_six : c.graph.UniqueGeodesicsBelow 6 := by
  intro x y p q hp hq hd
  by_contra hh
  obtain ⟨v,_,_,r,hr,hlen⟩ := (p.isPath_of_length_eq_dist hp).exists_isCycle_length_le_add_of_ne
    (q.isPath_of_length_eq_dist hq) hh
  have hb := c.cycle_length_ge_twelve v r hr
  omega

def bipartiteAction : GroupAction.DihedralPolygon.BipartiteAction G c.graph where
  color := (·.type)
  adjacent_color h := h.1
  smul_adj := c.graphAction.map_adj
  smul_color _ _ := rfl

theorem exists_twelve_cycle_of_involutions (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^6=1) :
    ∃v,∃p : c.graph.Walk v v,p.IsCycle ∧ p.length=12 := by
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
  let e : cycleGraph 12 ↪g c.graph := GroupAction.DihedralPolygon.edgeEmbedding c.bipartiteAction
    (by decide : 1<6) c.uniqueGeodesicsBelow_six (by decide : 0<6) le_rfl
    ⟨Bool.false_ne_true,incident_base c.family false true⟩ hs2 ht2 hsx hsl htl htx
    (by rw [hst,one_smul]) (by rw [hst,one_smul])
  exact (cycleGraph_isContained_iff (by decide : 2<12)).mp ⟨e.toCopy⟩

theorem hexagon_metric_of_involutions (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^6=1) :
    (∀v (p : c.graph.Walk v v),p.IsCycle → 12≤p.length) ∧
    (∀v w,c.graph.dist v w≤6) ∧
    (∃v,∃p : c.graph.Walk v v,p.IsCycle ∧ p.length=12) := by
  have hex := c.exists_twelve_cycle_of_involutions s t hs ht hsout htout hs2 ht2 hst
  refine ⟨c.cycle_length_ge_twelve,diameter_bound_of_seven_endpoint_bound c.connected ?_,hex⟩
  intro v p hp
  exact seven_endpoint_bound c.graphAction c.seven_transitive (·.type) (fun h => h.1)
    (fun h => (same_orbit_iff c.family _ _).mpr h) hex p hp

/-- The literal order-six input of F.4.26 forces the complete hexagon metric. -/
theorem hexagon_metric_of_orders (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : orderOf s=2) (ht2 : orderOf t=2) (hst : orderOf (s*t)=6) :
    (∀v (p : c.graph.Walk v v),p.IsCycle → 12≤p.length) ∧
    (∀v w,c.graph.dist v w≤6) ∧
    (∃v,∃p : c.graph.Walk v v,p.IsCycle ∧ p.length=12) :=
  c.hexagon_metric_of_involutions s t hs ht hsout htout
    (hs2 ▸ pow_orderOf_eq_one s) (ht2 ▸ pow_orderOf_eq_one t)
    (hst ▸ pow_orderOf_eq_one (s*t))
end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
