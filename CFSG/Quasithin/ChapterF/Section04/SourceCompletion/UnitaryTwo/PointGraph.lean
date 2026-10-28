module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.Lines
public import Theory.Combinatorics.SimpleGraph.QuadrangleCollinearity.Counts
public import Theory.Combinatorics.SimpleGraph.QuadrangleTwentySeven.Source

/-!
# Native recognition of the 27-point unitary completion graph

The original faithful completion of order25920 supplies its own quadrangle
metric, two-path census and valencies. Consequently its plane-coset collinearity
graph has the strongly regular parameters(27,10,1,5). The checked uniqueness
theorem identifies this graph with the canonical27-vertex model and bounds its
automorphism group by51840. No geometric or representation premise is added.

Source: Aschbacher–Smith F.4.8 andF.4.24, printed pp.278 and287.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
open SimpleGraph SimpleGraph.QuadrangleCollinearity
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

instance pointFintype : Fintype c.Point := Fintype.ofFinite c.Point
instance pointGraphDecidable : DecidableRel c.pointGraph.Adj := Classical.decRel _

include c in
theorem pointGraph_isSRG (hcard : Nat.card G = 25920) :
    c.pointGraph.IsSRGWith 27 10 1 5 := by
  classical
  have hg := (c.quadrangle_metric hcard).1
  have hd := (c.quadrangle_metric hcard).2.1
  have hcolor : ∀ {u v : c.Vertex},c.graph.Adj u v → u.type ≠ v.type := fun h => h.1
  refine ⟨?_,?_,?_,?_⟩
  · exact (Nat.card_eq_fintype_card (α := c.Point)).symm.trans (c.card_point hcard)
  · intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    have he := Nat.card_congr (twoNeighborEquiv hg hcolor x)
    exact he.symm.trans (c.card_two_paths x)
  · intro x y hxy
    rw [← Nat.card_eq_fintype_card]
    exact card_adjacent_common hg hcolor (fun l hl => by
      rw [c.card_neighbors l,hl]; rfl) hxy
  · intro x y hxy hnot
    rw [← Nat.card_eq_fintype_card]
    have he := Nat.card_congr (nonadjacentCommonEquiv hg hcolor c.connected hd hxy hnot)
    exact he.trans (by rw [c.card_neighbors y.val,y.property]; rfl)

theorem pointGraph_recognition (hcard : Nat.card G = 25920) :
    Nonempty (Theory.Combinatorics.QuadrangleTwentySeven.canonical ≃g c.pointGraph) ∧
      Nat.card (c.pointGraph ≃g c.pointGraph) ≤ 51840 :=
  Theory.Combinatorics.QuadrangleTwentySeven.source_recognition c.pointGraph
    (c.pointGraph_isSRG hcard)
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
