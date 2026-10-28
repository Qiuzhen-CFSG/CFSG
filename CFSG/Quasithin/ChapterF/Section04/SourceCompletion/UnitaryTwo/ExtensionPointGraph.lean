module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ExtensionQuadrangle
public import Theory.Combinatorics.SimpleGraph.QuadrangleCollinearity.Counts
public import Theory.Combinatorics.SimpleGraph.QuadrangleTwentySeven.Source
/-!
# The actual 27-point graph of a doubled unitary completion

The quadrangle metric gives degree ten and common-neighbor counts one and
five on the original plane cosets. The strongly regular parameter identity
then forces twenty-seven points, hence completion order 51840. The checked
graph recognition applies to this literal action. The final theorem applies
the order-four involution criterion, supplying the geometric input to the
marked group comparison in Aschbacher--Smith F.4.26, printed p.288.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Extension.Completion
open SimpleGraph SimpleGraph.QuadrangleCollinearity
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

instance pointFintype : Fintype c.Point := Fintype.ofFinite c.Point
instance pointGraphDecidable : DecidableRel c.pointGraph.Adj := Classical.decRel _

theorem pointGraph_isSRG_of_diameter (hd : ∀v w,c.graph.dist v w≤4) :
    c.pointGraph.IsSRGWith 27 10 1 5 := by
  classical
  have hg := c.cycle_length_ge_eight
  have hcolor : ∀ {u v : c.Vertex},c.graph.Adj u v → u.type≠v.type := fun h => h.1
  have h : c.pointGraph.IsSRGWith (Nat.card c.Point) 10 1 5 := by
    refine ⟨?_,?_,?_,?_⟩
    · exact (Nat.card_eq_fintype_card (α := c.Point)).symm
    · intro x
      rw [← SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
      have he := Nat.card_congr (twoNeighborEquiv hg hcolor x)
      exact he.symm.trans (c.card_two_paths x)
    · intro x y hxy
      rw [←Nat.card_eq_fintype_card]
      exact card_adjacent_common hg hcolor (fun l hl => by
        rw [c.card_neighbors l,hl]; rfl) hxy
    · intro x y hxy hnot
      rw [←Nat.card_eq_fintype_card]
      have he := Nat.card_congr (nonadjacentCommonEquiv hg hcolor c.connected hd hxy hnot)
      exact he.trans (by rw [c.card_neighbors y.val,y.property]; rfl)
  have hpos : 0<Nat.card c.Point := lt_of_lt_of_le (by decide : 0<12) c.twelve_le_card_point
  have hp := h.param_eq c.pointGraph hpos
  have hn : Nat.card c.Point=27 := by omega
  exact hn ▸ h

theorem card_eq_of_diameter (hd : ∀v w,c.graph.dist v w≤4) : Nat.card G=51840 := by
  have hp : Nat.card c.Point=27 := by
    rw [Nat.card_eq_fintype_card]
    exact (c.pointGraph_isSRG_of_diameter hd).card
  have hpoint : Nat.card c.Point=c.right.range.index := by
    rw [Nat.card_congr (c.fiberEquiv true),←Subgroup.index_eq_card]
    rfl
  have hc := c.right.range.card_mul_index
  rw [c.right_card,←hpoint,hp] at hc
  omega

theorem pointGraph_recognition_of_diameter (hd : ∀v w,c.graph.dist v w≤4) :
    Nonempty (Theory.Combinatorics.QuadrangleTwentySeven.canonical ≃g c.pointGraph) ∧
      Nat.card (c.pointGraph ≃g c.pointGraph)≤51840 :=
  Theory.Combinatorics.QuadrangleTwentySeven.source_recognition c.pointGraph
    (c.pointGraph_isSRG_of_diameter hd)

theorem pointGraph_of_involutions (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^4=1) :
    c.pointGraph.IsSRGWith 27 10 1 5 ∧ Nat.card G=51840 := by
  have hd := (c.quadrangle_metric_of_involutions s t hs ht hsout htout hs2 ht2 hst).2.1
  exact ⟨c.pointGraph_isSRG_of_diameter hd,c.card_eq_of_diameter hd⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Extension.Completion
