module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.NativeFive
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Native short paths and the binary unitary coset census

The genuine five-path action transfers from the matrix model through the common
amalgam cover. It supplies short-cycle exclusion at every source vertex. Under
order 25920 the actual vertex classes have sizes 45 and27, and the numbers of
rooted two- and four-walks from a plane coset are10 and80. The point graph is
collinearity on the original plane cosets, retaining the ambient group action.

Source: Aschbacher–Smith F.4.6 andF.4.24, printed pp.276 and287.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (c : Completion G)

/-- Thickness in the literal graph, as required by path-extension arguments. -/
theorem thick (v a b : c.Vertex) : ∃ z, c.graph.Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hc : 2 < Nat.card (c.graph.neighborSet v) := by
    rw [card_neighbors c v]
    cases v.type <;> decide
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

theorem five_transitive (v : c.Vertex) : RootPathTransitive c.graph G v 5 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.family v
  have hnative := NativeFive.five_path_transitive v.type
  have hc : RootPathTransitive NativeFive.completion.graph NativeFive.MG
      (RankTwo.base NativeFive.completion.family v.type) 5 := by
    change RootPathTransitive (RankTwo.graph NativeFive.completion.family) _ _ _
    rw [NativeFive.completion_family]
    exact hnative
  have hm := (rootPathTransitive_iff_model NativeFive.completion v.type 5).mp hc
  have hb := (rootPathTransitive_iff_model c v.type 5).mpr hm
  simpa only [hg] using RootPathTransitive.smul c.graphAction hb g

theorem cycle_length_gt_five (v : c.Vertex) (p : c.graph.Walk v v) (hp : p.IsCycle) :
    5 < p.length :=
  cycle_bound_of_root_transitivity c.graphAction c.thick c.five_transitive v p hp

instance finiteVertex [Finite G] : Finite c.Vertex :=
  Finite.of_equiv ((G ⧸ c.family false) ⊕ (G ⧸ c.family true))
    (RankTwo.vertexEquivSum c.family).symm

/-- The actual type-true cosets are the 27 points of the small quadrangle. -/
abbrev Point := {v : c.Vertex // v.type = true}

instance pointMulAction : MulAction G c.Point where
  smul g x := ⟨g • x.val,x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

@[simp] theorem point_smul_val (g : G) (x : c.Point) :
    (g • x).val = g • x.val := rfl

/-- Two plane cosets are collinear when they share a point-parabolic coset. -/
def pointGraph : SimpleGraph c.Point where
  Adj x y := x ≠ y ∧ ∃ l : c.Vertex, c.graph.Adj x.val l ∧ c.graph.Adj y.val l
  symm := ⟨by rintro x y ⟨hne,l,hx,hy⟩; exact ⟨hne.symm,l,hy,hx⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

theorem pointGraphAction : GraphAction c.pointGraph G where
  map_adj g := by
    rintro x y ⟨hne,l,hx,hy⟩
    exact ⟨fun h => hne ((MulAction.injective g) h),g • l,
      c.graphAction.map_adj g hx,c.graphAction.map_adj g hy⟩

def fiberEquiv (i : Bool) : {v : c.Vertex // v.type = i} ≃ (G ⧸ c.family i) where
  toFun v := v.property ▸ v.val.coset
  invFun q := ⟨⟨i,q⟩,rfl⟩
  left_inv v := by rcases v with ⟨⟨j,q⟩,h⟩; cases h; rfl
  right_inv q := rfl

theorem card_point [Finite G] (hcard : Nat.card G = 25920) : Nat.card c.Point = 27 := by
  rw [Nat.card_congr (c.fiberEquiv true), ← Subgroup.index_eq_card]
  have h := c.right.range.card_mul_index
  rw [c.right_card,hcard] at h
  change c.right.range.index = 27
  omega

theorem card_vertex [Finite G] (hcard : Nat.card G = 25920) : Nat.card c.Vertex = 72 := by
  rw [Nat.card_congr (RankTwo.vertexEquivSum c.family), Nat.card_sum,
    ← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
  have hl := c.left.range.card_mul_index
  have hr := c.right.range.card_mul_index
  rw [c.left_card,hcard] at hl
  rw [c.right_card,hcard] at hr
  change c.left.range.index + c.right.range.index = 72
  omega

theorem adjacency_flip {a b : c.Vertex} (h : c.graph.Adj a b) : b.type = !a.type := by
  have hn := h.1
  cases ha : a.type <;> cases hb : b.type <;> simp_all

instance finiteNeighbors (v : c.Vertex) : Finite (c.graph.neighborSet v) := by
  apply Nat.finite_of_card_ne_zero
  rw [c.card_neighbors v]
  cases v.type <;> decide

theorem card_two_paths (x : c.Point) :
    Nat.card {p : BasedWalk c.graph 2 x.val // p.Nonbacktracking} = 10 := by
  have h := BasedWalk.card_nonbacktracking_succ c.graph (·.type)
    (fun b => if b then 5 else 3) c.adjacency_flip c.card_neighbors 1 x.val
  simpa only [x.property, Bool.not_true, Bool.not_false, BasedWalk.forwardCount,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceSub, Nat.reduceMul] using h

theorem card_four_paths (x : c.Point) :
    Nat.card {p : BasedWalk c.graph 4 x.val // p.Nonbacktracking} = 80 := by
  have h := BasedWalk.card_nonbacktracking_succ c.graph (·.type)
    (fun b => if b then 5 else 3) c.adjacency_flip c.card_neighbors 3 x.val
  simpa only [x.property, Bool.not_true, Bool.not_false, BasedWalk.forwardCount,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceSub, Nat.reduceMul] using h
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
