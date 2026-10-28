module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.G2Three.NativeSeven
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.SevenGirth

/-!
# Short-path geometry in every faithful ternary G₂ completion

The native seven-path action transfers through the common universal coset
cover. Whole Borel overlap and the endpoint orders give valence four. The
seven-path action then rules out every cycle shorter than twelve. These
statements require neither ambient finiteness nor the order-six hypothesis.

Source: Aschbacher–Smith F.3.3–6 and F.4.6(1), printed pp.270–272 and 276.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
open Subgroup Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (c : Completion G)

theorem graphAction : GraphAction c.graph G where
  map_adj g := (translationGraphIso c.family g).toHom.map_adj

theorem seven_transitive (v : c.Vertex) : RootPathTransitive c.graph G v 7 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.family v
  have hm : RootPathTransitive modelCompletion.graph NativeSeven.MG
      (RankTwo.base modelCompletion.family v.type) 7 := by
    change RootPathTransitive (RankTwo.graph modelCompletion.family) _ _ _
    rw [NativeSeven.completion_family]
    exact NativeSeven.seven_path_transitive _
  have hb := (c.rootPathTransitive_iff_model v.type 7).mpr hm
  simpa only [hg] using RootPathTransitive.smul c.graphAction hb g

theorem left_card : Nat.card c.left.range = 11664 := by
  rw [Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion.left_card]
  exact NativeSeven.family_card false

theorem family_card (i : Bool) : Nat.card (c.family i) = 11664 := by
  cases i
  · exact c.left_card
  · exact c.right_card

theorem family_intersection (i : Bool) : c.family i ⊓ c.family (!i) = c.middle.range := by
  cases i
  · exact c.overlap
  · exact (inf_comm _ _).trans c.overlap

theorem base_neighbor_card (i : Bool) : Nat.card (c.graph.neighborSet (RankTwo.base c.family i)) = 4 := by
  rw [card_neighbor_base]
  have hidx := ((c.family (!i)).subgroupOf (c.family i)).card_mul_index
  have hmid : Nat.card ((c.family (!i)).subgroupOf (c.family i)) = Nat.card c.middle.range := by
    rw [←Subgroup.inf_subgroupOf_right]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,inf_comm,
      c.family_intersection]
  rw [hmid,c.middle_card,c.family_card] at hidx
  omega

theorem card_neighbors (v : c.Vertex) : Nat.card (c.graph.neighborSet v) = 4 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.family v
  have hh := Nat.card_congr ((translationGraphIso c.family g).mapNeighborSet (RankTwo.base c.family v.type))
  change Nat.card (c.graph.neighborSet (RankTwo.base c.family v.type)) =
    Nat.card (c.graph.neighborSet (g • RankTwo.base c.family v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans (c.base_neighbor_card v.type)

instance finiteNeighbors (v : c.Vertex) : Finite (c.graph.neighborSet v) :=
  Nat.finite_of_card_ne_zero (by rw [c.card_neighbors]; decide)

theorem thick (v a b : c.Vertex) : ∃z,c.graph.Adj v z ∧ z≠a ∧ z≠b := by
  classical
  let := Fintype.ofFinite (c.graph.neighborSet v)
  have hc : 2 < Fintype.card (c.graph.neighborSet v) := by
    rw [←Nat.card_eq_fintype_card,c.card_neighbors]
    decide
  obtain ⟨x,y,z,hxy,hxz,hyz⟩ := Fintype.two_lt_card_iff.mp hc
  by_contra hh
  push Not at hh
  have hx : x.val=a ∨ x.val=b := by
    by_cases ha : x.val=a
    · exact Or.inl ha
    · exact Or.inr (hh x.val x.property ha)
  have hy : y.val=a ∨ y.val=b := by
    by_cases ha : y.val=a
    · exact Or.inl ha
    · exact Or.inr (hh y.val y.property ha)
  have hz : z.val=a ∨ z.val=b := by
    by_cases ha : z.val=a
    · exact Or.inl ha
    · exact Or.inr (hh z.val z.property ha)
  have hxy' : x.val≠y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val≠z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val≠z.val := fun h => hyz (Subtype.ext h)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;> simp_all

theorem hasTwoNeighbors : BasedWalk.HasTwoNeighbors c.graph := by
  intro v a
  obtain ⟨z,hz,hza,_⟩ := c.thick v a a
  exact ⟨z,hz,hza⟩

theorem cycle_length_ge_twelve (v : c.Vertex) (p : c.graph.Walk v v) (hp : p.IsCycle) :
    12≤p.length :=
  cycle_bound_of_seven_transitive c.graphAction c.thick c.seven_transitive
    (·.type) (fun h => h.1) v p hp
end CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
