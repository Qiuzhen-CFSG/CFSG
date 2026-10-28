module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.RegularSphere

/-!
# Diameter and size of the original cubic component

A point at distance two has four common neighbors with W. No two of
them lie on one line through that point, so each of its four lines
contains one. Consequently every neighbor is again at distance at most
two from W. The connected component therefore consists exactly of W,
its 36 neighbors and its 243 points at distance two, and has order 280.

This is the component calculation in Asc94 45.10(8)–(10), p.248. The
global connectedness assertion is deliberately kept separate.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

theorem distance_two_common_neighbor_on_each_line {U : c.points}
    (hU : c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2)
    (L : c.linesThrough U.val) :
    ∃ Z : c.collinearity.commonNeighbors ⟨c.W, c.point_mem⟩ U, Z.val.val ≤ L.val := by
  classical
  let W : c.points := ⟨c.W, c.point_mem⟩
  let C := c.collinearity.commonNeighbors W U
  have hs (Z : C) : ∃ L : c.linesThrough U.val, Z.val.val ≤ L.val := by
    obtain ⟨-, -, L, hL, hUL, hZL⟩ := Z.property.2
    exact ⟨⟨L, hL, hUL⟩, hZL⟩
  let f (Z : C) : c.linesThrough U.val := (hs Z).choose
  have hf (Z : C) : Z.val.val ≤ (f Z).val := (hs Z).choose_spec
  have hd := c.collinearity.edist_eq_two_iff.mp hU
  have hinj : Function.Injective f := by
    intro Z Z' he
    apply Subtype.ext
    exact c.common_neighbors_on_line_unique U W Z.val Z'.val
      (fun hh => hd.2.1 (c.collinearity.adj_symm hh)) (Ne.symm hd.1)
      ⟨Z.property.2, Z.property.1⟩ ⟨Z'.property.2, Z'.property.1⟩
      (f Z).property (hf Z) (he ▸ hf Z')
  have hb : Function.Bijective f := hinj.bijective_of_nat_card_le (by
    change Nat.card (c.linesThrough U.val) ≤ Nat.card (c.collinearity.commonNeighbors W U)
    rw [c.linesThrough_card U.property, c.distance_two_common_neighbors_card hU])
  obtain ⟨Z, hZ⟩ := hb.2 L
  exact ⟨Z, hZ ▸ hf Z⟩

/-- Membership in the closed ball of radius two, without a finite-distance convention. -/
def withinTwo (U : c.points) : Prop :=
  U = ⟨c.W, c.point_mem⟩ ∨ c.collinearity.Adj ⟨c.W, c.point_mem⟩ U ∨
    c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2

omit [Finite G] in
private theorem withinTwo_of_common_neighbor (U Z : c.points)
    (hWZ : c.collinearity.Adj ⟨c.W, c.point_mem⟩ Z) (hUZ : c.collinearity.Adj U Z) :
    c.withinTwo U := by
  classical
  by_cases he : U = ⟨c.W, c.point_mem⟩
  · exact Or.inl he
  by_cases ha : c.collinearity.Adj ⟨c.W, c.point_mem⟩ U
  · exact Or.inr (Or.inl ha)
  exact Or.inr (Or.inr (c.collinearity.edist_eq_two_iff.mpr
    ⟨Ne.symm he, ha, Z, hWZ, hUZ⟩))

/-- No edge leaves the closed radius-two ball. -/
theorem withinTwo_adj {U U' : c.points} (hU : c.withinTwo U)
    (hadj : c.collinearity.Adj U U') : c.withinTwo U' := by
  rcases hU with he | ha | hd
  · exact Or.inr (Or.inl (he ▸ hadj))
  · exact c.withinTwo_of_common_neighbor U' U ha (c.collinearity.adj_symm hadj)
  · obtain ⟨-, hne, L, hL, hUL, hU'L⟩ := hadj
    obtain ⟨Z, hZL⟩ := c.distance_two_common_neighbor_on_each_line hd ⟨L, hL, hUL⟩
    by_cases he : U' = Z.val
    · exact Or.inr (Or.inl (he.symm ▸ Z.property.1))
    · have hUZ : c.collinearity.Adj U' Z.val :=
        ⟨Z.val.property, fun hh => he (Subtype.ext hh.symm), L, hL, hU'L, hZL⟩
      exact c.withinTwo_of_common_neighbor U' Z.val Z.property.1 hUZ

theorem reachable_iff_withinTwo (U : c.points) :
    c.collinearity.Reachable ⟨c.W, c.point_mem⟩ U ↔ c.withinTwo U := by
  constructor
  · intro hh
    have hr := (c.collinearity.reachable_iff_reflTransGen _ _).mp hh
    clear hh
    induction hr with
    | refl => exact Or.inl rfl
    | tail _ ha ih => exact c.withinTwo_adj ih ha
  · rintro (he | ha | hd)
    · subst U
      rfl
    · exact ha.reachable
    · obtain ⟨-, -, Z, hWZ, hUZ⟩ := c.collinearity.edist_eq_two_iff.mp hd
      exact hWZ.reachable.trans (c.collinearity.adj_symm hUZ).reachable

/-- The source component has 1 + 36 + 243 = 280 vertices. -/
theorem component_card : Nat.card
    {U : c.points // c.collinearity.Reachable ⟨c.W, c.point_mem⟩ U} = 280 := by
  classical
  let W : c.points := ⟨c.W, c.point_mem⟩
  let A : Set c.points := {W}
  let B := c.collinearity.neighborSet W
  let C := {U : c.points | c.collinearity.edist W U = 2}
  have hab : Disjoint A B := Set.disjoint_left.mpr (by
    intro U hUA hUB
    have he : U = W := hUA
    exact c.collinearity.irrefl (he ▸ hUB))
  have habc : Disjoint (A ∪ B) C := Set.disjoint_left.mpr (by
    intro U hU hUC
    have hd := c.collinearity.edist_eq_two_iff.mp hUC
    rcases hU with ha | hb
    · exact hd.1 (Set.mem_singleton_iff.mp ha).symm
    · exact hd.2.1 hb)
  have he : {U : c.points | c.collinearity.Reachable W U} = (A ∪ B) ∪ C := by
    ext U
    change c.collinearity.Reachable ⟨c.W, c.point_mem⟩ U ↔ U ∈ (A ∪ B) ∪ C
    rw [c.reachable_iff_withinTwo]
    change (U = W ∨ c.collinearity.Adj W U ∨ c.collinearity.edist W U = 2) ↔
      ((U = W ∨ c.collinearity.Adj W U) ∨ c.collinearity.edist W U = 2)
    exact or_assoc.symm
  change ({U : c.points | c.collinearity.Reachable W U}).ncard = 280
  rw [he, Set.ncard_union_eq habc, Set.ncard_union_eq hab]
  have ha : A.ncard = 1 := Set.ncard_singleton W
  have hb : B.ncard = 36 := c.collinearity_neighbor_card W
  have hc : C.ncard = 243 := c.distance_two_sphere_card
  omega

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
