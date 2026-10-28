module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.CommonNeighbors

/-!
# Counting the original two-step paths

Adjacent points have exactly the eight other points of their unique line
as common neighbors. Of the 36 neighbors of the second point, eight are
therefore adjacent to the first and one is the first point itself. The
remaining 27 give two-step paths to the distance-two sphere. There are
36·27 = 972 such paths from each original point.

Source: Aschbacher, *Sporadic Groups* (1994), 45.10(4)–(6), p.248.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

theorem adjacent_common_neighbors_card (U U' : c.points) (hadj : c.collinearity.Adj U U') :
    Nat.card (c.collinearity.commonNeighbors U U') = 8 := by
  classical
  have hadj0 := hadj
  obtain ⟨-, hne, L, hL, hUL, hU'L⟩ := hadj0
  let T := c.otherPoints U.val L \ {U'.val}
  have hZL (Z : c.collinearity.commonNeighbors U U') : Z.val.val ≤ L := by
    obtain ⟨M, hM, hUM, hU'M, hZM⟩ := c.triangle_on_line U U' Z.val hadj Z.property.1 Z.property.2
    exact (c.line_unique U.property U'.property hL hM hne hUL hUM hU'L hU'M) ▸ hZM
  let f : c.collinearity.commonNeighbors U U' → T := fun Z =>
    ⟨Z.val.val, ⟨⟨Z.val.property, hZL Z⟩, Z.property.1.2.1⟩, Z.property.2.2.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro Z Z' he
      have hh : Z.val.val = Z'.val.val := congrArg (fun a : T => a.val) he
      exact Subtype.ext (Subtype.ext hh)
    · rintro ⟨Z, ⟨⟨hZ, hZL⟩, hZU⟩, hZU'⟩
      exact ⟨⟨⟨Z, hZ⟩, ⟨hZ, hZU, L, hL, hUL, hZL⟩,
        ⟨hZ, hZU', L, hL, hU'L, hZL⟩⟩, rfl⟩
  rw [Nat.card_eq_of_bijective f hf]
  change (c.otherPoints U.val L \ {U'.val}).ncard = 8
  rw [Set.ncard_sdiff_singleton_of_mem (show U'.val ∈ c.otherPoints U.val L from
    ⟨⟨U'.property, hU'L⟩, hne⟩)]
  change Nat.card (c.otherPoints U.val L) - 1 = 8
  rw [c.otherPoints_card U.property hL hUL]

/-- The endpoints available after one fixed edge, excluding shorter paths. -/
def twoStepEndpoints (U Z : c.points) : Set c.points :=
  (c.collinearity.neighborSet Z \ c.collinearity.neighborSet U) \ {U}

theorem twoStepEndpoints_card (U Z : c.points) (hadj : c.collinearity.Adj U Z) :
    Nat.card (c.twoStepEndpoints U Z) = 27 := by
  have hm : U ∈ c.collinearity.neighborSet Z \ c.collinearity.neighborSet U :=
    ⟨c.collinearity.adj_symm hadj, c.collinearity.irrefl⟩
  change ((c.collinearity.neighborSet Z \ c.collinearity.neighborSet U) \ {U}).ncard = 27
  rw [Set.ncard_sdiff_singleton_of_mem hm]
  have hh := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (c.collinearity.neighborSet Z) (c.collinearity.neighborSet U)
  have hc : (c.collinearity.neighborSet Z ∩ c.collinearity.neighborSet U).ncard = 8 :=
    c.adjacent_common_neighbors_card Z U (c.collinearity.adj_symm hadj)
  rw [hc, show (c.collinearity.neighborSet Z).ncard = 36 from c.collinearity_neighbor_card Z] at hh
  omega

/-- The actual two-step paths whose endpoints have distance two. -/
def twoSteps (U : c.points) := Σ Z : c.collinearity.neighborSet U, c.twoStepEndpoints U Z.val

theorem twoSteps_card (U : c.points) : Nat.card (c.twoSteps U) = 972 := by
  classical
  let : Fintype (c.collinearity.neighborSet U) := Fintype.ofFinite _
  change Nat.card (Σ Z : c.collinearity.neighborSet U, c.twoStepEndpoints U Z.val) = 972
  rw [Nat.card_sigma]
  have hc (Z : c.collinearity.neighborSet U) : Nat.card (c.twoStepEndpoints U Z.val) = 27 :=
    c.twoStepEndpoints_card U Z.val Z.property
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, c.collinearity_neighbor_card]

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
