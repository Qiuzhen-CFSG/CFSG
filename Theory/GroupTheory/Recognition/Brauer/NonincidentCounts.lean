module
public import Theory.GroupTheory.Recognition.Brauer.BlockIntersection
public import Theory.GroupTheory.Recognition.Brauer.BlockSizes
public import Theory.GroupTheory.Recognition.Brauer.DualSeed

/-!
# Nonincident block counts in Brauer's geometry

Every point is nonincident with exactly `q²` lines, and every line with
exactly `q²` points. These are Brauer, *On finite Desarguesian planes I*,
(2C) and its dual, article p. 120. The result uses only the first three
postulates and the original disjointness incidence; no projective-plane
structure or total number of points is assumed.

Map each involution in a point to its unique containing line. That line
is nonincident with the point because their intersection contains the
involution. Point-line intersections are subsingletons, so the map is
injective; every nonincident line has a nonempty intersection, giving
surjectivity. The point has `q²` involutions by `block_sizes`.
Applying the same proof to the actual dual seed gives the other count.
-/

namespace Theory.GroupTheory.BrauerPlaneSeed
private theorem nonincident_lines_card
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)
    (p : S.Point) : Nat.card {l : S.Line // p ∉ l} = (p : Set G).ncard := by
  classical
  let line (x : (p : Set G)) : S.Line :=
    (S.existsUnique_blocks_of_involution (S.orderOf_mem_point p x.property)).2.choose
  have hmem (x : (p : Set G)) : (x : G) ∈ (line x : Set G) :=
    (S.existsUnique_blocks_of_involution (S.orderOf_mem_point p x.property)).2.choose_spec.1
  have hnot (x : (p : Set G)) : p ∉ line x := by
    intro hi
    exact (Set.disjoint_left.mp ((S.mem_iff_disjoint p (line x)).mp hi)) x.property (hmem x)
  let f : ↥(p : Set G) → {l : S.Line // p ∉ l} := fun x => ⟨line x, hnot x⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x z h
      have heq : line x = line z := congrArg Subtype.val h
      apply Subtype.ext
      exact S.point_line_intersection_subsingleton p (line x) ⟨x.property, hmem x⟩ ⟨z.property, heq.symm ▸ hmem z⟩
    · intro l
      have hnon : ((p : Set G) ∩ (l : Set G)).Nonempty := by
        exact Set.not_disjoint_iff_nonempty_inter.mp
          (fun hd => l.property ((S.mem_iff_disjoint p l).mpr hd))
      obtain ⟨x, hxp, hxl⟩ := hnon
      refine ⟨⟨x, hxp⟩, Subtype.ext ?_⟩
      exact (S.existsUnique_blocks_of_involution (S.orderOf_mem_point p hxp)).2.unique (hmem ⟨x,hxp⟩) hxl
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

/-- Brauer I (2C) and its dual, using the actual nonincidence subtypes. -/
public theorem nonincident_counts {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) :
    (∀ p : S.Point, Nat.card {l : S.Line // p ∉ l} = S.q ^ 2) ∧
    (∀ l : S.Line, Nat.card {p : S.Point // p ∉ l} = S.q ^ 2) := by
  constructor
  · intro p
    exact (nonincident_lines_card S p).trans (S.block_sizes.1 p)
  · intro l
    have hcard : Nat.card {p : S.Point // p ∉ l} =
        Nat.card {p : S.dual.Line // (show S.dual.Point from l) ∉ p} := by
      exact Nat.card_congr (Equiv.subtypeEquivRight fun p =>
        (not_congr (S.dual_incidence_iff p l)).symm)
    rw [hcard]
    simpa only [S.dual_q] using
      (nonincident_lines_card S.dual l).trans (S.dual.block_sizes.1 l)
end Theory.GroupTheory.BrauerPlaneSeed

