module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.IntrinsicGeometry

/-!
# Cycle bounds from levels

A height changing by one across each edge is bounded by walk length. If every
vertex at positive height below six has at most one neighbor at the preceding
height, a cycle based at height zero has length at least twelve: take a vertex
of maximum height on a hypothetical shorter cycle. Both cycle neighbors have
height one less, while the two arcs from the base bound that maximum by five.

This elementary graph argument is used with concrete octonion coordinate levels;
it assumes no generalized-polygon structure. Source context: the split G₂
geometry for Aschbacher--Smith, printed pp.3--4 and 481--482.
-/

public section

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {V : Type*} {G : SimpleGraph V}

/-- A height that changes by one along edges changes by at most walk length. -/
theorem metric_level_le_walk_length (level : V → ℕ)
    (hadj : ∀ {x y}, G.Adj x y → level x + 1 = level y ∨ level y + 1 = level x)
    {x y : V} (w : G.Walk x y) : level y ≤ level x + w.length := by
  induction w with
  | nil => simp
  | @cons x z y hx w ih =>
    have h := hadj hx
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- A short cycle has a maximum below level six and two different predecessors.
Thus uniqueness of predecessors below six rules out every cycle of length < 12. -/
theorem metric_cycle_bound_of_levels (level : V → ℕ)
    (hadj : ∀ {x y}, G.Adj x y → level x + 1 = level y ∨ level y + 1 = level x)
    (hunique : ∀ {x y z}, 0 < level x → level x < 6 → G.Adj x y → G.Adj x z →
      level y + 1 = level x → level z + 1 = level x → y = z)
    {x : V} (hx : level x = 0) (w : G.Walk x x) (hw : w.IsCycle) :
    12 ≤ w.length := by
  classical
  by_contra hlen
  have hl := hw.three_le_length
  have hbound (i : ℕ) (hi : i ≤ w.length) :
      level (w.getVert i) ≤ i ∧ level (w.getVert i) ≤ w.length - i := by
    have ha := metric_level_le_walk_length level hadj (w.take i)
    have hb := metric_level_le_walk_length level hadj ((w.drop i).reverse)
    simpa [hx, SimpleGraph.Walk.take_length, Nat.min_eq_left hi] using And.intro ha hb
  obtain ⟨i, hi, hmax⟩ := (Finset.range (w.length + 1)).exists_max_image
    (fun j => level (w.getVert j)) (by simp)
  have hi' : i ≤ w.length := by simpa using hi
  have hfirst : level (w.getVert 1) = 1 := by
    have h := hadj (w.adj_getVert_succ (i := 0) (by omega))
    simpa [hx, eq_comm] using h
  have hpositive : 0 < level (w.getVert i) := by
    have hm := hmax 1 (by simp; omega)
    omega
  have hzero : i ≠ 0 := by
    intro h
    simp [h, hx] at hpositive
  have hend : i ≠ w.length := by
    intro h
    simp [h, hx] at hpositive
  have hib : 0 < i ∧ i < w.length := by omega
  have hbelow : level (w.getVert i) < 6 := by
    obtain ⟨ha, hb⟩ := hbound i hi'
    omega
  have hleft : G.Adj (w.getVert i) (w.getVert (i - 1)) := by
    have h := (w.adj_getVert_succ (i := i - 1) (by omega)).symm
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ i)] using h
  have hright := w.adj_getVert_succ hib.2
  have hleftLevel : level (w.getVert (i - 1)) + 1 = level (w.getVert i) := by
    have hm := hmax (i - 1) (by simp; omega)
    have ha := hadj hleft
    omega
  have hrightLevel : level (w.getVert (i + 1)) + 1 = level (w.getVert i) := by
    have hm := hmax (i + 1) (by simp; omega)
    have ha := hadj hright
    omega
  exact hw.getVert_sub_one_ne_getVert_add_one hi'
    (hunique hpositive hbelow hleft hright hleftLevel hrightLevel)

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
