module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.Incidence
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.WalkBounds

/-!
# Coordinate strata and conditional girth assembly

Points have levels 0, 2, 4, and 6 according to equality with the first point,
the simultaneous annihilator of its basis vector, and its polar hyperplane.
Lines have levels 1, 3, and 5 according to containment of the first point and
incidence with a level-two point. These definitions use coordinates and linear
incidence only; they do not assume a distance or generalized-hexagon axiom.

The maximum-level argument gives the full cycle bound once two coordinate
calculations are supplied: the distribution and unique lower point on a line,
and uniqueness of a level-three line through a level-four point. Uniqueness at
level two already follows from the span of two distinct points. Rotation and
point transitivity cover cycles based at every vertex.

The assembly theorem is conditional; its coordinate premises remain to be
proved before claiming the intrinsic girth theorem. Source context is the
split G₂ case of Aschbacher--Smith, printed pp.3--4 and 481--482; coordinates
and point reductions are those of the licensed ATLAS port.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Atlas.G2 Atlas.SplitOctonion
namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {F : Type*} [Field F]

/-- The four coordinate strata about the first singular point. These are defined
algebraically, before identifying them with distance layers. -/
noncomputable def metricPointLevel (p : SingularPoints F) : ℕ := by
  classical
  exact if p = firstPoint then 0 else if inLowerPlane p.val.rep then 2
    else if p.val.rep 7 = 0 then 4 else 6

/-- Lines through the first point, lines meeting the second point stratum,
and the remaining lines. -/
noncomputable def metricLineLevel (L : ZeroProductLine F) : ℕ := by
  classical
  exact if pointOnLine firstPoint L then 1
    else if ∃ p : SingularPoints F, pointOnLine p L ∧ metricPointLevel p = 2 then 3 else 5

noncomputable def metricLevel : GeometryVertex F → ℕ
  | Sum.inl L => metricLineLevel L
  | Sum.inr p => metricPointLevel p

@[simp] theorem metricPointLevel_first : metricPointLevel (firstPoint (K := F)) = 0 := by
  simp [metricPointLevel]

theorem metricPointLevel_eq_zero_iff (p : SingularPoints F) :
    metricPointLevel p = 0 ↔ p = firstPoint := by
  classical
  simp only [metricPointLevel]
  split_ifs <;> simp_all

theorem metricPointLevel_cases (p : SingularPoints F) :
    metricPointLevel p = 0 ∨ metricPointLevel p = 2 ∨
      metricPointLevel p = 4 ∨ metricPointLevel p = 6 := by
  classical
  unfold metricPointLevel
  split_ifs <;> simp

theorem metricLineLevel_cases (L : ZeroProductLine F) :
    metricLineLevel L = 1 ∨ metricLineLevel L = 3 ∨ metricLineLevel L = 5 := by
  classical
  unfold metricLineLevel
  split_ifs <;> simp

theorem metricPointLevel_eq_two_iff (p : SingularPoints F) :
    metricPointLevel p = 2 ↔ p ≠ firstPoint ∧ inLowerPlane p.val.rep := by
  classical
  unfold metricPointLevel
  split_ifs <;> simp_all

theorem metricPointLevel_eq_four_iff (p : SingularPoints F) :
    metricPointLevel p = 4 ↔ p ≠ firstPoint ∧ ¬ inLowerPlane p.val.rep ∧ p.val.rep 7 = 0 := by
  classical
  unfold metricPointLevel
  split_ifs <;> simp_all

theorem metricLineLevel_eq_one_iff (L : ZeroProductLine F) :
    metricLineLevel L = 1 ↔ pointOnLine firstPoint L := by
  classical
  unfold metricLineLevel
  split_ifs <;> simp_all

theorem metricLineLevel_eq_three_iff (L : ZeroProductLine F) :
    metricLineLevel L = 3 ↔ ¬ pointOnLine firstPoint L ∧
      ∃ p : SingularPoints F, pointOnLine p L ∧ metricPointLevel p = 2 := by
  classical
  unfold metricLineLevel
  split_ifs <;> simp_all

/-- The level-two predecessor is the line spanned with the first point.
Consequently only uniqueness at level four remains to be supplied. -/
theorem metric_point_predecessors_of_level_four
    (hfour : ∀ (p : SingularPoints F) (L M : ZeroProductLine F),
      metricPointLevel p = 4 → pointOnLine p L → pointOnLine p M →
      metricLineLevel L = 3 → metricLineLevel M = 3 → L = M)
    (p : SingularPoints F) (L M : ZeroProductLine F)
    (hpL : pointOnLine p L) (hpM : pointOnLine p M) (hb : metricPointLevel p < 6)
    (hL : metricLineLevel L + 1 = metricPointLevel p)
    (hM : metricLineLevel M + 1 = metricPointLevel p) : L = M := by
  rcases metricPointLevel_cases p with h | h | h | h
  · omega
  · have hL' : metricLineLevel L = 1 := by omega
    have hM' : metricLineLevel M = 1 := by omega
    have hne : p ≠ firstPoint := (metricPointLevel_eq_two_iff p).mp h |>.1
    exact metric_line_unique hne hpL ((metricLineLevel_eq_one_iff L).mp hL')
      hpM ((metricLineLevel_eq_one_iff M).mp hM')
  · exact hfour p L M h hpL hpM (by omega) (by omega)
  · omega

/-- Conditional girth assembly. The premises concern only algebraic coordinate
strata and their incidences; they still require proofs in the intrinsic geometry. -/
theorem metric_girth_of_predecessors
    (hline_step : ∀ (L : ZeroProductLine F) (p : SingularPoints F), pointOnLine p L →
      metricPointLevel p + 1 = metricLineLevel L ∨ metricLineLevel L + 1 = metricPointLevel p)
    (hline_unique : ∀ (L : ZeroProductLine F) (p q : SingularPoints F),
      pointOnLine p L → pointOnLine q L →
      metricPointLevel p + 1 = metricLineLevel L →
      metricPointLevel q + 1 = metricLineLevel L → p = q)
    (hpoint_four : ∀ (p : SingularPoints F) (L M : ZeroProductLine F),
      metricPointLevel p = 4 → pointOnLine p L → pointOnLine p M →
      metricLineLevel L = 3 → metricLineLevel M = 3 → L = M)
    (x : GeometryVertex F) (w : geometryGraph.Walk x x) (hw : w.IsCycle) :
    12 ≤ w.length := by
  classical
  have hpoint_unique := metric_point_predecessors_of_level_four hpoint_four
  have hadj {x y : GeometryVertex F} (h : geometryGraph.Adj x y) :
      metricLevel x + 1 = metricLevel y ∨ metricLevel y + 1 = metricLevel x := by
    cases x with
    | inl L =>
      cases y with
      | inl M => exact h.elim
      | inr p => exact (hline_step L p h).symm
    | inr p =>
      cases y with
      | inl L => exact hline_step L p h
      | inr q => exact h.elim
  have huniq {x y z : GeometryVertex F} (_ : 0 < metricLevel x)
      (hb : metricLevel x < 6) (hy : geometryGraph.Adj x y) (hz : geometryGraph.Adj x z)
      (hyl : metricLevel y + 1 = metricLevel x) (hzl : metricLevel z + 1 = metricLevel x) :
      y = z := by
    cases x with
    | inl L =>
      cases y with
      | inl M => exact hy.elim
      | inr p =>
        cases z with
        | inl M => exact hz.elim
        | inr q => exact congrArg Sum.inr (hline_unique L p q hy hz hyl hzl)
    | inr p =>
      cases y with
      | inr q => exact hy.elim
      | inl L =>
        cases z with
        | inr q => exact hz.elim
        | inl M => exact congrArg Sum.inl (hpoint_unique p L M hy hz hb hyl hzl)
  have hbase (v : geometryGraph.Walk (Sum.inr (firstPoint (K := F)))
      (Sum.inr firstPoint)) (hv : v.IsCycle) : 12 ≤ v.length :=
    metric_cycle_bound_of_levels metricLevel hadj huniq
      (x := Sum.inr firstPoint) metricPointLevel_first v hv
  have hpoint (p : SingularPoints F) (v : geometryGraph.Walk (Sum.inr p) (Sum.inr p))
      (hv : v.IsCycle) : 12 ≤ v.length := by
    obtain ⟨g,hg⟩ := exists_smul_firstPoint p
    let v' := v.map (metricGraphIso g).toHom
    have he : (metricGraphIso g).toHom (Sum.inr p) = Sum.inr firstPoint :=
      congrArg Sum.inr hg
    have hc : (v'.copy he he).IsCycle := by
      simpa using hv.map (metricGraphIso g).injective
    have hb := hbase (v'.copy he he) hc
    simpa [v'] using hb
  cases x with
  | inr p => exact hpoint p w hw
  | inl L =>
    have had := w.adj_snd hw.not_nil
    cases hs : w.snd with
    | inl M =>
      rw [hs] at had
      exact had.elim
    | inr p =>
      have hm : Sum.inr p ∈ w.support := by
        rw [← hs]
        exact w.getVert_mem_support 1
      have hb := hpoint p (w.rotate (Sum.inr p) hm) (hw.rotate hm)
      simpa using hb

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
