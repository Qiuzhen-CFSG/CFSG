module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.Incidence
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CoordinateFrame

/-!
# Diameter of the intrinsic octonion incidence graph

Point transitivity and the four parabolic point orbits reduce point distances
to explicit coordinate walks of lengths 0, 2, 4, and 6. Every zero-product
plane meets the polar hyperplane of the first point by rank-nullity. The
intersection gives a point in one of the first three orbits, hence a walk of
length at most five from any point to any line. This also covers line-line
pairs by adjoining one incidence edge.

The result is for the actual graph of singular points and two-dimensional
zero-product subspaces and holds over every field. The coordinate reductions
are from the licensed ATLAS port. Source context: the split G₂ case in
Aschbacher--Smith, Theorem 0.1.2(1), printed pp.3--4, repeated as
Theorem 0.1.1 on pp.481--482.
-/

public section

set_option backward.isDefEq.respectTransparency false

open Atlas.G2 Atlas.SplitOctonion
namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {F : Type*} [Field F]

private theorem coordinate_two_walk {i j : Fin 6}
    (hij : offDiagonalIndex i ≠ offDiagonalIndex j)
    (hprod : mul (offDiagonalVector (F := F) i) (offDiagonalVector j) = 0 ∧
      mul (offDiagonalVector (F := F) j) (offDiagonalVector i) = 0) :
    ∃ w : geometryGraph.Walk (Sum.inr (coordinatePoint (F := F) i))
      (Sum.inr (coordinatePoint j)), w.length = 2 := by
  have hi : LinearIndependent F ![offDiagonalVector (F := F) i, offDiagonalVector j] := by
    rw [linearIndependent_fin2]
    refine ⟨offDiagonalVector_ne_zero j, ?_⟩
    intro a ha
    have h := congrFun ha (offDiagonalIndex i)
    simp [offDiagonalVector, basisVector, hij] at h
  have hr : Set.range (![offDiagonalVector (F := F) i, offDiagonalVector j] : Fin 2 → Carrier F) =
      {offDiagonalVector i, offDiagonalVector j} := by
    ext x
    simp [or_comm]
  have hdim : Module.finrank F
      (Submodule.span F {offDiagonalVector (F := F) i, offDiagonalVector j}) = 2 := by
    have h := finrank_span_eq_card hi
    change Module.finrank F (Submodule.span F
      (Set.range (![offDiagonalVector i, offDiagonalVector j] : Fin 2 → Carrier F))) = 2 at h
    rw [hr] at h
    exact h
  have hs (k : Fin 6) : mul (offDiagonalVector (F := F) k) (offDiagonalVector k) = 0 := by
    have h := quadratic_identity (offDiagonalVector (F := F) k)
    simpa [(offDiagonal_singular k).1, (offDiagonal_singular k).2] using h
  have hplane : IsZeroProductLine
      (Submodule.span F {offDiagonalVector (F := F) i, offDiagonalVector j}) := by
    refine ⟨hdim, ?_⟩
    intro x hx y hy
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [SplitOctonion.add_mul, SplitOctonion.mul_add, SplitOctonion.smul_mul,
      SplitOctonion.mul_smul, hprod.1, hprod.2, hs, smul_zero, add_zero]
  let L : ZeroProductLine F := ⟨_, hplane⟩
  have hL (k : Fin 6) (hk : k = i ∨ k = j) : pointOnLine (coordinatePoint k) L := by
    change (Projectivization.mk F (offDiagonalVector k) _).submodule ≤ L.val
    rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
    apply Submodule.subset_span
    rcases hk with rfl | rfl <;> simp
  exact ⟨.cons (v := Sum.inl L) (hL i (Or.inl rfl))
    (.cons (v := Sum.inr (coordinatePoint j)) (hL j (Or.inr rfl)) .nil), rfl⟩

/-- The four point-orbit representatives have explicit walks of lengths 0, 2, 4, 6. -/
theorem metric_walk_orbitPoint (i : Fin 4) :
    ∃ w : geometryGraph.Walk (Sum.inr (firstPoint (K := F))) (Sum.inr (orbitPoint i)),
      w.length = 2 * i.val := by
  have h01 := coordinate_two_walk (F := F) (i := 0) (j := 1) (by decide)
    (by constructor <;> ext k <;> fin_cases k <;>
      simp [mul, offDiagonalVector, offDiagonalIndex, basisVector])
  have h02 := coordinate_two_walk (F := F) (i := 0) (j := 2) (by decide)
    (by constructor <;> ext k <;> fin_cases k <;>
      simp [mul, offDiagonalVector, offDiagonalIndex, basisVector])
  have h24 := coordinate_two_walk (F := F) (i := 2) (j := 4) (by decide)
    (by constructor <;> ext k <;> fin_cases k <;>
      simp [mul, offDiagonalVector, offDiagonalIndex, basisVector])
  have h45 := coordinate_two_walk (F := F) (i := 4) (j := 5) (by decide)
    (by constructor <;> ext k <;> fin_cases k <;>
      simp [mul, offDiagonalVector, offDiagonalIndex, basisVector])
  fin_cases i
  · exact ⟨.nil, rfl⟩
  · exact h01
  · obtain ⟨u,hu⟩ := h02
    obtain ⟨v,hv⟩ := h24
    exact ⟨u.append v, by simp [SimpleGraph.Walk.length_append,hu,hv]⟩
  · obtain ⟨u,hu⟩ := h02
    obtain ⟨v,hv⟩ := h24
    obtain ⟨w,hw⟩ := h45
    exact ⟨(u.append v).append w, by simp [SimpleGraph.Walk.length_append,hu,hv,hw]⟩

/-- Every point is within six edges of the first point. -/
theorem metric_firstPoint_walk (p : SingularPoints F) :
    ∃ w : geometryGraph.Walk (Sum.inr (firstPoint (K := F))) (Sum.inr p),
      w.length ≤ 6 := by
  obtain ⟨g,i,hi⟩ := parabolic_four_point_representatives p
  obtain ⟨w,hw⟩ := metric_walk_orbitPoint (F := F) i
  have hg : g.val • firstPoint = firstPoint (K := F) :=
    MulAction.mem_stabilizer_iff.mp (parabolic_le_pointStabilizer g.property)
  have he : g.val⁻¹ • firstPoint = firstPoint (K := F) := by
    exact (congrArg (fun p : SingularPoints F => g.val⁻¹ • p) hg).symm.trans
      (inv_smul_smul g.val firstPoint)
  have hp : g.val⁻¹ • orbitPoint i = p := by rw [← hi, inv_smul_smul]
  refine ⟨(w.map (metricGraphIso g.val⁻¹).toHom).copy
    (by exact congrArg Sum.inr he) (by exact congrArg Sum.inr hp), ?_⟩
  simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map, hw]
  omega

/-- Points in the polar hyperplane are within four edges of the first point. -/
theorem metric_firstPoint_walk_of_polar (p : SingularPoints F) (hp : p.val.rep 7 = 0) :
    ∃ w : geometryGraph.Walk (Sum.inr (firstPoint (K := F))) (Sum.inr p),
      w.length ≤ 4 := by
  obtain ⟨g,i,hi⟩ := parabolic_four_point_representatives p
  have hnot : i ≠ 3 := by
    intro he
    subst i
    have hzero := (pointStabilizer_last_zero_iff
      ⟨g.val, parabolic_le_pointStabilizer g.property⟩ p.val.rep).mpr hp
    rw [← singularPointMk_rep F p, singularPointMk_smul, orbitPoint] at hi
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp
      (congrArg Subtype.val hi)
    have hh := congrFun ha 7
    simp [Units.smul_def, orbitBasisIndex, basisVector, hzero] at hh
  obtain ⟨w,hw⟩ := metric_walk_orbitPoint (F := F) i
  have hg : g.val • firstPoint = firstPoint (K := F) :=
    MulAction.mem_stabilizer_iff.mp (parabolic_le_pointStabilizer g.property)
  have he : g.val⁻¹ • firstPoint = firstPoint (K := F) := by
    exact (congrArg (fun p : SingularPoints F => g.val⁻¹ • p) hg).symm.trans
      (inv_smul_smul g.val firstPoint)
  have hpi : g.val⁻¹ • orbitPoint i = p := by rw [← hi, inv_smul_smul]
  refine ⟨(w.map (metricGraphIso g.val⁻¹).toHom).copy
    (by exact congrArg Sum.inr he) (by exact congrArg Sum.inr hpi), ?_⟩
  simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map, hw]
  have : i.val ≠ 3 := fun h => hnot (Fin.ext h)
  omega

/-- Each line contains an actual projective point polar to the first point. -/
theorem metric_line_has_polar_point (L : ZeroProductLine F) :
    ∃ p : SingularPoints F, pointOnLine p L ∧ p.val.rep 7 = 0 := by
  obtain ⟨x,hx,hne,h7⟩ := metric_line_meets_polar L
  have hs := metric_line_singular L hx
  let p := singularPointMk F x hne hs.1 hs.2
  refine ⟨p, ?_, ?_⟩
  · change (Projectivization.mk F x hne).submodule ≤ L.val
    rwa [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
  · have he : Projectivization.mk F p.val.rep p.val.rep_nonzero =
        Projectivization.mk F x hne := Projectivization.mk_rep p.val
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp he
    have hh := congrFun ha 7
    simp only [h7, Units.smul_def, Pi.smul_apply, smul_eq_mul] at hh
    simpa using hh.symm

/-- A point in the polar hyperplane gives a five-edge walk to its line. -/
theorem metric_firstPoint_line_walk (L : ZeroProductLine F) :
    ∃ w : geometryGraph.Walk (Sum.inr (firstPoint (K := F))) (Sum.inl L),
      w.length ≤ 5 := by
  obtain ⟨p,hp,h7⟩ := metric_line_has_polar_point L
  obtain ⟨w,hw⟩ := metric_firstPoint_walk_of_polar p h7
  refine ⟨w.concat (by exact hp), ?_⟩
  simp only [SimpleGraph.Walk.length_concat]
  omega

/-- Every point-line pair is joined by a walk of length at most five. -/
theorem metric_point_line_walk (p : SingularPoints F) (L : ZeroProductLine F) :
    ∃ w : geometryGraph.Walk (Sum.inr p) (Sum.inl L), w.length ≤ 5 := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  obtain ⟨w,hw⟩ := metric_firstPoint_line_walk (g • L)
  have hp : g⁻¹ • firstPoint = p := by rw [← hg, inv_smul_smul]
  refine ⟨(w.map (metricGraphIso g⁻¹).toHom).copy
    (by exact congrArg Sum.inr hp) (by exact congrArg Sum.inl (inv_smul_smul g L)), ?_⟩
  simpa using hw

/-- Diameter at most six for the exact intrinsic point-line incidence graph.
The proof applies over every field. -/
theorem geometryGraph_diameter_bound (x y : GeometryVertex F) :
    ∃ w : geometryGraph.Walk x y, w.length ≤ 6 := by
  cases x with
  | inl L =>
    cases y with
    | inl M =>
      obtain ⟨p,hp,_⟩ := metric_line_has_polar_point L
      obtain ⟨w,hw⟩ := metric_point_line_walk p M
      refine ⟨.cons (v := Sum.inr p) hp w, ?_⟩
      simp only [SimpleGraph.Walk.length_cons]
      omega
    | inr p =>
      obtain ⟨w,hw⟩ := metric_point_line_walk p L
      exact ⟨w.reverse, by simpa using hw.trans (by decide : 5 ≤ 6)⟩
  | inr p =>
    cases y with
    | inl L =>
      obtain ⟨w,hw⟩ := metric_point_line_walk p L
      exact ⟨w, hw.trans (by decide)⟩
    | inr q =>
      obtain ⟨g,hg⟩ := exists_smul_firstPoint p
      obtain ⟨w,hw⟩ := metric_firstPoint_walk (g • q)
      have hp : g⁻¹ • firstPoint = p := by rw [← hg, inv_smul_smul]
      refine ⟨(w.map (metricGraphIso g⁻¹).toHom).copy
        (by exact congrArg Sum.inr hp) (by exact congrArg Sum.inr (inv_smul_smul g q)), ?_⟩
      simpa using hw

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
