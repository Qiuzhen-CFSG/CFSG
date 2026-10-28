module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.IntrinsicGeometry
public import Theory.AtlasPort.LinearGroups.G2.PointOrbits

/-!
# Linear incidence facts for the octonion metric

A square-zero octonion is singular. Rank-nullity therefore produces a singular
point in the intersection of each zero-product plane with the polar hyperplane
of the first point. Two distinct incident points determine their line, and
mutually annihilating singular points span a line. Actual octonion automorphisms
preserve this incidence and act as graph automorphisms.

These facts prepare the intrinsic diameter and girth arguments for the split
G₂ geometry in Aschbacher--Smith, Theorem 0.1.2(1), printed pp.3--4,
and Theorem 0.1.1, printed pp.481--482. The coordinate and action APIs are
those of the licensed ATLAS port; the proofs here use linear algebra directly.
-/

@[expose] public section

open Atlas.G2 Atlas.SplitOctonion
namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {F : Type*} [Field F]

/-- A square-zero octonion is singular. -/
theorem metric_singular_of_square_zero {x : Carrier F} (hx : mul x x = 0) :
    trace x = 0 ∧ norm x = 0 := by
  have hn : norm x = 0 := by
    have hh := norm_mul x x
    rw [hx] at hh
    have hz : norm (0 : Carrier F) = 0 := by simp [norm]
    rw [hz] at hh
    exact mul_self_eq_zero.mp hh.symm
  refine ⟨?_, hn⟩
  by_cases hzero : x = 0
  · simp [hzero, trace]
  have hq := quadratic_identity x
  rw [hx, hn, zero_smul, add_zero, zero_sub, neg_eq_zero] at hq
  exact (smul_eq_zero.mp hq).resolve_right hzero

/-- Every vector in a geometric line is singular, as follows from its square. -/
theorem metric_line_singular (L : ZeroProductLine F) {x : Carrier F} (hx : x ∈ L.val) :
    trace x = 0 ∧ norm x = 0 :=
  metric_singular_of_square_zero (L.property.2 x hx x hx)

/-- Every geometric line meets the polar hyperplane of the first point. -/
theorem metric_line_meets_polar (L : ZeroProductLine F) :
    ∃ x : Carrier F, x ∈ L.val ∧ x ≠ 0 ∧ x 7 = 0 := by
  let e : L.val →ₗ[F] F := (LinearMap.proj 7).comp L.val.subtype
  have hk : LinearMap.ker e ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_self, L.property.1]
    decide)
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨x.val, x.property, ?_, ?_⟩
  · intro h
    apply hne
    exact Subtype.ext h
  · exact hx

/-- An octonion automorphism preserves point-line incidence. -/
theorem metric_smul_pointOnLine (g : Model F) {p : SingularPoints F}
    {L : ZeroProductLine F} (h : pointOnLine p L) : pointOnLine (g • p) (g • L) := by
  rw [← singularPointMk_rep F p, singularPointMk_smul]
  change (Projectivization.mk F (g.val p.val.rep) _).submodule ≤
    L.val.map g.val.toLinearMap
  rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
  exact ⟨p.val.rep, (pointOnLine_iff p L).mp h, rfl⟩

theorem metric_smul_adj (g : Model F) {x y : GeometryVertex F}
    (h : geometryGraph.Adj x y) : geometryGraph.Adj (g • x) (g • y) := by
  cases x <;> cases y
  · exact h
  · exact metric_smul_pointOnLine g h
  · exact metric_smul_pointOnLine g h
  · exact h

/-- The actual linear action, as an automorphism of the intrinsic graph. -/
def metricGraphIso (g : Model F) : geometryGraph (F := F) ≃g geometryGraph (F := F) where
  toEquiv :=
    { toFun := fun x => g • x
      invFun := fun x => g⁻¹ • x
      left_inv := inv_smul_smul g
      right_inv := smul_inv_smul g }
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have hh := metric_smul_adj g⁻¹ h
      simpa using hh
    · exact metric_smul_adj g

/-- A singular point squares to zero. -/
theorem metric_point_square_zero (p : SingularPoints F) : mul p.val.rep p.val.rep = 0 := by
  have h := quadratic_identity p.val.rep
  simpa [p.property.1, p.property.2] using h

private theorem metric_finrank_span_pair {p q : SingularPoints F} (hpq : p ≠ q) :
    Module.finrank F (Submodule.span F {p.val.rep, q.val.rep}) = 2 := by
  have hi : LinearIndependent F ![p.val.rep, q.val.rep] :=
    Projectivization.linearIndependent_pair_iff_ne.mpr (fun h => hpq (Subtype.ext h))
  have hr : Set.range (![p.val.rep, q.val.rep] : Fin 2 → Carrier F) =
      {p.val.rep, q.val.rep} := by
    ext x
    simp [or_comm]
  have h := finrank_span_eq_card hi
  change Module.finrank F (Submodule.span F (Set.range ![p.val.rep, q.val.rep])) = 2 at h
  rw [hr] at h
  exact h

/-- Two distinct points determine any geometric line that contains them. -/
theorem metric_line_eq_span {p q : SingularPoints F} (hpq : p ≠ q)
    {L : ZeroProductLine F} (hp : pointOnLine p L) (hq : pointOnLine q L) :
    L.val = Submodule.span F {p.val.rep, q.val.rep} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact (pointOnLine_iff p L).mp hp
    · exact (pointOnLine_iff q L).mp hq
  · rw [metric_finrank_span_pair hpq, L.property.1]

theorem metric_line_unique {p q : SingularPoints F} (hpq : p ≠ q)
    {L M : ZeroProductLine F} (hpL : pointOnLine p L) (hqL : pointOnLine q L)
    (hpM : pointOnLine p M) (hqM : pointOnLine q M) : L = M := by
  apply Subtype.ext
  rw [metric_line_eq_span hpq hpL hqL, metric_line_eq_span hpq hpM hqM]

/-- Distinct singular points annihilating each other span a geometric line. -/
theorem metric_line_of_zero_products {p q : SingularPoints F} (hpq : p ≠ q)
    (hl : mul p.val.rep q.val.rep = 0) (hr : mul q.val.rep p.val.rep = 0) :
    ∃ L : ZeroProductLine F, pointOnLine p L ∧ pointOnLine q L := by
  have hplane : IsZeroProductLine (Submodule.span F {p.val.rep, q.val.rep}) := by
    refine ⟨metric_finrank_span_pair hpq, ?_⟩
    intro x hx y hy
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [SplitOctonion.add_mul, SplitOctonion.mul_add, SplitOctonion.smul_mul,
      SplitOctonion.mul_smul, hl, hr, metric_point_square_zero, smul_zero, add_zero]
  let L : ZeroProductLine F := ⟨_, hplane⟩
  refine ⟨L, (pointOnLine_iff p L).mpr ?_, (pointOnLine_iff q L).mpr ?_⟩
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
