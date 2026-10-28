module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Coordinates
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Hyperplane

/-!
# Geometry of the marked quotient axis in B.4.9(1)

The coordinate axis group is identified with the actual hyperplane shears.
Its nontrivial elements fix precisely the axis, and its action on the
complementary unit vector is free. Over the binary prime field, that vector
and one shear displacement cover every quotient vector. The special-linear
Levi normalizes the axis group; their join is exactly the subgroup fixing
the coordinate covector, including its scale.

These calculations concern the literal quotient of `DoubleNatural` and work
for either recorded orientation. They do not assume upstairs quadraticity
or fixed lifts. Choosing the marking from a given four-group, conjugate
generation, and Sylow placement are separate geometric obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(1),
printed pp.92–93. The shear calculation is reused from Chapter K's
`Linear.Natural.Hyperplane`.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ}
namespace QuotientCoordinates
variable (m : QuotientCoordinates d) (j : Fin n)

/-- Membership in the original quotient axis is coordinate vanishing. -/
@[simp] theorem mem_axis_iff (z : V ⧸ d.space.toSubmodule) :
    z ∈ m.axis j ↔ m.action.linearEquiv z j = 0 := Iff.rfl

/-- The given actor marking identifies the two pointwise centralizers. -/
@[simp] theorem mem_Q_iff (g : G) :
    g ∈ m.Q j ↔ m.action.groupEquiv g ∈ hyperplaneCentralizer F n j := by
  constructor
  · intro hg
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    have hfix := hg.2 (m.action.linearEquiv.symm v) (by
      rw [mem_axis_iff, LinearEquiv.apply_symm_apply]
      exact hv)
    have h := congrArg m.action.linearEquiv hfix
    simpa only [m.action.intertwines, LinearEquiv.apply_symm_apply] using h
  · intro hg
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    apply m.action.linearEquiv.injective
    rw [m.action.intertwines]
    exact hg.2 _ hv

/-- The marked axis group is the literal matrix hyperplane centralizer. -/
noncomputable def axisGroupEquiv : m.Q j ≃* hyperplaneCentralizer F n j where
  toFun g := ⟨m.action.groupEquiv g, (m.mem_Q_iff j g).mp g.property⟩
  invFun g := ⟨m.action.groupEquiv.symm g, (m.mem_Q_iff j _).mpr (by
    simpa only [MulEquiv.apply_symm_apply] using g.property)⟩
  left_inv g := Subtype.ext (m.action.groupEquiv.symm_apply_apply g)
  right_inv g := Subtype.ext (m.action.groupEquiv.apply_symm_apply g)
  map_mul' g h := Subtype.ext (m.action.groupEquiv.map_mul g h)

/-- An actual group element, transported from a shear by the recorded marking. -/
noncomputable def axisShear (w : coordinateHyperplane F n j) : G :=
  m.action.groupEquiv.symm (shear F n j w)

@[simp] theorem axisShear_mem (w : coordinateHyperplane F n j) :
    m.axisShear j w ∈ m.Q j := by
  rw [m.mem_Q_iff]
  exact (m.action.groupEquiv.apply_symm_apply _).symm ▸ shear_mem F n j w

theorem axisShear_apply (w : coordinateHyperplane F n j)
    (z : V ⧸ d.space.toSubmodule) :
    m.action.linearEquiv (d.space.quotientRepresentation (m.axisShear j w) z) =
      m.action.linearEquiv z + m.action.linearEquiv z j • w.val := by
  rw [m.action.intertwines]
  simp only [axisShear, MulEquiv.apply_symm_apply, shear_apply]

theorem exists_axisShear (g : m.Q j) :
    ∃ w : coordinateHyperplane F n j, m.axisShear j w = (g : G) := by
  obtain ⟨w, hw⟩ := centralizer_eq_shear F n j ((m.mem_Q_iff j _).mp g.property)
  exact ⟨w, m.action.groupEquiv.injective (by
    change m.action.groupEquiv (m.action.groupEquiv.symm _) = _
    rwa [MulEquiv.apply_symm_apply])⟩

@[simp] theorem axisShear_zero : m.axisShear j 0 = 1 := by
  simp only [axisShear, shear_zero, map_one]

@[simp] theorem lineVector_coordinates :
    m.action.linearEquiv (m.lineVector j) = Pi.single j (1 : F.Carrier) :=
  m.action.linearEquiv.apply_symm_apply _

/-- The unit quotient vector has trivial stabilizer in the full axis group. -/
theorem lineVector_free (x : m.Q j)
    (hx : d.space.quotientRepresentation x (m.lineVector j) = m.lineVector j) :
    (x : G) = 1 := by
  obtain ⟨w, hw⟩ := m.exists_axisShear j x
  have he := congrArg m.action.linearEquiv hx
  rw [← hw, m.axisShear_apply, m.lineVector_coordinates, Pi.single_eq_same, one_smul] at he
  have hw0 : w = 0 := Subtype.ext (add_left_cancel (he.trans (add_zero _).symm))
  rw [← hw, hw0, m.axisShear_zero]

/-- In dimension at least two, the full axis group fixes exactly its axis. -/
theorem fixedSpace_Q (hn : 2 ≤ n) :
    fixedSpace d.space.quotientRepresentation (m.Q j) = m.axis j := by
  apply le_antisymm
  · intro z hz
    have hm : m.action.linearEquiv z ∈
        fixedSpace (linearNatural F n) (hyperplaneCentralizer F n j) := by
      intro a
      have h := hz ((m.axisGroupEquiv j).symm a)
      have he := congrArg m.action.linearEquiv h
      change m.action.linearEquiv (d.space.quotientRepresentation
        (m.action.groupEquiv.symm a) z) = m.action.linearEquiv z at he
      rw [m.action.intertwines, MulEquiv.apply_symm_apply] at he
      exact he
    rw [subgroup_fixedSpace F n j le_rfl (hyperplaneCentralizer_elementary F n j hn).1] at hm
    exact hm
  · intro z hz a
    exact a.property.2 z hz

theorem lineVector_not_fixed (hn : 2 ≤ n) :
    m.lineVector j ∉ fixedSpace d.space.quotientRepresentation (m.Q j) := by
  rw [m.fixedSpace_Q j hn, m.mem_axis_iff, m.lineVector_coordinates, Pi.single_eq_same]
  exact one_ne_zero

/-- Relative normalization by the literal Levi, not normality in G. -/
theorem K_normalizes_Q :
    ∀ k ∈ m.K j, ∀ x ∈ m.Q j, k * x * k⁻¹ ∈ m.Q j := by
  intro k hk x hx
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro v hv
  have hi : d.space.quotientRepresentation k⁻¹ v ∈ m.axis j :=
    ((m.K j).inv_mem hk).1 v |>.mpr hv
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx.2 _ hi,
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The three-term quotient decomposition used in the binary complement. -/
theorem binary_lineVector_cover (hF : F.degree = 1)
    (z : V ⧸ d.space.toSubmodule) :
    ∃ c : ZMod 2, ∃ x : m.Q j,
      z = c • m.lineVector j +
        (d.space.quotientRepresentation x (m.lineVector j) - m.lineVector j) := by
  have hs : Function.Surjective (algebraMap (ZMod 2) F.Carrier) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp ((field_finrank F).trans hF)).2
  obtain ⟨c, hc⟩ := hs (m.action.linearEquiv z j)
  let w : coordinateHyperplane F n j :=
    ⟨m.action.linearEquiv z - m.action.linearEquiv z j • Pi.single j 1, by
      change m.action.linearEquiv z j - m.action.linearEquiv z j * (Pi.single j 1 : Fin n → F.Carrier) j = 0
      simp⟩
  refine ⟨c, ⟨m.axisShear j w, m.axisShear_mem j w⟩, ?_⟩
  apply m.action.linearEquiv.injective
  rw [map_add, map_smul, map_sub, m.axisShear_apply, m.lineVector_coordinates,
    Pi.single_eq_same, one_smul, add_sub_cancel_left]
  have hscalar : c • (Pi.single j 1 : Fin n → F.Carrier) =
      m.action.linearEquiv z j • Pi.single j 1 := by
    ext i
    simp [Algebra.smul_def, hc]
  rw [hscalar]
  exact (add_sub_cancel _ _).symm


/-- The subgroup fixing the coordinate functional, including its scale. -/
def coordinateFixer : Subgroup G where
  carrier := {g | ∀ v : Fin n → F.Carrier,
    linearNatural F n (m.action.groupEquiv g) v j = v j}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro g h hg hh v
    simp only [map_mul, Module.End.mul_apply]
    exact (hg _).trans (hh v)
  inv_mem' := by
    intro g hg v
    have h := hg (linearNatural F n (m.action.groupEquiv g⁻¹) v)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] using h.symm

/-- A coordinate-functional fixer fixing its complementary unit vector is
exactly an element of the specified Levi subgroup. -/
theorem mem_K_of_coordinateFixer {g : G} (hg : g ∈ m.coordinateFixer j)
    (he : linearNatural F n (m.action.groupEquiv g) (Pi.single j 1) = Pi.single j 1) :
    g ∈ m.K j := by
  constructor
  · intro v
    change m.action.linearEquiv (d.space.quotientRepresentation g v) j = 0 ↔
      m.action.linearEquiv v j = 0
    rw [m.action.intertwines, hg]
  · refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    change m.action.linearEquiv v ∈ Submodule.span F.Carrier {Pi.single j 1} at hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    apply m.action.linearEquiv.injective
    rw [m.action.intertwines, ← hc]
    change specialLinearNatural n _ (c • Pi.single j 1) = c • Pi.single j 1
    rw [map_smul]
    change c • linearNatural F n _ (Pi.single j 1) = c • Pi.single j 1
    rw [he]

theorem Q_le_coordinateFixer : m.Q j ≤ m.coordinateFixer j := by
  intro g hg v
  obtain ⟨w, hw⟩ := m.exists_axisShear j ⟨g, hg⟩
  change m.axisShear j w = g at hw
  rw [← hw]
  change linearNatural F n (m.action.groupEquiv (m.action.groupEquiv.symm _)) v j = _
  rw [MulEquiv.apply_symm_apply, shear_apply]
  change v j + v j * w.val j = v j
  rw [show w.val j = 0 from w.property, mul_zero, add_zero]

theorem K_le_coordinateFixer : m.K j ≤ m.coordinateFixer j := by
  intro g hg v
  let e : Fin n → F.Carrier := Pi.single j 1
  have he : linearNatural F n (m.action.groupEquiv g) e = e := by
    have hv : m.lineVector j ∈ m.line j := by
      change m.action.linearEquiv (m.lineVector j) ∈ Submodule.span F.Carrier {e}
      rw [m.lineVector_coordinates]
      exact Submodule.subset_span (Set.mem_singleton e)
    have h := congrArg m.action.linearEquiv (hg.2.2 _ hv)
    rw [m.action.intertwines, m.lineVector_coordinates] at h
    exact h
  have haxis : m.action.linearEquiv.symm (v - v j • e) ∈ m.axis j := by
    rw [m.mem_axis_iff, LinearEquiv.apply_symm_apply]
    change v j - v j * (Pi.single j 1 : Fin n → F.Carrier) j = 0
    simp
  have h := (hg.1 _).mpr haxis
  rw [m.mem_axis_iff, m.action.intertwines, LinearEquiv.apply_symm_apply] at h
  change specialLinearNatural n _ (v - v j • e) j = 0 at h
  rw [map_sub, map_smul] at h
  change linearNatural F n (m.action.groupEquiv g) v j -
    v j * linearNatural F n (m.action.groupEquiv g) e j = 0 at h
  rw [he] at h
  simpa only [e, Pi.single_eq_same, mul_one] using sub_eq_zero.mp h

/-- The source's KQ is the literal stabilizer of a nonzero covector.
This characterization supports its Sylow placement via the odd covector orbit. -/
theorem K_sup_Q_eq_coordinateFixer : m.K j ⊔ m.Q j = m.coordinateFixer j := by
  apply le_antisymm (sup_le (m.K_le_coordinateFixer j) (m.Q_le_coordinateFixer j))
  intro g hg
  let e : Fin n → F.Carrier := Pi.single j 1
  let w : coordinateHyperplane F n j :=
    ⟨linearNatural F n (m.action.groupEquiv g) e - e, by
      change linearNatural F n (m.action.groupEquiv g) e j - e j = 0
      rw [hg e, sub_self]⟩
  let q := m.axisShear j w
  let k := q⁻¹ * g
  have hqQ : q ∈ m.Q j := m.axisShear_mem j w
  have hq : linearNatural F n (m.action.groupEquiv q) e =
      linearNatural F n (m.action.groupEquiv g) e := by
    change linearNatural F n (m.action.groupEquiv (m.action.groupEquiv.symm _)) e = _
    rw [MulEquiv.apply_symm_apply, shear_apply]
    simp only [e, Pi.single_eq_same, one_smul]
    exact add_sub_cancel _ _
  have hk : k ∈ m.K j := by
    apply m.mem_K_of_coordinateFixer j
      ((m.coordinateFixer j).mul_mem ((m.coordinateFixer j).inv_mem
        (m.Q_le_coordinateFixer j hqQ)) hg)
    change linearNatural F n (m.action.groupEquiv (q⁻¹ * g)) e = e
    rw [map_mul, map_mul, Module.End.mul_apply, ← hq,
      ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one]
    simp only [map_one, Module.End.one_apply]
  have h : q * k ∈ m.K j ⊔ m.Q j :=
    (m.K j ⊔ m.Q j).mul_mem (Subgroup.mem_sup_right hqQ) (Subgroup.mem_sup_left hk)
  simpa only [k, mul_inv_cancel_left] using h

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
