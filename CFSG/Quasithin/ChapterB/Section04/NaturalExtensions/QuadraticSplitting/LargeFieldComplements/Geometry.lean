module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Coordinates
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Displacement
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Hyperplane

/-!
# Quotient geometry for the larger-field complement

In the actual quotient coordinates, the axis group consists of all shears
with parameter in the coordinate hyperplane. The orbit of the unit vector
is free and its displacements cover that hyperplane. Consequently the
upstairs displacement space is disjoint from the original natural submodule
and maps onto the quotient axis. The recorded Levi normalizes the full axis
group, hence preserves the displacement space of a fixed lift.

These calculations work in every dimension and field degree, including F₄.
They are the common geometric step of Aschbacher–Smith B.4.9(1), printed
pp.93–94. Both orientations use the same literal quotient maps.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ} (m : QuotientCoordinates d) (j : Fin n)

namespace QuotientCoordinates

theorem largeField_mem_axis (z : V ⧸ d.space.toSubmodule) :
    z ∈ m.axis j ↔ m.action.linearEquiv z j = 0 := Iff.rfl

theorem largeField_mem_line (z : V ⧸ d.space.toSubmodule) :
    z ∈ m.line j ↔ ∃ c : F.Carrier,
      c • (Pi.single j 1 : Fin n → F.Carrier) = m.action.linearEquiv z := by
  change m.action.linearEquiv z ∈ Submodule.span F.Carrier {Pi.single j 1} ↔ _
  exact Submodule.mem_span_singleton

theorem largeField_axis_isCompl_line : IsCompl (m.axis j) (m.line j) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro z hI hL
    obtain ⟨c, hc⟩ := (m.largeField_mem_line j z).mp hL
    have hc0 : c = 0 := by
      have h := congrFun hc j
      simpa only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        (m.largeField_mem_axis j z).mp hI] using h
    apply m.action.linearEquiv.injective
    rw [map_zero, ← hc, hc0, zero_smul]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro z _
    let c := m.action.linearEquiv z j
    let l := m.action.linearEquiv.symm (c • (Pi.single j 1 : Fin n → F.Carrier))
    have hl : l ∈ m.line j := by
      apply (m.largeField_mem_line j l).mpr
      exact ⟨c, (m.action.linearEquiv.apply_symm_apply _).symm⟩
    have hi : z - l ∈ m.axis j := by
      apply (m.largeField_mem_axis j _).mpr
      rw [map_sub]
      change m.action.linearEquiv z j -
        m.action.linearEquiv (m.action.linearEquiv.symm (c • Pi.single j 1)) j = 0
      rw [m.action.linearEquiv.apply_symm_apply]
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      exact sub_self c
    exact Submodule.mem_sup.mpr ⟨z - l, hi, l, hl, sub_add_cancel _ _⟩

theorem largeField_mem_Q (g : G) : g ∈ m.Q j ↔
    m.action.groupEquiv g ∈ hyperplaneCentralizer F n j := by
  constructor
  · intro hg
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro z hz
    let u := m.action.linearEquiv.symm z
    have hu : u ∈ m.axis j := by
      apply (m.largeField_mem_axis j u).mpr
      change z j = 0 at hz
      simpa only [u, LinearEquiv.apply_symm_apply] using hz
    have hh := congrArg m.action.linearEquiv (hg.2 u hu)
    rw [m.action.intertwines] at hh
    simpa only [u, LinearEquiv.apply_symm_apply] using hh
  · intro hg
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro z hz
    apply m.action.linearEquiv.injective
    rw [m.action.intertwines]
    exact hg.2 _ hz

theorem largeField_quotient_displacement (x : m.Q j) :
    ∃ w : coordinateHyperplane F n j,
      m.action.groupEquiv x = shear F n j w ∧
      m.action.linearEquiv
        (d.space.quotientRepresentation x (m.lineVector j) - m.lineVector j) = w := by
  obtain ⟨w, hw⟩ := centralizer_eq_shear F n j
    ((m.largeField_mem_Q j x).mp x.property)
  refine ⟨w, hw.symm, ?_⟩
  rw [map_sub, m.action.intertwines, ← hw]
  unfold lineVector
  rw [m.action.linearEquiv.apply_symm_apply, shear_apply]
  simp only [Pi.single_eq_same, one_smul, add_sub_cancel_left]

theorem largeField_quotient_free (x : m.Q j)
    (h : d.space.quotientRepresentation x (m.lineVector j) = m.lineVector j) :
    (x : G) = 1 := by
  obtain ⟨w, hw, he⟩ := m.largeField_quotient_displacement j x
  have hw0 : w = 0 := by
    apply Subtype.ext
    change (w : Fin n → F.Carrier) = 0
    simpa only [h, sub_self, map_zero] using he.symm
  apply m.action.groupEquiv.injective
  rw [hw, hw0, shear_zero, map_one]

theorem largeField_quotient_displacement_range :
    ∀ z ∈ m.axis j, ∃ x : m.Q j,
      d.space.quotientRepresentation x (m.lineVector j) - m.lineVector j = z := by
  intro z hz
  let w : coordinateHyperplane F n j := ⟨m.action.linearEquiv z, hz⟩
  let g := m.action.groupEquiv.symm (shear F n j w)
  have hg : g ∈ m.Q j := by
    apply (m.largeField_mem_Q j g).mpr
    dsimp [g]
    rw [m.action.groupEquiv.apply_symm_apply]
    exact shear_mem F n j w
  refine ⟨⟨g, hg⟩, ?_⟩
  apply m.action.linearEquiv.injective
  rw [map_sub, m.action.intertwines]
  change linearNatural F n (m.action.groupEquiv g)
    (m.action.linearEquiv (m.lineVector j)) -
      m.action.linearEquiv (m.lineVector j) = m.action.linearEquiv z
  dsimp [g, lineVector]
  rw [m.action.groupEquiv.apply_symm_apply, m.action.linearEquiv.apply_symm_apply,
    shear_apply]
  simp only [Pi.single_eq_same, one_smul, add_sub_cancel_left]
  rfl

theorem largeField_K_normalizes_Q :
    ∀ k ∈ m.K j, ∀ x ∈ m.Q j, k * x * k⁻¹ ∈ m.Q j := by
  intro k hk x hx
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro z hz
  have hk' := (m.K j).inv_mem hk
  have hi : d.space.quotientRepresentation k⁻¹ z ∈ m.axis j :=
    (hk'.1 z).mpr hz
  change d.space.quotientRepresentation (k * x * k⁻¹) z = z
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx.2 _ hi]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem largeField_map_displacement (v : V)
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) (x : m.Q j) :
    d.space.toSubmodule.mkQ (ρ x v - v) =
      d.space.quotientRepresentation x (m.lineVector j) - m.lineVector j := by
  rw [map_sub]
  change d.space.quotientRepresentation x (d.space.toSubmodule.mkQ v) -
    d.space.toSubmodule.mkQ v = _
  rw [hv]

theorem largeField_displacement_disjoint
    (hq : IsQuadratic ρ (m.Q j)) (v : V)
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    Disjoint d.space.toSubmodule (displacementSpace ρ (m.Q j) hq v) := by
  apply Submodule.disjoint_def.mpr
  intro w hw hW
  obtain ⟨x, rfl⟩ := (mem_displacementSpace ρ (m.Q j) hq v w).mp hW
  have hz : d.space.toSubmodule.mkQ (ρ x v - v) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hw
  rw [m.largeField_map_displacement j v hv x] at hz
  have hx := m.largeField_quotient_free j x (sub_eq_zero.mp hz)
  simp only [hx, map_one, Module.End.one_apply, sub_self]

theorem largeField_displacement_map
    (hq : IsQuadratic ρ (m.Q j)) (v : V)
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    (displacementSpace ρ (m.Q j) hq v).map d.space.toSubmodule.mkQ = m.axis j := by
  apply le_antisymm
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨x, rfl⟩ := (mem_displacementSpace ρ (m.Q j) hq v w).mp hw
    rw [m.largeField_map_displacement j v hv x]
    apply (m.largeField_mem_axis j _).mpr
    obtain ⟨u, _, hu⟩ := m.largeField_quotient_displacement j x
    rw [hu]
    exact u.property
  · intro z hz
    obtain ⟨x, hx⟩ := m.largeField_quotient_displacement_range j z hz
    refine ⟨ρ x v - v, (mem_displacementSpace ρ (m.Q j) hq v _).mpr ⟨x, rfl⟩, ?_⟩
    exact (m.largeField_map_displacement j v hv x).trans hx

theorem largeField_displacement_stable
    (hq : IsQuadratic ρ (m.Q j)) (v : V) (hv : v ∈ fixedSpace ρ (m.K j)) :
    m.K j ≤ subspaceStabilizer ρ (displacementSpace ρ (m.Q j) hq v) := by
  apply le_subspaceStabilizer
  apply displacementSpace_invariant ρ (m.Q j) hq v (m.K j)
    (m.largeField_K_normalizes_Q j)
  exact fun k hk => hv ⟨k, hk⟩

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
