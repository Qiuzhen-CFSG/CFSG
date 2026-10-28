module

public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Defs
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Cosets
public import Theory.GroupTheory.ElementaryThompsonInvolutionFusion
public import Theory.Mathieu.M24.Properties.Order

/-!
# Plane markers and the elementary Thompson subgroup

The abelian elementary Thompson subgroup controls fusion into itself. Together
with M=N_G(E), this proves AS91 (6.1) for the actual left cosets: a plane
marker belongs to a point radical exactly when that point lies on the plane.
No ambient conjugate-core uniqueness is assumed.

The same equivalence proves that each radical fixes its incident planes.
Containment E≤S≤N_G(Z) gives fixation of incident lines. Since the line
stabilizer normalizes Z≤E, every point on a line lies on every plane through
that line. Plane markers identify the planes through the base line with
Z minus its identity; the kernel of this literal action is S=C_G(Z).
This distinguishes it from the five-point action, whose kernel is K.

The original consumer's simplicity, when supplied, makes M proper and its
coset action faithful. No generation or source simplicity theorem is claimed.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.1)(1), (5.2)(1),
(6.1), pp.599–602, DOI 10.1007/BF01232280.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open LocalGeometry LocalGeometry.LocalSubgroups SourceRecognition
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}

namespace LocalData
variable {h : IsTypeJ4 z} (a : LocalData h)
open SourceCycleBase GraphUniquenessSystem

 theorem marker_mem_E : z ∈ a.P.E := by
  exact ⟨_, a.marker_vector⟩

theorem controls_marker_fusion {u : G} (hu : u ∈ a.P.E) (hc : IsConj z u) :
    ∃ m ∈ a.P.M, MulAut.conj m z = u := by
  let := a.P.E_elementary
  have : IsMulCommutative (Stellmacher.elementaryAbelianMaxJ (a.T : Subgroup G)) := by
    rw [← a.E_eq_maxJ]
    infer_instance
  obtain ⟨m, hm, he⟩ := Stellmacher.abelian_maxJ_controls_element_fusion a.T
    (a.E_eq_maxJ ▸ a.marker_mem_E) (a.E_eq_maxJ ▸ hu) hc
  rw [← a.E_eq_maxJ, a.point_normalizer] at hm
  exact ⟨m, hm, he⟩

omit [Finite G] in
/-- Equality of plane markers is equality of the original centralizer cosets. -/
theorem marker_injective : Function.Injective (marker (z := z)) := by
  intro π σ he
  induction π using QuotientGroup.induction_on with
  | H g =>
    induction σ using QuotientGroup.induction_on with
    | H k =>
      change marker (Cosets.vertex (centralizer z) g) = marker (Cosets.vertex (centralizer z) k) at he
      rw [marker_vertex, marker_vertex] at he
      apply (Cosets.vertex_eq_iff (centralizer z) g k).mpr
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (fun u => g⁻¹ * u * k) he
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh.symm

theorem marker_mem_core_base (π : Plane z) :
    marker π ∈ coreAt a.P (Cosets.vertex a.P.M 1) ↔
      OnPlane a.P (Cosets.vertex a.P.M 1) π := by
  have hb : coreAt a.P (Cosets.vertex a.P.M 1) = a.P.E := by
    rw [coreAt_vertex]
    ext v
    simp
  rw [hb]
  constructor
  · intro hmem
    have hc : IsConj z (marker π) := by
      exact isConj_iff.mpr ⟨representative π, rfl⟩
    obtain ⟨m, hm, he⟩ := a.controls_marker_fusion hmem hc
    refine ⟨m, (Cosets.vertex_eq_base a.P.M m).mpr hm, ?_⟩
    apply marker_injective
    rw [marker_vertex]
    exact he
  · rintro ⟨m, hm, rfl⟩
    rw [marker_vertex]
    have hnorm : m ∈ normalizer (a.P.E : Set G) := by
      rw [a.point_normalizer]
      exact (Cosets.vertex_eq_base a.P.M m).mp hm
    exact (mem_normalizer_iff.mp hnorm z).mp a.marker_mem_E

/-- AS91 (6.1), with the unchanged left-coset and conjugate-radical conventions. -/
theorem marker_mem_core (π : Plane z) (x : Point a.P) :
    marker π ∈ coreAt a.P x ↔ OnPlane a.P x π := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    change marker π ∈ coreAt a.P (Cosets.vertex a.P.M g) ↔
      OnPlane a.P (Cosets.vertex a.P.M g) π
    have hm : marker (g⁻¹ • π) ∈ coreAt a.P (Cosets.vertex a.P.M 1) ↔
        marker π ∈ coreAt a.P (Cosets.vertex a.P.M g) := by
      rw [marker_smul, coreAt_vertex, coreAt_vertex]
      simp only [inv_one, MulAut.conj_apply,
        mem_comap, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        one_mul, mul_one]
    rw [← hm, a.marker_mem_core_base]
    have hi := incident_smul_iff (Cosets.vertex a.P.M g) π g⁻¹
    simpa only [Cosets.smul_vertex, inv_mul_cancel, OnPlane] using hi

/-- The Todd radical fixes each incident plane, now deduced from (6.1). -/
theorem core_fixes_planes (x : Point a.P) (u : coreAt a.P x) (π : Plane z)
    (hπ : OnPlane a.P x π) : (u : G) • π = π := by
  apply marker_injective
  rw [marker_smul]
  have hmem := (a.marker_mem_core π x).mpr hπ
  have hc : Commute (u : G) (marker π) := by
    let := a.P.E_elementary
    let : IsMulCommutative (coreAt a.P x) := by
      rw [← vertex_representative x, coreAt_vertex]
      exact a.P.E.comap_injective_isMulCommutative
        (MulAut.conj (representative x)⁻¹).injective
    exact ((Commute.all u ⟨marker π, hmem⟩).map (coreAt a.P x).subtype)
  exact mul_inv_eq_iff_eq_mul.mpr hc.eq


theorem E_le_line : a.P.E ≤ a.L.G₂ := by
  rw [a.line_normalizer]
  exact a.E_le_S.trans (Subgroup.centralizer_le_normalizer _)

/-- The radical fixes all lines through its point under the literal left action. -/
theorem core_fixes_lines (x : Point a.P) (u : coreAt a.P x) (l : Line a.L)
    (hl : OnLine a.L x l) : (u : G) • l = l := by
  obtain ⟨g, hx, rfl⟩ := hl
  apply MulAction.mem_stabilizer_iff.mp
  rw [Cosets.stabilizer_vertex]
  apply Subgroup.comap_mono a.E_le_line
  rw [← coreAt_vertex, hx]
  exact u.property


/-- AS91 (5.2)(1), the string condition. A line normalizes the original
three-space, so its plane markers lie in every incident point radical. -/
theorem string (x : Point a.P) (l : Line a.L) (π : Plane z)
    (hx : OnLine a.L x l) (hπ : LineOnPlane a.L l π) : OnPlane a.P x π := by
  obtain ⟨g, rfl, hg⟩ := hx
  obtain ⟨k, hk, rfl⟩ := hπ
  have hn : g⁻¹ * k ∈ normalizer (a.d.space : Set G) := by
    rw [← a.line_normalizer]
    exact (Cosets.vertex_eq_iff a.L.G₂ g k).mp (hg.trans hk.symm)
  have hz : z ∈ a.d.space := (a.d.markedPoint 0).property
  have he := a.space_le_E ((mem_normalizer_iff.mp hn z).mp hz)
  apply (a.marker_mem_core _ _).mp
  rw [marker_vertex, coreAt_vertex]
  change g⁻¹ * (k * z * k⁻¹) * (g⁻¹)⁻¹ ∈ a.P.E
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using he

/-- Every plane marker is a nonidentity conjugate of the original involution. -/
theorem marker_ne_one (ht : IsTypeJ4 z) (π : Plane z) : marker π ≠ 1 := by
  intro he
  have hz : z = 1 := (MulAut.conj (representative π)).injective
    (he.trans (map_one _).symm)
  have ho := ht.involution
  rw [hz, orderOf_one] at ho
  norm_num at ho

/-- The seven plane markers on the original line are exactly the nonzero
members of the original three-space. -/
theorem line_plane_marker (π : Plane z) :
    LineOnPlane a.L (Cosets.vertex a.L.G₂ 1) π ↔ marker π ∈ a.d.space := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hn : g ∈ normalizer (a.d.space : Set G) := by
      rw [← a.line_normalizer]
      exact (Cosets.vertex_eq_base a.L.G₂ g).mp hg
    rw [marker_vertex]
    exact (mem_normalizer_iff.mp hn z).mp (a.d.markedPoint 0).property
  · intro hv
    obtain ⟨g, hg, he⟩ := a.d.normalizer_transitive (marker π) hv (marker_ne_one h π)
    refine ⟨g, (Cosets.vertex_eq_base a.L.G₂ g).mpr (a.line_normalizer ▸ hg), ?_⟩
    apply marker_injective
    rw [marker_vertex]
    exact he

/-- The kernel of the actual seven-plane action is S=C_G(Z), not K.
This uses the literal plane cosets and their markers, rather than an
abstract quotient isomorphism. -/
theorem plane_action_kernel (g : a.L.G₂) :
    (∀ π : Plane z, LineOnPlane a.L (Cosets.vertex a.L.G₂ 1) π →
      (g : G) • π = π) ↔ (g : G) ∈ a.d.S := by
  constructor
  · intro hg t ht
    by_cases ht1 : t = 1
    · simp [ht1]
    obtain ⟨n, hn, he⟩ := a.d.normalizer_transitive t ht ht1
    have hπ : LineOnPlane a.L (Cosets.vertex a.L.G₂ 1)
        (Cosets.vertex (centralizer z) n) := by
      apply (a.line_plane_marker _).mpr
      rwa [marker_vertex, he]
    have hh := congrArg marker (hg _ hπ)
    rw [marker_smul, marker_vertex, he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hg π hπ
    apply marker_injective
    rw [marker_smul]
    exact mul_inv_eq_iff_eq_mul.mpr (hg (marker π) ((a.line_plane_marker π).mp hπ)).symm

/-- The full marked Mathieu quotient, retained as an actual surjection. -/
theorem projection_surjective : Function.Surjective a.P.projection := by
  intro g
  refine ⟨a.P.toddEquiv (SemidirectProduct.inr g), ?_⟩
  simp [PointData.projection]

theorem E_ne_point : a.P.E ≠ a.P.M := by
  intro he
  have hk : a.P.projection.ker = ⊤ := by
    rw [a.P.projection_ker, he, subgroupOf_self]
  have : Nontrivial M24 := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [m24_order]
    norm_num)
  obtain ⟨g, hg⟩ := exists_ne (1 : M24)
  obtain ⟨m, hm⟩ := a.projection_surjective g
  have hmem : m ∈ a.P.projection.ker := by rw [hk]; trivial
  exact hg (hm.symm.trans hmem)

/-- Use the actual consumer's simplicity to prove properness of the point group. -/
theorem point_ne_top [IsSimpleGroup G] : a.P.M ≠ ⊤ := by
  intro htop
  have hn : a.P.E.Normal := normalizer_eq_top_iff.mp (a.point_normalizer.trans htop)
  rcases hn.eq_bot_or_eq_top with he | he
  · have hz : z = 1 := by simpa only [he, mem_bot] using a.marker_mem_E
    have ho := h.involution
    rw [hz, orderOf_one] at ho
    norm_num at ho
  · apply a.E_ne_point
    exact le_antisymm a.P.E_le (he ▸ le_top)

/-- The original point-coset action is faithful in the finite-simple consumer. -/
theorem point_corefree [IsSimpleGroup G] : a.P.M.normalCore = ⊥ := by
  rcases a.P.M.normalCore_normal.eq_bot_or_eq_top with he | he
  · exact he
  · exact (a.point_ne_top (top_unique (he ▸ a.P.M.normalCore_le))).elim



end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
