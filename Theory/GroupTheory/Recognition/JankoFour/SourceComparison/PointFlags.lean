module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PointComparison
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PointChart

/-!
# One Todd comparison for both members of the original flag

The original triple-intersection index forces the selected trio and sextet
to be incident. Native flag transitivity supplies one M₂₄ conjugator for
both partitions. The resulting Todd isomorphism carries the marked
involution and the literal point-line, point-plane and triple overlaps.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.4), p.607.
Agreement with the plane isomorphism and the full two-point edge-fixer
conjugation equation are separate remaining parts of Section 8.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped Pointwise
variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
variable {z : G} {z' : G'} {h : IsTypeJ4 z} {h' : IsTypeJ4 z'}
variable (a : SourceIncidence.LocalData h) (a' : SourceIncidence.LocalData h')

private theorem transported_fixed_iff {B : Type*} [MulAction M24 B]
    (g k : M24) (x y : B) (hg : g • x = y) :
    (g*k*g⁻¹) • y = y ↔ k • x = x := by
  rw [← hg,mul_smul,mul_smul,inv_smul_smul]
  exact (MulAction.injective g).eq_iff

/-- The one Todd conjugator carries the literal point-line overlap. -/
theorem pointEquiv_line_overlap (g : M24)
    (hg : g • a.trio.parts = a'.trio.parts) :
    (a.L.G₂.subgroupOf a.P.M).map (pointEquiv a.P a'.P g).toMonoidHom =
      a'.L.G₂.subgroupOf a'.P.M := by
  let φ := pointEquiv a.P a'.P g
  have he (m : a.P.M) : (φ m : G') ∈ a'.L.G₂ ↔ (m : G) ∈ a.L.G₂ := by
    rw [a'.point_line_overlap,a.point_line_overlap]
    change (a'.P.projection (pointEquiv a.P a'.P g m)) • a'.trio.parts = a'.trio.parts ↔ _
    rw [pointEquiv_projection]
    exact transported_fixed_iff g (a.P.projection m) a.trio.parts a'.trio.parts hg
  ext m'
  constructor
  · rintro ⟨m,hm,rfl⟩
    exact (he m).mpr hm
  · intro hm'
    change (m' : G') ∈ a'.L.G₂ at hm'
    exact ⟨φ.symm m',(he _).mp (by simpa only [φ.apply_symm_apply] using hm'),
      φ.apply_symm_apply m'⟩

/-- A single native flag conjugator aligns both original local markings. -/
theorem exists_point_flag_equiv :
    ∃ (g : M24) (φ : a.P.M ≃* a'.P.M),
      g • a.trio.parts = a'.trio.parts ∧
      g • a.sextet.parts = a'.sextet.parts ∧
      (∀ m, a'.P.projection (φ m) = g * a.P.projection m * g⁻¹) ∧
      (φ ⟨z,marker_mem_point a⟩ : G') = z' ∧
      ((centralizer z).subgroupOf a.P.M).map φ.toMonoidHom =
        (centralizer z').subgroupOf a'.P.M ∧
      (a.L.G₂.subgroupOf a.P.M).map φ.toMonoidHom = a'.L.G₂.subgroupOf a'.P.M ∧
      ((centralizer z ⊓ a.L.G₂).subgroupOf a.P.M).map φ.toMonoidHom =
        (centralizer z' ⊓ a'.L.G₂).subgroupOf a'.P.M := by
  obtain ⟨g,ht,hs⟩ := SourceIncidence.NativeFlags.flag_transitive
    a.trio a'.trio a.sextet a'.sextet a.native_flag a'.native_flag
  have hv : cocodeRepresentation g (sextetVector a.sextet) = sextetVector a'.sextet := by
    obtain ⟨B,hB⟩ := sextet_parts_nonempty a.sextet
    rw [sextetVector_eq a.sextet hB,evenSetVector_equivariant]
    exact (sextetVector_eq a'.sextet (hs ▸ Finset.smul_mem_smul_finset hB)).symm
  let φ := pointEquiv a.P a'.P g
  have hm := pointEquiv_marker a a' g hv
  have hp := pointEquiv_overlap a a' φ hm
  have hl := pointEquiv_line_overlap a a' g ht
  refine ⟨g,φ,ht,hs,pointEquiv_projection a.P a'.P g,hm,hp,hl,?_⟩
  change (((centralizer z).subgroupOf a.P.M) ⊓ a.L.G₂.subgroupOf a.P.M).map φ.toMonoidHom =
    ((centralizer z').subgroupOf a'.P.M) ⊓ a'.L.G₂.subgroupOf a'.P.M
  rw [Subgroup.map_inf _ _ _ φ.injective,hp,hl]

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
