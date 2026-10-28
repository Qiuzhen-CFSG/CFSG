module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.Defs
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport.Markings

/-!
# Comparing the marked Todd point groups

Native M₂₄ transitivity transports the whole sextet with a single group
element. Conjugating by its lift in the split Todd group and composing the
two given Todd identifications constructs the point-group isomorphism.
It retains the same quotient conjugation, sends the actual embedded marker
to its counterpart, and hence maps the literal point-plane intersection.

This is the point/plane portion of AS91 (8.4), p.607. The simultaneous trio
and edge-stabilizer images, and agreement with the separately constructed
plane-group comparison, are not asserted by these results.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped Pointwise

private theorem sextetVector_transport (S T : Sextet) (g : M24)
    (hg : g • S.parts = T.parts) : cocodeRepresentation g (sextetVector S) = sextetVector T := by
  obtain ⟨B,hB⟩ := sextet_parts_nonempty S
  rw [sextetVector_eq S hB,evenSetVector_equivariant]
  exact (sextetVector_eq T (hg ▸ Finset.smul_mem_smul_finset hB)).symm

/-- One native M₂₄ element transports the full sextet and its actual cocode marker. -/
theorem exists_sextet_transport (S T : Sextet) :
    ∃ g : M24, g • S.parts = T.parts ∧
      cocodeRepresentation g (sextetVector S) = sextetVector T := by
  obtain ⟨a,ha⟩ := SextetLayers.CoordinateTransport.exists_sextet_conjugator S
  obtain ⟨b,hb⟩ := SextetLayers.CoordinateTransport.exists_sextet_conjugator T
  have hg : (b * a⁻¹) • S.parts = T.parts := by
    rw [mul_smul,← ha,inv_smul_smul,hb]
  exact ⟨b * a⁻¹,hg,sextetVector_transport S T _ hg⟩

variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
variable {z : G} {z' : G'}

/-- The comparison uses one conjugation in the common marked Todd group. -/
noncomputable def pointEquiv (P : PointData z) (P' : PointData z') (g : M24) : P.M ≃* P'.M :=
  (P.toddEquiv.symm.trans (MulAut.conj (SemidirectProduct.inr g : ToddGroup))).trans P'.toddEquiv

/-- The same M₂₄ conjugator is retained in the quotient equation. -/
theorem pointEquiv_projection (P : PointData z) (P' : PointData z') (g : M24) (m : P.M) :
    P'.projection (pointEquiv P P' g m) = g * P.projection m * g⁻¹ := by
  simp [pointEquiv,PointData.projection,MulAut.conj_apply]

/-- The vector formula keeps the original embedded cocode. -/
theorem pointEquiv_vector (P : PointData z) (P' : PointData z') (g : M24) (v : ToddVector) :
    (pointEquiv P P' g (P.toddEquiv (SemidirectProduct.inl v)) : G') =
      P'.vectorEmbedding (toddAction g v) := by
  change (P'.toddEquiv (SemidirectProduct.inr g *
    P.toddEquiv.symm (P.toddEquiv (SemidirectProduct.inl v)) *
      (SemidirectProduct.inr g)⁻¹) : G') = _
  rw [P.toddEquiv.symm_apply_apply,← map_inv,← SemidirectProduct.inl_aut]
  rfl

variable {h : IsTypeJ4 z} {h' : IsTypeJ4 z'}
variable (a : SourceIncidence.LocalData h) (a' : SourceIncidence.LocalData h')

/-- The same marked involution lies in the constructed point subgroup. -/
theorem marker_mem_point : z ∈ a.P.M := by
  have hm : a.P.vectorEmbedding (Multiplicative.ofAdd (sextetVector a.sextet)) ∈ a.P.M :=
    (a.P.toddEquiv (SemidirectProduct.inl (Multiplicative.ofAdd (sextetVector a.sextet)))).property
  exact Eq.mp (congrArg (fun x : G => x ∈ a.P.M) a.marker_vector) hm

/-- Transporting the sextet transports the original marker as an element. -/
theorem pointEquiv_marker (g : M24)
    (hg : cocodeRepresentation g (sextetVector a.sextet) = sextetVector a'.sextet) :
    (pointEquiv a.P a'.P g ⟨z,marker_mem_point a⟩ : G') = z' := by
  have hz : (⟨z,marker_mem_point a⟩ : a.P.M) =
      a.P.toddEquiv (SemidirectProduct.inl (Multiplicative.ofAdd (sextetVector a.sextet))) :=
    Subtype.ext a.marker_vector.symm
  rw [hz,pointEquiv_vector]
  change a'.P.vectorEmbedding (Multiplicative.ofAdd (cocodeRepresentation g (sextetVector a.sextet))) = z'
  rw [hg]
  exact a'.marker_vector

/-- Any marker-preserving point comparison carries the literal plane overlap. -/
theorem pointEquiv_overlap (φ : a.P.M ≃* a'.P.M)
    (hφ : (φ ⟨z,marker_mem_point a⟩ : G') = z') :
    ((centralizer z).subgroupOf a.P.M).map φ.toMonoidHom =
      (centralizer z').subgroupOf a'.P.M := by
  have he (m : a.P.M) :
      (φ m : G') ∈ centralizer z' ↔ (m : G) ∈ centralizer z := by
    rw [mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
    have hzφ : φ ⟨z,marker_mem_point a⟩ = (⟨z',marker_mem_point a'⟩ : a'.P.M) := Subtype.ext hφ
    have hi : φ m * (⟨z',marker_mem_point a'⟩ : a'.P.M) =
        (⟨z',marker_mem_point a'⟩ : a'.P.M) * φ m ↔
        m * (⟨z,marker_mem_point a⟩ : a.P.M) = (⟨z,marker_mem_point a⟩ : a.P.M) * m := by
      rw [← hzφ,← φ.map_mul,← φ.map_mul,φ.injective.eq_iff]
    exact Subtype.ext_iff.symm.trans (hi.trans Subtype.ext_iff)
  ext m'
  constructor
  · rintro ⟨m,hm,rfl⟩
    exact (he m).mpr hm
  · intro hm'
    change (m' : G') ∈ centralizer z' at hm'
    exact ⟨φ.symm m',(he _).mp (by simpa only [φ.apply_symm_apply] using hm'),φ.apply_symm_apply m'⟩

/-- Construct the point-group comparison and plane-overlap image. The line
and full edge-stabilizer images are additional Section 8 obligations. -/
theorem exists_point_equiv :
    ∃ (g : M24) (φ : a.P.M ≃* a'.P.M),
      g • a.sextet.parts = a'.sextet.parts ∧
      (∀ m, a'.P.projection (φ m) = g * a.P.projection m * g⁻¹) ∧
      (φ ⟨z,marker_mem_point a⟩ : G') = z' ∧
      ((centralizer z).subgroupOf a.P.M).map φ.toMonoidHom =
        (centralizer z').subgroupOf a'.P.M := by
  obtain ⟨g,hg,hv⟩ := exists_sextet_transport a.sextet a'.sextet
  have hm := pointEquiv_marker a a' g hv
  exact ⟨g,pointEquiv a.P a'.P g,hg,pointEquiv_projection a.P a'.P g,hm,
    pointEquiv_overlap a a' _ hm⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
