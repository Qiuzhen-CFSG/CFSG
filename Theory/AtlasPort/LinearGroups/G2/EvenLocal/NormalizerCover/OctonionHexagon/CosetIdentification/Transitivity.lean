module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification.Basic
public import Theory.AtlasPort.LinearGroups.G2.PointOrbits

/-!
# Transitivity on octonion flags

After sending an incident point to the first coordinate point, every vector
in its zero-product plane lies in the common annihilator of that coordinate.
The licensed ATLAS port's `lower_vector_reduction` sends a second independent
vector to coordinate 1 while fixing the first projective point. Dimension two
then identifies the image plane with `standardLine`.

This proves flag and line transitivity for the actual automorphism model,
without a counting argument. Source context: the split G₂ geometry underlying
Aschbacher--Smith, Theorem 0.1.2(1), printed pp.3--4 and pp.481--482.
-/

public section

open Atlas.G2 Atlas.SplitOctonion
namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
variable {F : Type*} [Field F]

theorem firstPoint_on_line_iff (L : ZeroProductLine F) :
    pointOnLine (firstPoint (K := F)) L ↔ basisVector 0 ∈ L.val := by
  exact pointOnLine_mk _ _ _ _ _

theorem line_through_firstPoint_reduction (L : ZeroProductLine F)
    (hL : pointOnLine firstPoint L) :
    ∃ g ∈ parabolic (F := F), g • L = standardLine := by
  have h0 := (firstPoint_on_line_iff L).mp hL
  have hnot : ¬ L.val ≤ Submodule.span F {basisVector 0} := by
    intro h
    have hf := Submodule.finrank_mono h
    rw [L.property.1, finrank_span_singleton first_basis_ne_zero] at hf
    omega
  have hex : ∃ x ∈ L.val, x ∉ Submodule.span F {basisVector 0} := by
    by_contra! hn
    exact hnot hn
  obtain ⟨x,hx,hout⟩ := hex
  have hl : inLowerPlane x := inLowerPlane_iff_annihilator x |>.mpr
    ⟨L.property.2 _ h0 _ hx, L.property.2 _ hx _ h0⟩
  obtain ⟨h3,h4,h5,h6,h7⟩ := hl
  have hp : x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra! h
    apply hout
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x 0,?_⟩
    funext i
    fin_cases i <;> simp [basisVector,h.1,h.2,h3,h4,h5,h6,h7]
  have hs := line_singular L x hx
  obtain ⟨g,hg,a,ha,he⟩ := lower_vector_reduction x hs.1 hs.2 h5 h6 h7 hp
  refine ⟨g,hg,line_eq_standard_of_basis_mem (g • L) ?_ ?_⟩
  · have hfix : g • firstPoint = firstPoint := parabolic_le_pointStabilizer hg
    apply (firstPoint_on_line_iff _).mp
    rw [← hfix]
    exact (pointOnLine_smul_iff g firstPoint L).mpr hL
  · have hx' := (mem_line_smul g L x).mpr hx
    rw [he] at hx'
    exact ((g • L).val.smul_mem_iff ha).mp hx'

/-- Every intrinsic flag is a translate of the standard point and plane. -/
theorem exists_flag_translate (p : SingularPoints F) (L : ZeroProductLine F)
    (hp : pointOnLine p L) :
    ∃ g : Model F, g • standardLine = L ∧ g • firstPoint = p := by
  obtain ⟨h,hh⟩ := exists_smul_firstPoint p
  have hp' : pointOnLine firstPoint (h • L) := by
    rw [← hh]
    exact (pointOnLine_smul_iff h p L).mpr hp
  obtain ⟨k,hk,hL⟩ := line_through_firstPoint_reduction (h • L) hp'
  have hfirst : k • firstPoint = firstPoint := parabolic_le_pointStabilizer hk
  refine ⟨(k*h)⁻¹,?_,?_⟩
  · have he : (k*h) • L = standardLine := by
      simpa only [SemigroupAction.mul_smul] using hL
    rw [← he,inv_smul_smul]
  · have he : (k*h) • p = firstPoint := by rw [SemigroupAction.mul_smul,hh,hfirst]
    rw [← he,inv_smul_smul]

theorem exists_line_translate (L : ZeroProductLine F) :
    ∃ g : Model F, g • standardLine = L := by
  obtain ⟨p,hp⟩ := line_has_point L
  obtain ⟨g,hg,_⟩ := exists_flag_translate p L hp
  exact ⟨g,hg⟩

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
