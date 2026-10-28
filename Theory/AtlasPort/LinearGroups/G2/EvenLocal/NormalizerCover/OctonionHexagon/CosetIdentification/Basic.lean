module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.IntrinsicGeometry

/-!
# Elementary incidence lemmas for the coset identification

Zero-product planes consist of singular vectors, hence contain projective
singular points. Linear images preserve the intrinsic point-line incidence.
The coordinate membership criterion will identify the line stabilizer.

Source context: the split-octonion realization of G₂ in the licensed ATLAS
port, and Aschbacher--Smith, Theorem 0.1.2(1), printed pp.3--4 (repeated on
pp.481--482). These are geometric lemmas, not the classification theorem.
-/

public section

open Atlas.G2 Atlas.SplitOctonion
open Atlas.G2.EvenLocal.NormalizerCover
namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
variable {F : Type*} [Field F]

theorem pointOnLine_mk (x : Carrier F) (hx : x ≠ 0)
    (ht : trace x = 0) (hn : SplitOctonion.norm x = 0) (L : ZeroProductLine F) :
    pointOnLine (singularPointMk F x hx ht hn) L ↔ x ∈ L.val := by
  change (Projectivization.mk F x hx).submodule ≤ L.val ↔ _
  rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]

theorem mem_line_smul (g : Model F) (L : ZeroProductLine F) (x : Carrier F) :
    g.val x ∈ (g • L).val ↔ x ∈ L.val := by
  change g.val x ∈ L.val.map g.val.toLinearMap ↔ _
  constructor
  · rintro ⟨y,hy,h⟩
    exact g.val.injective h ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem pointOnLine_smul_iff (g : Model F) (p : SingularPoints F) (L : ZeroProductLine F) :
    pointOnLine (g • p) (g • L) ↔ pointOnLine p L := by
  rw [← singularPointMk_rep F p, singularPointMk_smul, pointOnLine_mk,
    pointOnLine_mk, mem_line_smul]

theorem firstPoint_on_standardLine : pointOnLine (firstPoint (K := F)) standardLine := by
  rw [firstPoint, pointOnLine_mk]
  exact Submodule.subset_span (by simp)

theorem mem_standardPlane_iff_coordinates (x : Carrier F) :
    x ∈ standardPlane ↔ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 ∧ x 6 = 0 ∧ x 7 = 0 := by
  constructor
  · rintro hx
    obtain ⟨a,b,rfl⟩ := (mem_standardPlane x).mp hx
    simp [basisVector]
  · rintro ⟨h2,h3,h4,h5,h6,h7⟩
    apply (mem_standardPlane x).mpr
    refine ⟨x 0,x 1,?_⟩
    funext i
    fin_cases i <;> simp [basisVector,h2,h3,h4,h5,h6,h7]

theorem line_eq_standard_of_basis_mem (L : ZeroProductLine F)
    (h0 : basisVector 0 ∈ L.val) (h1 : basisVector 1 ∈ L.val) : L = standardLine := by
  apply Subtype.ext
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (by rintro x (rfl | rfl) <;> assumption)
  · exact standardPlane_isZeroProductLine.1.trans L.property.1.symm

theorem line_singular (L : ZeroProductLine F) (x : Carrier F) (hx : x ∈ L.val) :
    trace x = 0 ∧ SplitOctonion.norm x = 0 := by
  have hs := L.property.2 x hx x hx
  have hn : SplitOctonion.norm x = 0 := by
    have h := norm_mul x x
    rw [hs] at h
    have h' : SplitOctonion.norm x * SplitOctonion.norm x = 0 := by
      simpa [SplitOctonion.norm] using h.symm
    exact mul_self_eq_zero.mp h'
  refine ⟨?_,hn⟩
  by_cases h0 : x = 0
  · simp [h0,trace]
  have h := quadratic_identity x
  rw [hs,hn,zero_smul,add_zero,zero_sub,neg_eq_zero] at h
  exact (smul_eq_zero.mp h).resolve_right h0

theorem line_has_point (L : ZeroProductLine F) : ∃ p : SingularPoints F, pointOnLine p L := by
  have hne : L.val ≠ ⊥ := by
    intro h
    have hf := L.property.1
    rw [h,finrank_bot] at hf
    exact (by decide : (0 : ℕ) ≠ 2) hf
  obtain ⟨x,hx,h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hs := line_singular L x hx
  exact ⟨singularPointMk F x h0 hs.1 hs.2,(pointOnLine_mk _ _ _ _ _).mpr hx⟩

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
