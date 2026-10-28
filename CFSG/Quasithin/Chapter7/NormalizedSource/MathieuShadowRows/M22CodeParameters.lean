module
public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.OctadGeometry.Reduction
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.NoFF
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Quadratic parameters for the original M22 code row

The proved quadratic-actor bound leaves only ranks one and two. A rank-two
actor meets the native inner M22 in an involution, whose actual code
displacement is four. The involution bounds therefore prove q >= 2 for
the full outer code action. The native code/cocode pairing transports the
proved cocode non-FF theorem to the dual of every marked code restriction.

These discharge the numerical and dual inputs of original 3.1.9 in the
exceptional inside-core branch of 8.2.2(1), without supplying the later
parabolic quotient or its exclusion as an assumption.
Source: Aschbacher--Smith, K.4.4 and 8.2.2(1), printed pp.459,714--715,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender MathieuCode
open CFSG.Quasithin.ChapterK.Mathieu CFSG.Quasithin.ChapterK.Mathieu.OctadGeometry
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows

/-- The full outer code action has quadratic ratio at least two. -/
theorem m22_code_quadratic_lower : 2 ≤ quadraticRatio m22OuterCodeRepresentation := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA,hq⟩
  let : IsElementaryAbelian 2 A := hA.2
  have hc := MathieuCode.QuadraticActors.m22Outer_code_card_le_four A hq
  have hr : rank A ≤ 2 := (Nat.log_mono_right hc : Nat.log 2 (Nat.card A) ≤ Nat.log 2 4)
  have hb : 2 * rank A ≤ fixedCodim m22OuterCodeRepresentation A := by
    by_cases ht : 1 < rank A
    · obtain ⟨x,hx,hx2,h0⟩ := m22_exists_inner_involution A hA ht
      have hd := m22Outer_cocode_involution_displacement_of_fixed_zero x hx2 h0
      rw [← m22Outer_code_cocode_fixedCodim_zpowers] at hd
      have hm := Submodule.finrank_mono
        (fixedSpace_antitone m22OuterCodeRepresentation (zpowers_le.mpr hx))
      have hf := fixedCodim_add_finrank m22OuterCodeRepresentation A
      have hg := fixedCodim_add_finrank m22OuterCodeRepresentation (zpowers x)
      omega
    · have hm := ChapterE.moduleM_le_fixedCodim m22OuterCodeRepresentation hA
      have h3 := m22_code_moduleM_gt_two
      omega
  rw [actionRatio, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)))
    (Or.inl (by simp))]
  exact_mod_cast hb

/-- Actual marked restrictions retain the ratio bound and are not dual FF. -/
theorem marked_m22_code_parameters
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W)
    (f : X →* m22PairStabilizer) (hf : Function.Injective f)
    (E : W ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ g v, E (ρ g v) = m22OuterCodeRepresentation (f g) (E v)) :
    2 ≤ quadraticRatio ρ ∧ ¬ IsFFModule ρ.dual := by
  refine ⟨m22_code_quadratic_lower.trans
    (quadraticRatio_le_of_injective_equivariant ρ _ f hf E hE), ?_⟩
  let F : M22Cocode ≃ₗ[ZMod 2] Module.Dual (ZMod 2) W :=
    ((Module.evalEquiv (ZMod 2) M22Cocode).trans m22CodeCocodeDuality.dualMap).trans E.dualMap
  have hF (g : X) (u : M22Cocode) :
      F (m22OuterCocodeRepresentation (f g) u) = ρ.dual g (F u) := by
    ext w
    change m22CodeCocodeDuality (E w) (m22OuterCocodeRepresentation (f g) u) =
      m22CodeCocodeDuality (E (ρ g⁻¹ w)) u
    rw [hE]
    have he := LinearMap.congr_fun (m22CodeCocodeDuality_equivariant (f g⁻¹) (E w)) u
    simpa only [Representation.dual_apply, Module.Dual.transpose_apply, map_inv, inv_inv, LinearMap.comp_apply] using he.symm
  intro hff
  apply MathieuCode.QuadraticActors.m22OuterCocode_not_isFFModule
  apply hff.map_equivariant ρ.dual m22OuterCocodeRepresentation f hf F.symm
  intro g v
  apply F.injective
  rw [F.apply_symm_apply,hF,F.apply_symm_apply]

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows
