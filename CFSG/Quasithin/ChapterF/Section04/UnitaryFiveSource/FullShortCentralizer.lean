module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.SquareTypes
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortConjugacy
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.Involutions
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.LongCentralizer
public import Theory.GroupTheory.SylowKernelCore

/-!
# Full-extension short-root centralizers in U₅(4)

The singular central plane parameters are precisely the squares in the
whole plane radical. Every full plane-endpoint automorphism preserves that
radical, hence preserves nonsingularity. Factor an arbitrary extension
centralizer element into a native inner automorphism and a middle actor.
The middle actor carries the chosen nonsingular parameter to another one;
the conjugator theorem then places the inner factor in the plane parabolic.
Thus the entire extension centralizer lies in its full plane endpoint.

This discharges the native full-extension placement used to choose t at the
start of Aschbacher–Smith F.4.42, printed p.295. The Chapter6 companion
identifies its order with the original local centralizer on the identical
marking. The original ambient equality C_G(t)=X_t still requires F.4.42.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

/-- A native automorphism preserving the plane radical preserves nonsingular
central parameters; singularity is detected by square roots in that radical. -/
theorem nonsingular_parameter_image (a : MulAut U.Carrier)
    (hQ : (U.rightLocalImage.pCoreIn 2).map a.toMonoidHom = U.rightLocalImage.pCoreIn 2)
    (v : PlaneCore.Parameters U.form) (hv : v.x = 0) (hd : v.z.det ≠ 0) :
    ∃ w : PlaneCore.Parameters U.form, w.x = 0 ∧ w.z.det ≠ 0 ∧
      a (PlaneCore.Parameters.toParabolic U.matrix v).val =
        (PlaneCore.Parameters.toParabolic U.matrix w).val := by
  let φ := U.rightParabolic.subtype.comp (PlaneCore.Parameters.toParabolic U.matrix)
  have hφ : Function.Injective φ := Subtype.val_injective.comp
    (PlaneCore.Parameters.toParabolic_injective U.matrix)
  have hQR : U.rightLocalImage.pCoreIn 2 = φ.range := by
    change Source.twoCore U.rightLocalImage = _
    rw [U.rightLocalImage_twoCore]
    exact MonoidHom.range_comp _ _ |>.symm
  have hav : a (φ v) ∈ U.rightLocalImage.pCoreIn 2 := by
    rw [←hQ]
    exact mem_map_of_mem a.toMonoidHom (hQR.symm ▸ (show φ v ∈ φ.range from ⟨v,rfl⟩))
  rw [hQR] at hav
  obtain ⟨w,hw⟩ := hav
  have hv2 : v^2=1 := (PlaneCore.Parameters.square_eq_one_iff U.form v).mpr hv
  have hw2 : w^2=1 := by
    apply hφ
    rw [map_pow,map_one,hw,←map_pow,←map_pow,hv2,map_one,map_one]
  have hwx := (PlaneCore.Parameters.square_eq_one_iff U.form w).mp hw2
  refine ⟨w,hwx,?_,hw.symm⟩
  intro hwd
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  obtain ⟨b,hb⟩ := (PlaneCore.Parameters.square_root_iff_det_zero U.form c hc w hwx).mpr hwd
  have hbQ : φ b ∈ (U.rightLocalImage.pCoreIn 2).map a.toMonoidHom := by
    rw [hQ,hQR]
    exact ⟨b,rfl⟩
  obtain ⟨x,hx,hex⟩ := hbQ
  rw [hQR] at hx
  obtain ⟨y,rfl⟩ := hx
  change a (φ y) = φ b at hex
  have hyv : y^2=v := by
    apply hφ
    apply a.injective
    rw [map_pow,map_pow,hex,←map_pow,hb,hw]
  exact hd ((PlaneCore.Parameters.square_root_iff_det_zero U.form c hc v hv).mp ⟨y,hyv⟩)

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive
variable (U : GreenBook.UnitaryFive.Model 4)

private theorem aut_conjugate_inner (a : MulAut U.Carrier) (x : U.Carrier) :
    a * MulAut.conj x * a⁻¹ = MulAut.conj (a x) := by
  apply MulEquiv.ext
  intro y
  change a (x * (a.symm y) * x⁻¹) = a x * y * (a x)⁻¹
  rw [map_mul,map_mul,map_inv,a.apply_symm_apply]

private theorem preserves_right_core (E : FiveExtension U) (a : MulAut U.Carrier)
    (ha : a ∈ E.right) :
    (U.rightLocalImage.pCoreIn 2).map a.toMonoidHom = U.rightLocalImage.pCoreIn 2 := by
  have hmem (a : MulAut U.Carrier) (ha : a ∈ E.right) (x : U.Carrier)
      (hx : x ∈ U.rightParabolic) : a x ∈ U.rightParabolic := by
    apply (E.conj_mem_right_iff (five_conj_injective U) _).mp
    rw [←aut_conjugate_inner]
    exact E.right.mul_mem (E.right.mul_mem ha
      ((E.conj_mem_right_iff (five_conj_injective U) _).mpr hx)) (E.right.inv_mem ha)
  have hP : U.rightParabolic.map a.toMonoidHom = U.rightParabolic := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hmem a ha x hx
    · intro x hx
      exact ⟨a⁻¹ x,hmem a⁻¹ (E.right.inv_mem ha) x hx,a.apply_symm_apply x⟩
  let e := (a.subgroupMap U.rightParabolic).trans (MulEquiv.subgroupCongr hP)
  have hR : U.rightLocalImage.map a.toMonoidHom = U.rightLocalImage := by
    change ((solvableResidual U.rightParabolic).map U.rightParabolic.subtype).map a.toMonoidHom = _
    rw [map_map,show a.toMonoidHom.comp U.rightParabolic.subtype =
      U.rightParabolic.subtype.comp e.toMonoidHom from rfl,←map_map,
      map_solvableResidual_eq e.toMonoidHom e.surjective]
    rfl
  rw [map_pCoreIn_of_injective 2 _ a.toMonoidHom a.injective,hR]

/-- Every nonsingular central plane parameter has its full extension
centralizer in the full plane endpoint, including the outer actors. -/
theorem FiveExtension.nonsingular_centralizer_le (E : FiveExtension U)
    (v : PlaneCore.Parameters U.form) (hv : v.x = 0) (hd : v.z.det ≠ 0) :
    centralizer ({E.baseHom (PlaneCore.Parameters.toParabolic U.matrix v).val} : Set E.carrier) ≤
      E.right.subgroupOf E.carrier := by
  intro a ha
  have he : a.val * MulAut.conj (PlaneCore.Parameters.toParabolic U.matrix v).val =
      MulAut.conj (PlaneCore.Parameters.toParabolic U.matrix v).val * a.val :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
  have hfix : a.val (PlaneCore.Parameters.toParabolic U.matrix v).val =
      (PlaneCore.Parameters.toParabolic U.matrix v).val := by
    apply five_conj_injective U
    rw [←aut_conjugate_inner,he,mul_inv_cancel_right]
  obtain ⟨b,k,hk,hak⟩ := E.factor a.val a.property
  obtain ⟨w,hw,hdw,hew⟩ := U.nonsingular_parameter_image k
    (preserves_right_core U E k hk.2) v hv hd
  have hconj : b * (PlaneCore.Parameters.toParabolic U.matrix w).val * b⁻¹ =
      (PlaneCore.Parameters.toParabolic U.matrix v).val := by
    rw [hak] at hfix
    change b * k (PlaneCore.Parameters.toParabolic U.matrix v).val * b⁻¹ = _ at hfix
    rwa [hew] at hfix
  have hbp := InvolutionGeometry.nonsingular_conjugator_mem_plane U.form U.local_field_card
    U.conjugation U.matrix w v hw hv hdw hd b hconj
  change a.val ∈ E.right
  rw [hak]
  exact E.right.mul_mem ((E.conj_mem_right_iff (five_conj_injective U) b).mpr hbp) hk.2

/-- The selected short involution satisfies the full-extension endpoint bound. -/
theorem FiveExtension.shortInvolution_centralizer_le (E : FiveExtension U) :
    centralizer ({E.baseHom U.shortInvolution.val} : Set E.carrier) ≤
      E.right.subgroupOf E.carrier :=
  FiveExtension.nonsingular_centralizer_le U E _ rfl (by
    rw [InvolutionGeometry.shortParameter_det]; exact one_ne_zero)

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
