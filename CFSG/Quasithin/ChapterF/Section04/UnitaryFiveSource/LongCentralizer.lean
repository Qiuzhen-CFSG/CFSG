module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.LongCentralizer
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.LineCenter
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveCensus

/-!
# Full-extension long-root centralizers on the unitary-five model

The native long-root matrix calculation places the centralizer of every
nonidentity element of the line residual center inside its parabolic.
An extension automorphism factors as an inner automorphism times a marked
middle element. The latter preserves the residual center; its native parabolic
orbit reduces the inner factor to the native centralizer. This proves full
centralizer placement in the extension endpoint, including all outer actors.

The Chapter6 companion applies this on the published extension of the original
row. Source: Aschbacher–Smith F.4.27(4), F.4.31(b) and F.4.43, pp.288,291,296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

/-- The whole native projective centralizer lies in the line parabolic. -/
theorem leftLocalImage_center_centralizer (z : U.Carrier)
    (hz : z ∈ (center U.leftLocalImage).map U.leftLocalImage.subtype) (hne : z ≠ 1) :
    centralizer ({z} : Set U.Carrier) ≤ U.leftParabolic := by
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  obtain ⟨z,hz,rfl⟩ := hz
  let e := (centerCongr U.leftLocalImageEquiv).symm ⟨z,hz⟩
  have he : (e.val.val : U.Carrier) = z.val :=
    congrArg (fun z : U.leftLocalImage => z.val) (U.leftLocalImageEquiv.apply_symm_apply z)
  have hc' : e.val.val ∈ (center U.leftLocal).map U.leftLocal.subtype :=
    ⟨e.val,e.property,rfl⟩
  have hZ : (center U.leftLocal).map U.leftLocal.subtype =
      (center (LineCore.Coord U.form)).map (LineCore.Parabolic.toParabolic U.form U.matrix) := by
    rw [U.leftLocal_eq_lineRadicalLeviSubgroup]
    exact LineCore.Parabolic.center_image_eq U.form U.matrix U.conjugation U.local_field_card c hc
  rw [hZ] at hc'
  obtain ⟨u,hu,huval⟩ := hc'
  have hzval : (LineCore.Parabolic.toParabolic U.form U.matrix u).val = z.val :=
    (congrArg Subtype.val huval).trans he
  change centralizer ({z.val} : Set U.Carrier) ≤ U.leftParabolic
  rw [←hzval]
  exact long_root_centralizer_le U.form U.matrix U.conjugation U.local_field_card c hc
    u hu (fun hu1 => hne (hzval.symm.trans (by rw [hu1,map_one]; rfl)))

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
variable {B : Type*} [Group B]

private theorem aut_conjugate_inner (a : MulAut B) (x : B) :
    a * MulAut.conj x * a⁻¹ = MulAut.conj (a x) := by
  ext y
  change a (x * (a.symm y) * x⁻¹) = a x * y * (a x)⁻¹
  rw [map_mul,map_mul,map_inv,a.apply_symm_apply]

private theorem SourceExtension.preserves_left {P Q : Subgroup B}
    (E : SourceExtension P Q) (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (a : MulAut B) (ha : a ∈ E.left) : P.map a.toMonoidHom = P := by
  have hmem (a : MulAut B) (ha : a ∈ E.left) (x : B) (hx : x ∈ P) : a x ∈ P := by
    apply (E.conj_mem_left_iff hi _).mp
    rw [←aut_conjugate_inner]
    exact E.left.mul_mem (E.left.mul_mem ha ((E.conj_mem_left_iff hi _).mpr hx))
      (E.left.inv_mem ha)
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hmem a ha x hx
  · intro x hx
    exact ⟨a⁻¹ x,hmem a⁻¹ (E.left.inv_mem ha) x hx,a.apply_symm_apply x⟩

private theorem center_image_preserved (K : Subgroup B) (a : MulAut B)
    (hK : K.map a.toMonoidHom = K) (z : B)
    (hz : z ∈ (center K).map K.subtype) : a z ∈ (center K).map K.subtype := by
  obtain ⟨z,hz,rfl⟩ := hz
  let e := (a.subgroupMap K).trans (MulEquiv.subgroupCongr hK)
  exact ⟨e z,(centerCongr e ⟨z,hz⟩).property,rfl⟩

private theorem residual_image_preserved [Finite B] (P : Subgroup B) (a : MulAut B)
    (hP : P.map a.toMonoidHom = P) :
    ((solvableResidual P).map P.subtype).map a.toMonoidHom =
      (solvableResidual P).map P.subtype := by
  let e := (a.subgroupMap P).trans (MulEquiv.subgroupCongr hP)
  rw [map_map,show a.toMonoidHom.comp P.subtype = P.subtype.comp e.toMonoidHom from rfl,
    ←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]

variable (U : GreenBook.UnitaryFive.Model 4)

/-- Every full-extension centralizer of a nonidentity long-root element
lies in the corresponding full endpoint. -/
theorem FiveExtension.long_root_centralizer_le (E : FiveExtension U) (z : U.Carrier)
    (hz : z ∈ (center U.leftLocalImage).map U.leftLocalImage.subtype) (hne : z ≠ 1) :
    centralizer ({E.baseHom z} : Set E.carrier) ≤ E.left.subgroupOf E.carrier := by
  intro a ha
  have he : a.val * MulAut.conj z = MulAut.conj z * a.val :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
  have hfix : a.val z = z := by
    apply five_conj_injective U
    rw [←aut_conjugate_inner,he,mul_inv_cancel_right]
  obtain ⟨b,k,hk,hak⟩ := E.factor a.val a.property
  have hkP := E.preserves_left (five_conj_injective U) k hk.1
  have hkL : U.leftLocalImage.map k.toMonoidHom = U.leftLocalImage :=
    residual_image_preserved U.leftParabolic k hkP
  have hkz := center_image_preserved U.leftLocalImage k hkL z hz
  obtain ⟨p,hp,hep⟩ := U.leftLocalImage_center_orbit z hz hne (k z) hkz
    (fun he => hne (k.map_eq_one_iff.mp he))
  have hbp : b*p ∈ centralizer ({z} : Set U.Carrier) := by
    apply mem_centralizer_singleton_iff.mpr
    have hfix' : b * (k z) * b⁻¹ = z := by
      have hh := hfix
      rw [hak] at hh
      exact hh
    have hh : (b*p)*z*(b*p)⁻¹ = z := by
      calc
        (b*p)*z*(b*p)⁻¹ = b*(p*z*p⁻¹)*b⁻¹ := by group
        _ = z := by rw [←hep]; exact hfix'
    exact (mul_inv_eq_iff_eq_mul).mp hh
  have hb : b ∈ U.leftParabolic := by
    have hh := U.leftParabolic.mul_mem (U.leftLocalImage_center_centralizer z hz hne hbp)
      (U.leftParabolic.inv_mem hp)
    simpa only [mul_inv_cancel_right] using hh
  change a.val ∈ E.left
  rw [hak]
  exact E.left.mul_mem ((E.conj_mem_left_iff (five_conj_injective U) b).mpr hb) hk.1

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
