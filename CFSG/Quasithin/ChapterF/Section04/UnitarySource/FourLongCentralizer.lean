module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongCentralizer
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointResidual
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Models
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.CartanTransport

/-!
# Full-extension long-root centralizers for unitary four-space

An element of the extension factors as a native inner automorphism times
an element of its whole middle. The middle preserves the point parabolic,
its solvable residual and that residual's center. Transitivity on nonzero
long roots corrects the inner factor by an element of the point parabolic;
the native centralizer containment then places the full automorphism in
the corresponding extension endpoint. No restriction on outer degree is
assumed. The Chapter6 companion uses this on the same constructed marking.

Source: Aschbacher–Smith F.4.27(4), F.4.42–43, printed pp.288,295–296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary

private theorem aut_conjugate_inner {B : Type*} [Group B] (a : MulAut B) (x : B) :
    a * MulAut.conj x * a⁻¹ = MulAut.conj (a x) := by
  ext y
  change a (x * (a.symm y) * x⁻¹) = a x * y * (a x)⁻¹
  rw [map_mul,map_mul,map_inv,a.apply_symm_apply]

private theorem residual_center_preserved {B : Type*} [Group B] [Finite B]
    (P : Subgroup B) (a : MulAut B) (hP : P.map a.toMonoidHom = P)
    (z : B) (hz : z ∈ (center ((solvableResidual P).map P.subtype)).map
      ((solvableResidual P).map P.subtype).subtype) :
    a z ∈ (center ((solvableResidual P).map P.subtype)).map
      ((solvableResidual P).map P.subtype).subtype := by
  let e := (a.subgroupMap P).trans (MulEquiv.subgroupCongr hP)
  let K := (solvableResidual P).map P.subtype
  have hK : K.map a.toMonoidHom = K := by
    dsimp only [K]
    rw [map_map,show a.toMonoidHom.comp P.subtype = P.subtype.comp e.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]
  obtain ⟨z,hz,rfl⟩ := hz
  let f := (a.subgroupMap K).trans (MulEquiv.subgroupCongr hK)
  exact ⟨f z,(centerCongr f ⟨z,hz⟩).property,rfl⟩

/-- Every full-extension centralizer of a nonidentity long root belongs to
its full point endpoint, including the outer actors. -/
theorem FourExtension.long_root_centralizer_le (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m)
    (E : FourExtension m hm) (z : ProjectiveGroup m hm)
    (hz : z ∈ (center (PointLocal.ProjectiveLocal m hm)).map
      (PointLocal.ProjectiveLocal m hm).subtype) (hne : z ≠ 1) :
    centralizer ({E.baseHom z} : Set E.carrier) ≤ E.left.subgroupOf E.carrier := by
  let : Finite (ProjectiveGroup m hm) :=
    Finite.of_surjective (projection m hm)
      (UnitaryFourFlag.project_surjective (MatrixField m) (standardForm m hm))
  intro a ha
  have he : a.val * MulAut.conj z = MulAut.conj z * a.val :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
  have hfix : a.val z = z := by
    apply four_conj_injective m hm
    rw [←aut_conjugate_inner,he,mul_inv_cancel_right]
  obtain ⟨b,k,hk,hak⟩ := E.factor a.val a.property
  have hkP : (pointParabolic m hm).map k.toMonoidHom = pointParabolic m hm := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (E.middle_preserves_left (four_conj_injective m hm) ⟨k,hk⟩ y).mpr hy
    · intro hx
      refine ⟨k.symm x,?_,k.apply_symm_apply x⟩
      exact (E.middle_preserves_left (four_conj_injective m hm) ⟨k,hk⟩ (k.symm x)).mp
        (by simpa only [k.apply_symm_apply] using hx)
  have hkz : k z ∈ (center (PointLocal.ProjectiveLocal m hm)).map
      (PointLocal.ProjectiveLocal m hm).subtype := by
    rw [←PointLocal.pointParabolic_solvableResidual m hm hmgt] at hz ⊢
    exact residual_center_preserved (pointParabolic m hm) k hkP z hz
  obtain ⟨p,hp,hep⟩ : ∃ p : ProjectiveGroup m hm, p ∈ pointParabolic m hm ∧
      k z = p*z*p⁻¹ := SourceNormalizer.FourCenter.projective_center_orbit
    (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
    (PointLocal.fieldConj_nontrivial m hm) z hz hne (k z) hkz
    (fun hh => hne (k.map_eq_one_iff.mp hh))
  have hbp : b*p ∈ centralizer ({z} : Set (ProjectiveGroup m hm)) := by
    apply mem_centralizer_singleton_iff.mpr
    have hfix' : b * (k z) * b⁻¹ = z := by
      rw [hak] at hfix
      exact hfix
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (b*p)*z*(b*p)⁻¹ = b*(p*z*p⁻¹)*b⁻¹ := by group
      _ = z := by rw [←hep]; exact hfix'
  have hb : b ∈ pointParabolic m hm := by
    have hcent := SourceNormalizer.FourCenter.projective_center_centralizer_le
      (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
      (PointLocal.fieldConj_nontrivial m hm) z hz hne hbp
    have hh := (pointParabolic m hm).mul_mem hcent ((pointParabolic m hm).inv_mem hp)
    simpa only [mul_inv_cancel_right] using hh
  change a.val ∈ E.left
  rw [hak]
  exact E.left.mul_mem ((E.conj_mem_left_iff (four_conj_injective m hm) b).mpr hb) hk.1
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
