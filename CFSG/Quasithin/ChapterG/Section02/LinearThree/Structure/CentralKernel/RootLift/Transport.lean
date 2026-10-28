module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.Interface
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Lifting the additional root through the genuine G.2.5 extension

Relative normality in LT makes T∩I Sylow in I. Its image is therefore
Sylow in I/P and normalizes the image of U. If a conjugate of U* supplies
an independent root in the Sylow image, intersect the same lifted conjugate
with this actual Sylow. The kernel is a normal two-group and lies in the
Sylow, so mapping this intersection gives the required intersection of
images. Faithfulness of U survives conjugation and restriction.

Source: Aschbacher–Smith G.2.5(3), printed pp.335–336, referring to
G.2.3 on pp.333–334. The matrix root construction remains explicit;
no global complement or two-perfectness is assumed here.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
open Setup
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)
  [((WProduct D g h).subgroupOf (I D g h)).Normal]

include d in
/-- The image of the original T, restricted to I, is Sylow in I/P. -/
theorem exists_sylow_eq_image_T (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    ∃ R : Sylow 2 (Quotient D g h), (R : Subgroup (Quotient D g h)) = image D g h D.T := by
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  let N := (I D g h).subgroupOf D.LT
  have hILT := d.I_le_LT hUT
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hILT).mpr
    (d.LT_normalizes_I_of_star hstar.ge)
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal N
  let e := subgroupOfEquivOfLe hILT
  let QI := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQI : (QI : Subgroup (I D g h)) = D.T.subgroupOf (I D g h) := by
    change (Q : Subgroup N).map e.toMonoidHom = _
    rw [hQ]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ((y : D.LT) : G) ∈ D.T
      rw [← hP]
      exact ⟨y, hy, rfl⟩
    · intro hx
      have hpx : (⟨x, hILT x.property⟩ : D.LT) ∈ (P : Subgroup D.LT) := by
        have hm : (x : G) ∈ (P : Subgroup D.LT).map D.LT.subtype := by
          rw [hP]
          exact hx
        obtain ⟨y, hy, he⟩ := hm
        exact (show y = (⟨x, hILT x.property⟩ : D.LT) from Subtype.ext he) ▸ hy
      exact ⟨⟨⟨x, hILT x.property⟩, x.property⟩, hpx, rfl⟩
  refine ⟨QI.mapSurjective (f := projection D g h) (QuotientGroup.mk'_surjective _), ?_⟩
  change (QI : Subgroup (I D g h)).map (projection D g h) = _
  rw [hQI]
  rfl

private theorem map_conjugate {E Q : Type*} [Group E] [Group Q]
    (f : E →* Q) (A : Subgroup E) (x : E) :
    (conjugate A x).map f = conjugate (A.map f) (f x) := by
  simp only [conjugate, map_map]
  congr 1
  ext a
  simp

private theorem map_inf_of_kernel_le {E Q : Type*} [Group E] [Group Q]
    (f : E →* Q) (R C : Subgroup E) (hk : f.ker ≤ R) :
    (R ⊓ C).map f = R.map f ⊓ C.map f := by
  apply le_antisymm (map_inf_le _ _ _)
  rintro y ⟨⟨r, hr, he⟩, c, hc, hce⟩
  have hkr : r⁻¹ * c ∈ f.ker := by
    change f (r⁻¹ * c) = 1
    simp only [map_mul, map_inv, he, hce, inv_mul_cancel]
  have hcr : c ∈ R := by
    simpa only [mul_inv_cancel_left] using R.mul_mem hr (hk hkr)
  exact ⟨c, ⟨hcr, hc⟩, hce⟩

/-- A conjugate root intersection downstairs lifts to the same intersection
upstairs because the two-kernel is contained in the actual Sylow subgroup. -/
theorem hasRootLift_of_star_conjugate (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (hroot : ∃ x : D.star D.L,
      Disjoint ((image D g h D.U).map (starMap d hUT hstar))
        (((image D g h D.T).map (starMap d hUT hstar)) ⊓
          conjugate ((image D g h D.U).map (starMap d hUT hstar)) x) ∧
      (image D g h D.T).map (starMap d hUT hstar) ≤
        (image D g h D.U).map (starMap d hUT hstar) ⊔
          (((image D g h D.T).map (starMap d hUT hstar)) ⊓
            conjugate ((image D g h D.U).map (starMap d hUT hstar)) x)) :
    HasRootLift d hUT hstar := by
  let f := starMap d hUT hstar
  let A := image D g h D.U
  obtain ⟨R, hR⟩ := exists_sylow_eq_image_T d hUT hstar
  obtain ⟨x, hxdis, hxcover⟩ := hroot
  obtain ⟨z, hz⟩ := starMap_surjective d hUT hstar x
  let C := conjugate A z
  let B := (R : Subgroup (Quotient D g h)) ⊓ C
  have hkR : f.ker ≤ R := (starMap_ker_isPGroup d hUT hstar).le_sylow_of_normal R
  have hBmap : B.map f = ((R : Subgroup (Quotient D g h)).map f) ⊓
      conjugate (A.map f) x := by
    rw [map_inf_of_kernel_le f _ _ hkR, map_conjugate, hz]
  have hBker : Disjoint B f.ker := by
    apply disjoint_def.mpr
    rintro b ⟨_, a, ha, he⟩ hb
    have hka : a ∈ f.ker := by
      change f a = 1
      have hh : f ((MulAut.conj z⁻¹) a) = 1 :=
        show (MulAut.conj z⁻¹) a ∈ f.ker from he.symm ▸ hb
      change f (z⁻¹ * a * (z⁻¹)⁻¹) = 1 at hh
      have hh' : (f z)⁻¹ * f a * ((f z)⁻¹)⁻¹ = 1 := by
        simpa only [map_mul, map_inv] using hh
      exact conj_eq_one_iff.mp hh'
    have ha1 : a = 1 := disjoint_def.mp (image_U_disjoint_ker d hUT hstar) ha hka
    simpa only [ha1, map_one] using he.symm
  refine ⟨R, B, ?_, inf_le_left, ?_, hBker, ?_, ?_⟩
  · rw [hR]
    exact map_mono (comap_mono hUT)
  · exact inf_le_left.trans (hR.le.trans (image_T_normalizes_U d))
  · rw [hBmap, hR]
    exact hxdis
  · rw [hBmap, hR]
    exact hxcover

end CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
