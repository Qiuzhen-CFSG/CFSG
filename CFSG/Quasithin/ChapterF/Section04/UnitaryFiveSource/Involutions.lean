module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortCentralizer
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.PlaneCenter
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Native involution coverage and short centralizers on the U₅(4) model

Every native involution is conjugate to a nonidentity element of the actual
plane-core center. The faithful unipotent parametrization identifies this
center with the zero-vector-coordinate locus in the plane radical. The
identity Hermitian block selects a rank-two involution whose entire native
centralizer lies in the plane endpoint.

The Chapter6 companion applies these statements through the published exact
marking; native coverage does not imply coverage of outer or ambient involutions.
Source: Aschbacher–Smith F.4.27(3–4), F.4.35 and F.4.42, pp.288,292,295.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

/-- A square-one plane parameter belongs to the intrinsic core center. -/
theorem parameter_mem_right_core_center (v : PlaneCore.Parameters U.form) (hv : v.x = 0) :
    (PlaneCore.Parameters.toParabolic U.matrix v).val ∈
      (center (U.rightLocalImage.pCoreIn 2)).map (U.rightLocalImage.pCoreIn 2).subtype := by
  have hcore : (PlaneCore.Parameters.toParabolic U.matrix v).val ∈
      U.rightLocalImage.pCoreIn 2 := by
    change _ ∈ Source.twoCore U.rightLocalImage
    rw [U.rightLocalImage_twoCore]
    exact ⟨_,⟨v,rfl⟩,rfl⟩
  obtain ⟨q,hq,he⟩ := hcore
  let e := (pCore 2 U.rightLocalImage).equivMapOfInjective
    U.rightLocalImage.subtype U.rightLocalImage.subtype_injective
  have hsq : (⟨q,hq⟩ : pCore 2 U.rightLocalImage) ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change q.val ^ 2 = 1
    change q.val = _ at he
    rw [he]
    exact congrArg Subtype.val (show PlaneCore.Parameters.toParabolic U.matrix v ^ 2 = 1 from by
      rw [←map_pow,(PlaneCore.Parameters.square_eq_one_iff U.form v).mpr hv,map_one])
  have hz := (U.rightLocalImage_core_center_structure).2.2.2.2 ⟨q,hq⟩ |>.mp hsq
  exact ⟨e ⟨q,hq⟩,(centerCongr e ⟨⟨q,hq⟩,hz⟩).property,he⟩

/-- Every native involution is conjugate to a member of the actual plane-core center. -/
theorem involution_to_right_core_center (u : U.Carrier) (hu : orderOf u = 2) :
    ∃ v : U.rightParabolic,
      v.val ∈ (center (U.rightLocalImage.pCoreIn 2)).map (U.rightLocalImage.pCoreIn 2).subtype ∧
      orderOf v = 2 ∧ IsConj u v.val := by
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have hne : u ≠ 1 := by intro he; simp [he] at hu
  obtain ⟨g,v,hv,hvne,he⟩ := InvolutionGeometry.projective_involution_to_plane_center
    U.form U.local_field_card U.conjugation U.matrix u hu2 hne
  refine ⟨PlaneCore.Parameters.toParabolic U.matrix v,U.parameter_mem_right_core_center v hv,?_,
    isConj_iff.mpr ⟨(project U.form g)⁻¹,by simpa only [inv_inv] using he⟩⟩
  apply orderOf_eq_prime
  · rw [←map_pow,(PlaneCore.Parameters.square_eq_one_iff U.form v).mpr hv,map_one]
  · intro hh
    apply hvne
    apply PlaneCore.Parameters.toParabolic_injective U.matrix
    simpa only [map_one] using hh

/-- The selected rank-two involution, inside the literal plane endpoint. -/
def shortInvolution : U.rightParabolic :=
  PlaneCore.Parameters.toParabolic U.matrix (InvolutionGeometry.shortParameter U.form)

theorem shortInvolution_mem_center :
    (U.shortInvolution).val ∈ (center (U.rightLocalImage.pCoreIn 2)).map
      (U.rightLocalImage.pCoreIn 2).subtype :=
  U.parameter_mem_right_core_center _ rfl

theorem shortInvolution_order : orderOf U.shortInvolution = 2 := by
  apply orderOf_eq_prime
  · change (PlaneCore.Parameters.toParabolic U.matrix (InvolutionGeometry.shortParameter U.form)) ^ 2 = 1
    rw [←map_pow,InvolutionGeometry.shortParameter_square,map_one]
  · intro hh
    apply InvolutionGeometry.shortParameter_ne_one U.form
    apply PlaneCore.Parameters.toParabolic_injective U.matrix
    simpa only [shortInvolution,map_one] using hh

/-- The entire native projective centralizer lies in the marked plane endpoint. -/
theorem shortInvolution_centralizer_le :
    centralizer ({U.shortInvolution.val} : Set U.Carrier) ≤ U.rightParabolic :=
  InvolutionGeometry.short_centralizer_le U.form U.local_field_card U.conjugation U.matrix

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
