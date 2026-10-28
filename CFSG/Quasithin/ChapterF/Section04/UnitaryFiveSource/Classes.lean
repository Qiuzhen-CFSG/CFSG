module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Classes
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.FullShortCentralizer

/-!
# Two native involution classes and their full-extension fusion

Hermitian congruence gives two classes in the plane-core center. The proved
native involution placement makes them exhaustive in PSU₅(4), and the
projective displacement calculation separates them. Radical-preserving
middle actors preserve nonsingularity, so the two classes also stay distinct
in every actual full extension. Consequently fusion of plane-core central
elements in either carrier is already realized in the native plane endpoint.

The Chapter6 companion transfers this equivalence to the original prepared
row using its published endpoint marking and ambient normalizer control.
This does not cover outer involutions or prove ambient class coverage.
Source: Aschbacher–Smith F.4.27(3), F.4.29 and F.4.35, printed pp.288–292.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive
open PlaneCore PlaneCore.Parameters
variable (U : Model 4)

/-- The rank-one representative in the literal plane endpoint. -/
def longInvolution : U.rightParabolic :=
  toParabolic U.matrix (diagonalParameter U.form 0 (map_zero _))

theorem longInvolution_mem_center : U.longInvolution.val ∈
    (center (U.rightLocalImage.pCoreIn 2)).map (U.rightLocalImage.pCoreIn 2).subtype :=
  U.parameter_mem_right_core_center _ rfl

theorem longInvolution_order : orderOf U.longInvolution = 2 := by
  apply orderOf_eq_prime
  · change (toParabolic U.matrix (diagonalParameter U.form 0 (map_zero _)))^2=1
    rw [←map_pow,(square_eq_one_iff U.form _).mpr rfl,map_one]
  · intro hh
    have he := toParabolic_injective U.matrix (hh.trans (map_one _).symm)
    exact one_ne_zero (congrArg (fun v : Parameters U.form => v.z 0 0) he)

private theorem diagonal_one : diagonalParameter U.form 1 (map_one _) =
    InvolutionGeometry.shortParameter U.form := by
  apply Parameters.ext (u := diagonalParameter U.form 1 (map_one _))
    (v := InvolutionGeometry.shortParameter U.form) rfl
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The two native representatives are not conjugate in PSU₅(4). -/
theorem long_short_not_isConj : ¬ IsConj U.longInvolution.val U.shortInvolution.val := by
  have h := InvolutionGeometry.long_short_not_isConj U.form U.local_field_card U.conjugation U.matrix
  rwa [diagonal_one U] at h

private theorem center_parameters (v : U.rightParabolic)
    (hv : v.val ∈ (center (U.rightLocalImage.pCoreIn 2)).map (U.rightLocalImage.pCoreIn 2).subtype) :
    ∃ u : Parameters U.form, u.x=0 ∧ toParabolic U.matrix u = v := by
  let φ := U.rightParabolic.subtype.comp (toParabolic U.matrix)
  have hφ : Function.Injective φ := Subtype.val_injective.comp (toParabolic_injective U.matrix)
  have hQR : U.rightLocalImage.pCoreIn 2 = φ.range := by
    change Source.twoCore U.rightLocalImage = _
    rw [U.rightLocalImage_twoCore]
    exact MonoidHom.range_comp _ _ |>.symm
  obtain ⟨z,hz,hzv⟩ := hv
  obtain ⟨u,hu⟩ := hQR.le z.property
  have huv : φ u = v.val := hu.trans hzv
  have huc : u ∈ center (Parameters U.form) := by
    apply mem_center_iff.mpr
    intro w
    apply hφ
    rw [map_mul,map_mul,hu]
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨φ w,hQR.ge ⟨w,rfl⟩⟩)
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  exact ⟨u,(mem_center_iff_x_eq_zero U.form c hc u).mp huc,Subtype.ext huv⟩

/-- The nonidentity plane-core center is covered by the two literal parabolic classes. -/
theorem right_core_center_two_classes (v : U.rightParabolic)
    (hv : v.val ∈ (center (U.rightLocalImage.pCoreIn 2)).map (U.rightLocalImage.pCoreIn 2).subtype)
    (hv1 : v ≠ 1) : IsConj U.longInvolution v ∨ IsConj U.shortInvolution v := by
  obtain ⟨u,hu,rfl⟩ := center_parameters U v hv
  have hu1 : u ≠ 1 := fun he => hv1 (by rw [he,map_one])
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  obtain ⟨e⟩ := Representation.SL2.BinarySmall.nonempty_hermitianFieldEquiv (K := U.F) 2
    (by simpa using U.local_field_card)
  rcases central_two_types U.form c hc U.conjugation e U.matrix u hu hu1 with hh | hh
  · exact Or.inl hh.symm
  · rw [diagonal_one U] at hh
    exact Or.inr hh.symm

/-- Exactly two conjugacy classes exhaust the native projective involutions. -/
theorem involution_two_classes (u : U.Carrier) (hu : orderOf u = 2) :
    IsConj U.longInvolution.val u ∨ IsConj U.shortInvolution.val u := by
  obtain ⟨v,hv,hv2,hev⟩ := U.involution_to_right_core_center u hu
  have hv1 : v ≠ 1 := fun he => by simp [he] at hv2
  rcases U.right_core_center_two_classes v hv hv1 with h | h
  · exact Or.inl ((U.rightParabolic.subtype.map_isConj h).trans hev.symm)
  · exact Or.inr ((U.rightParabolic.subtype.map_isConj h).trans hev.symm)

/-- Native conjugacy on the plane-core center is already conjugacy in its endpoint. -/
theorem right_core_center_fusion (u v : U.rightParabolic)
    (hu : u.val ∈ (center (U.rightLocalImage.pCoreIn 2)).map (U.rightLocalImage.pCoreIn 2).subtype)
    (hv : v.val ∈ (center (U.rightLocalImage.pCoreIn 2)).map (U.rightLocalImage.pCoreIn 2).subtype) :
    IsConj u.val v.val ↔ IsConj u v := by
  constructor
  · intro h
    by_cases hu1 : u = 1
    · have hv1 : v = 1 := Subtype.ext (by simpa [hu1] using h.symm)
      rw [hu1,hv1]
    have hv1 : v ≠ 1 := by
      intro hv1
      apply hu1
      apply Subtype.ext
      simpa [hv1] using h
    rcases U.right_core_center_two_classes u hu hu1 with hzu | htu <;>
      rcases U.right_core_center_two_classes v hv hv1 with hzv | htv
    · exact hzu.symm.trans hzv
    · exact (U.long_short_not_isConj ((U.rightParabolic.subtype.map_isConj hzu).trans
        (h.trans (U.rightParabolic.subtype.map_isConj htv).symm))).elim
    · exact (U.long_short_not_isConj ((U.rightParabolic.subtype.map_isConj hzv).trans
        (h.symm.trans (U.rightParabolic.subtype.map_isConj htu).symm))).elim
    · exact htu.symm.trans htv
  · exact U.rightParabolic.subtype.map_isConj

/-- Every nonsingular central parameter belongs to the selected short class. -/
theorem nonsingular_parameter_isConj_short (u : Parameters U.form)
    (hu : u.x=0) (hd : u.z.det ≠ 0) :
    IsConj (toParabolic U.matrix u) U.shortInvolution := by
  have hu1 : u ≠ 1 := by
    intro he
    have hh : u.z.det = 0 := by rw [he]; simp
    exact hd hh
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  obtain ⟨e⟩ := Representation.SL2.BinarySmall.nonempty_hermitianFieldEquiv (K := U.F) 2
    (by simpa using U.local_field_card)
  obtain ⟨A,b,hb,he⟩ := central_normalize U.form c hc U.conjugation e u hu hu1
  have hd' := congrArg (fun v : Parameters U.form => v.z.det) he
  have hdet : (planeAdjoint U.form A.val).det = 1 := by
    change (A.val.map U.form.conj).transpose.det = 1
    rw [Matrix.det_transpose]
    exact (U.form.conj.map_det (A : Matrix (Fin 2) (Fin 2) U.F)).symm.trans
      ((congrArg U.form.conj A.property).trans (map_one _))
  simp only [planeAction_z,Matrix.det_mul,A.property,hdet,mul_one,one_mul] at hd'
  have hbne : b ≠ 0 := by
    have hh : u.z.det = b := by simpa [diagonalParameter,Matrix.det_fin_two] using hd'
    exact hh ▸ hd
  have h1 : IsConj (toParabolic U.matrix u) (toParabolic U.matrix (diagonalParameter U.form b hb)) :=
    isConj_iff.mpr ⟨planeSLParabolic U.form c hc U.matrix A,
      he ▸ planeSLParabolic_conjugation c hc U.matrix A u⟩
  have hh := h1.trans (diagonal_conjugate U.form c hc U.matrix b hb hbne)
  rwa [diagonal_one U] at hh

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

private theorem right_core_preserved (E : FiveExtension U) (a : MulAut U.Carrier)
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

/-- No full-extension automorphism fuses the two native involution classes. -/
theorem FiveExtension.long_short_not_isConj (E : FiveExtension U) :
    ¬ IsConj (E.baseHom U.longInvolution.val) (E.baseHom U.shortInvolution.val) := by
  intro h
  obtain ⟨g,hg⟩ := isConj_iff.mp h.symm
  have hh : g.val * MulAut.conj U.shortInvolution.val * g.val⁻¹ =
      MulAut.conj U.longInvolution.val := congrArg Subtype.val hg
  rw [aut_conjugate_inner] at hh
  have hf := five_conj_injective U hh
  obtain ⟨b,k,hk,hgk⟩ := E.factor g.val g.property
  obtain ⟨w,hw,hdw,hew⟩ := U.nonsingular_parameter_image k
    (right_core_preserved U E k hk.2) (InvolutionGeometry.shortParameter U.form) rfl
    (by rw [InvolutionGeometry.shortParameter_det]; exact one_ne_zero)
  have hb : b * (PlaneCore.Parameters.toParabolic U.matrix w).val * b⁻¹ = U.longInvolution.val := by
    rw [hgk] at hf
    change b * k U.shortInvolution.val * b⁻¹ = _ at hf
    change k U.shortInvolution.val = _ at hew
    rwa [hew] at hf
  have ht : IsConj U.shortInvolution.val (PlaneCore.Parameters.toParabolic U.matrix w).val :=
    U.rightParabolic.subtype.map_isConj (U.nonsingular_parameter_isConj_short w hw hdw).symm
  exact U.long_short_not_isConj (ht.trans (isConj_iff.mpr ⟨b,hb⟩)).symm

/-- Full-extension fusion of plane-core elements is exactly native endpoint fusion. -/
theorem FiveExtension.right_core_center_fusion (E : FiveExtension U) (u v : U.rightParabolic)
    (hu : u.val ∈ (center (U.rightLocalImage.pCoreIn 2)).map (U.rightLocalImage.pCoreIn 2).subtype)
    (hv : v.val ∈ (center (U.rightLocalImage.pCoreIn 2)).map (U.rightLocalImage.pCoreIn 2).subtype) :
    IsConj (E.baseHom u.val) (E.baseHom v.val) ↔ IsConj u v := by
  let f := E.baseHom.comp U.rightParabolic.subtype
  have hf : Function.Injective f :=
    (E.baseHom_injective (five_conj_injective U)).comp Subtype.val_injective
  constructor
  · intro h
    change IsConj (f u) (f v) at h
    by_cases hu1 : u = 1
    · have hv1 : f v = 1 := by simpa [hu1] using h.symm
      have he : v = 1 := hf (hv1.trans f.map_one.symm)
      rw [hu1,he]
    have hv1 : v ≠ 1 := by
      intro hv1
      have he : f u = 1 := by simpa [hv1] using h
      exact hu1 (hf (he.trans f.map_one.symm))
    rcases U.right_core_center_two_classes u hu hu1 with hzu | htu <;>
      rcases U.right_core_center_two_classes v hv hv1 with hzv | htv
    · exact hzu.symm.trans hzv
    · exact (FiveExtension.long_short_not_isConj U E ((f.map_isConj hzu).trans
        (h.trans (f.map_isConj htv).symm))).elim
    · exact (FiveExtension.long_short_not_isConj U E ((f.map_isConj hzv).trans
        (h.symm.trans (f.map_isConj htu).symm))).elim
    · exact htu.symm.trans htv
  · exact f.map_isConj

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
