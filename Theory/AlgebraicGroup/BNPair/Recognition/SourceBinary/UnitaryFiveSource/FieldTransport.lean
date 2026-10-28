module
public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel
public import Mathlib.Algebra.Field.TransferInstance

/-!
# Coefficient transport of the complete U₅ flag

An isomorphism of the coefficient fields compatible with the Hermitian
involutions preserves determinant-one isometries, their entire scalar
kernels and both literal flag stabilizers. The resulting projective map
therefore preserves the full overlap. This permits the finite source field
in any universe to be represented in the published model's small universe.
Source: the coefficient description of Fong--Seitz II (8C), pp.202--210.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource.FieldTransport
variable {F E : Type*} [Field F] [Field E]
  (e : F ≃+* E) (J : HermitianForm 5 F) (K : HermitianForm 5 E)
  (hc : ∀ x, e (J.conj x) = K.conj (e x)) (hform : J.form.map e = K.form)

@[expose] def coefficientGL : GL (Fin 5) F ≃* GL (Fin 5) E :=
  { GeneralLinearGroup.map e.toRingHom with
    invFun := GeneralLinearGroup.map e.symm.toRingHom
    left_inv := by intro g; ext i j; exact e.symm_apply_apply (g i j)
    right_inv := by intro g; ext i j; exact e.apply_symm_apply (g i j) }

include hc hform in
theorem coefficient_mem (a : GL (Fin 5) F) :
    coefficientGL e a ∈ K.specialSubgroup ↔ a ∈ J.specialSubgroup := by
  rw [K.mem_specialSubgroup_iff,J.mem_specialSubgroup_iff]
  have hadj : K.conjTranspose (coefficientGL e a).val = (J.conjTranspose a.val).map e := by
    ext i j
    exact (hc (a.val j i)).symm
  have hval : (coefficientGL e a).val = a.val.map e := rfl
  have hu : K.conjTranspose (coefficientGL e a).val*K.form*(coefficientGL e a).val = K.form ↔
      J.conjTranspose a.val*J.form*a.val = J.form := by
    rw [hadj,hval,←hform,←Matrix.map_mul,←Matrix.map_mul]
    exact e.toEquiv.mapMatrix.injective.eq_iff
  rw [hu]
  apply and_congr_right
  intro _
  change GeneralLinearGroup.det (GeneralLinearGroup.map e.toRingHom a) = 1 ↔ _
  rw [GeneralLinearGroup.map_det]
  constructor
  · intro hh
    apply Units.ext
    apply e.injective
    simpa using congrArg Units.val hh
  · intro hh
    rw [hh,map_one]

/-- Coefficient transport with a public matrix-entry specification. -/
@[expose] def specialEquiv : J.specialSubgroup ≃* K.specialSubgroup where
  toFun a := ⟨coefficientGL e a.val,(coefficient_mem e J K hc hform a.val).2 a.property⟩
  invFun a := ⟨(coefficientGL e).symm a.val,
    (coefficient_mem e J K hc hform _).1 (by simp)⟩
  left_inv a := by ext; simp
  right_inv a := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem specialEquiv_apply (a : J.specialSubgroup) (i j : Fin 5) :
    (specialEquiv e J K hc hform a).val.val i j = e (a.val.val i j) := rfl

private theorem kernel_iff (a : J.specialSubgroup) :
    specialEquiv e J K hc hform a ∈ (project K).ker ↔ a ∈ (project J).ker := by
  have aux (U : HermitianForm 5 F) (b : U.specialSubgroup) :
      b ∈ (project U).ker ↔ b.val ∈ center (GL (Fin 5) F) := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro hb
      exact ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val hb)
    · intro hb
      exact Subtype.ext (ProjGenLinGroup.mk_eq_one.mpr hb)
  have aux' (b : K.specialSubgroup) :
      b ∈ (project K).ker ↔ b.val ∈ center (GL (Fin 5) E) := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro hb
      exact ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val hb)
    · intro hb
      exact Subtype.ext (ProjGenLinGroup.mk_eq_one.mpr hb)
  rw [aux',aux]
  change coefficientGL e a.val ∈ center (GL (Fin 5) E) ↔ a.val ∈ center (GL (Fin 5) F)
  constructor
  · intro ha
    have hz := (centerCongr (coefficientGL e).symm ⟨_,ha⟩).property
    change (coefficientGL e).symm (coefficientGL e a.val) ∈ center (GL (Fin 5) F) at hz
    rwa [MulEquiv.symm_apply_apply] at hz
  · intro ha
    exact (centerCongr (coefficientGL e) ⟨_,ha⟩).property

private theorem kernel_map : (project J).ker.map (specialEquiv e J K hc hform).toMonoidHom =
    (project K).ker := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact (kernel_iff e J K hc hform b).2 hb
  · intro ha
    obtain ⟨b,rfl⟩ := (specialEquiv e J K hc hform).surjective a
    exact ⟨b,(kernel_iff e J K hc hform b).1 ha,rfl⟩

/-- The projective transport keeps the complete canonical scalar quotient. -/
def projectiveEquiv : ProjectiveSpecialUnitaryMatrixGroup J ≃*
    ProjectiveSpecialUnitaryMatrixGroup K :=
  (QuotientGroup.quotientKerEquivOfSurjective (project J) (project_surjective J)).symm.trans
    ((QuotientGroup.congr _ _ (specialEquiv e J K hc hform) (kernel_map e J K hc hform)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (project K) (project_surjective K)))

@[simp] theorem projectiveEquiv_project (a : J.specialSubgroup) :
    projectiveEquiv e J K hc hform (project J a) = project K (specialEquiv e J K hc hform a) := by
  let f := QuotientGroup.quotientKerEquivOfSurjective (project J) (project_surjective J)
  have ha : f (QuotientGroup.mk a) = project J a := rfl
  rw [←ha]
  change (QuotientGroup.quotientKerEquivOfSurjective (project K) (project_surjective K)) ((QuotientGroup.congr _ _ (specialEquiv e J K hc hform) (kernel_map e J K hc hform))
    (f.symm (f (QuotientGroup.mk a)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

private theorem stabilizer_iff
    (V : Submodule F (Fin 5 → F)) (W : Submodule E (Fin 5 → E))
    (hv : ∀ v : Fin 5 → F, (fun i => e (v i)) ∈ W ↔ v ∈ V) (a : J.specialSubgroup) :
    specialEquiv e J K hc hform a ∈ specialStabilizer K W ↔ a ∈ specialStabilizer J V := by
  rw [mem_specialStabilizer_iff,mem_specialStabilizer_iff]
  have he (v : Fin 5 → F) :
      (specialEquiv e J K hc hform a).val.val *ᵥ (fun i => e (v i)) =
        fun i => e ((a.val.val *ᵥ v) i) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, specialEquiv_apply,map_sum,map_mul]
  constructor
  · intro h v
    simpa only [he,hv] using h (fun i => e (v i))
  · intro h w
    let v : Fin 5 → F := fun i => e.symm (w i)
    have hw : w = fun i => e (v i) := by ext i; simp [v]
    rw [hw,he,hv,hv]
    exact h v

private theorem map_specialStabilizer
    (V : Submodule F (Fin 5 → F)) (W : Submodule E (Fin 5 → E))
    (hv : ∀ v : Fin 5 → F, (fun i => e (v i)) ∈ W ↔ v ∈ V) :
    (specialStabilizer J V).map (specialEquiv e J K hc hform).toMonoidHom = specialStabilizer K W := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact (stabilizer_iff e J K hc hform V W hv b).2 hb
  · intro ha
    obtain ⟨b,rfl⟩ := (specialEquiv e J K hc hform).surjective a
    exact ⟨b,(stabilizer_iff e J K hc hform V W hv b).1 ha,rfl⟩

private theorem map_parabolic
    (V : Submodule F (Fin 5 → F)) (W : Submodule E (Fin 5 → E))
    (hv : ∀ v : Fin 5 → F, (fun i => e (v i)) ∈ W ↔ v ∈ V) :
    (parabolic J V).map (projectiveEquiv e J K hc hform).toMonoidHom = parabolic K W := by
  have he : (projectiveEquiv e J K hc hform).toMonoidHom.comp (project J) =
      (project K).comp (specialEquiv e J K hc hform).toMonoidHom := by
    apply MonoidHom.ext
    intro a
    exact projectiveEquiv_project e J K hc hform a
  change ((specialStabilizer J V).map (project J)).map _ = (specialStabilizer K W).map _
  rw [Subgroup.map_map,he,←Subgroup.map_map,map_specialStabilizer e J K hc hform V W hv]

/-- The literal isotropic line is preserved by coefficient transport. -/
theorem map_line : (lineParabolic J).map (projectiveEquiv e J K hc hform).toMonoidHom = lineParabolic K := by
  apply map_parabolic
  intro v
  change (e (v 1) = e (v 0) ∧ e (v 2) = 0 ∧ e (v 3) = 0 ∧ e (v 4) = 0) ↔ _
  simp only [e.injective.eq_iff,map_eq_zero]
  rfl

/-- The literal isotropic plane is preserved by coefficient transport. -/
theorem map_plane : (planeParabolic J).map (projectiveEquiv e J K hc hform).toMonoidHom = planeParabolic K := by
  apply map_parabolic
  intro v
  change (e (v 1) = e (v 0) ∧ e (v 3) = e (v 2) ∧ e (v 4) = 0) ↔ _
  simp only [e.injective.eq_iff,map_eq_zero]
  rfl

/-- Both transported endpoints retain their whole common Borel. -/
theorem map_overlap : (lineParabolic J ⊓ planeParabolic J).map
    (projectiveEquiv e J K hc hform).toMonoidHom = lineParabolic K ⊓ planeParabolic K := by
  rw [Subgroup.map_inf _ _ _ (projectiveEquiv e J K hc hform).injective,map_line,map_plane]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource.FieldTransport
