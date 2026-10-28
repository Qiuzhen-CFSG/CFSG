module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.Conjugation
public import Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.Restriction
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry

/-!
# Unitary coordinate changes and the native five-dimensional flag

Conjugation by a unitary matrix carries each projective parabolic to the
stabilizer of the literal inverse-image subspace. A determinant correction
supported on the fifth coordinate fixes the native line and plane and
turns a unitary matrix into a special unitary matrix. The source consumer
uses the proved inner-flag theorem to recover vector-space preservation
from abstract preservation of the two projective parabolics.

For a unitary coboundary, pulling this flag back along the descent basis
makes it invariant under coefficient conjugation, retaining its dimensions
and total isotropy. The projective scalar kernel is retained throughout.
Source: Aschbacher–Smith F.4.29(2), F.4.37(2), printed pp.289,293 of
refs/quasithin.pdf. The determinant norm argument follows the analogous
SU3/ProjectiveOuterInvolutions/NormalForm/Diagonal.lean calculation.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.Descent
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

@[expose] def unitaryLinear (u : J.unitarySubgroup) : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 5 → F)
    (GeneralLinearGroup.toLin u.val)

theorem unitaryLinear_apply (u : J.unitarySubgroup) (x : Fin 5 → F) :
    unitaryLinear J u x = u.val.val *ᵥ x := rfl

@[expose] def Preserves (u : J.unitarySubgroup) (W : Submodule F (Fin 5 → F)) : Prop :=
  ∀ x, unitaryLinear J u x ∈ W ↔ x ∈ W

theorem unitaryConj_mul (u v : J.unitarySubgroup) :
    unitaryConj J (u*v) = unitaryConj J u * unitaryConj J v := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp only [MulAut.mul_apply, unitaryConj_apply_val, Subgroup.coe_mul, map_mul,
    _root_.mul_inv_rev]
  group

theorem unitaryConj_special (g : J.specialSubgroup) :
    unitaryConj J ⟨g.val,g.property.1⟩ = MulAut.conj (project J g) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [unitaryConj_apply_val]
  rfl

theorem project_mem_parabolic (W : Submodule F (Fin 5 → F)) (g : J.specialSubgroup) :
    project J g ∈ parabolic J W ↔ g ∈ specialStabilizer J W := by
  constructor
  · rintro ⟨a,ha,he⟩
    have hk : a⁻¹*g ∈ (project J).ker := by simp [MonoidHom.mem_ker,he]
    have hh := (specialStabilizer J W).mul_mem ha
      (ker_project_le_specialStabilizer J W hk)
    simpa only [←mul_assoc,mul_inv_cancel,one_mul] using hh
  · intro hg
    exact mem_map_of_mem _ hg

theorem unitaryConj_mem_parabolic (u : J.unitarySubgroup)
    (W : Submodule F (Fin 5 → F)) (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    unitaryConj J u x ∈ parabolic J W ↔
      x ∈ parabolic J (W.comap (unitaryLinear J u).toLinearMap) := by
  obtain ⟨g,rfl⟩ := project_surjective J x
  rw [unitaryConj_project,project_mem_parabolic,project_mem_parabolic,
    mem_specialStabilizer_iff,mem_specialStabilizer_iff]
  simp only [specialUnitaryConj_val, Units.val_mul]
  constructor
  · intro h y
    have hh := h (unitaryLinear J u y)
    change u.val.val *ᵥ (g.val.val *ᵥ y) ∈ W ↔ u.val.val *ᵥ y ∈ W
    simpa only [unitaryLinear_apply, Matrix.mulVec_mulVec, mul_assoc, Units.inv_mul, mul_one] using hh
  · intro h y
    have hh := h ((u.val⁻¹).val *ᵥ y)
    change u.val.val *ᵥ (g.val.val *ᵥ ((u.val⁻¹).val *ᵥ y)) ∈ W ↔
      u.val.val *ᵥ ((u.val⁻¹).val *ᵥ y) ∈ W at hh
    simpa only [mulVec_mulVec,mul_assoc,Units.mul_inv,one_mulVec] using hh

theorem unitaryConj_parabolic_comap (u : J.unitarySubgroup)
    (W : Submodule F (Fin 5 → F)) :
    (parabolic J W).comap (unitaryConj J u).toMonoidHom =
      parabolic J (W.comap (unitaryLinear J u).toLinearMap) := by
  ext x
  exact unitaryConj_mem_parabolic J u W x

theorem unitaryConj_parabolic_of_preserves (u : J.unitarySubgroup)
    (W : Submodule F (Fin 5 → F)) (h : Preserves J u W) :
    (parabolic J W).map (unitaryConj J u).toMonoidHom = parabolic J W := by
  have hc : (parabolic J W).comap (unitaryConj J u).toMonoidHom = parabolic J W := by
    rw [unitaryConj_parabolic_comap]
    congr 1
    ext x
    exact h x
  calc
    _ = ((parabolic J W).comap (unitaryConj J u).toMonoidHom).map
        (unitaryConj J u).toMonoidHom := congrArg _ hc.symm
    _ = _ := Subgroup.map_comap_eq_self_of_surjective (unitaryConj J u).surjective _

private theorem det_norm_one (u : J.unitarySubgroup) :
    J.conj u.val.val.det * u.val.val.det = 1 := by
  have h := congrArg Matrix.det ((J.mem_unitarySubgroup_iff _).mp u.property)
  have hadj : (J.conjTranspose u.val.val).det = J.conj u.val.val.det := by
    change ((u.val.val.map J.conj).transpose).det = _
    rw [Matrix.det_transpose]
    exact (J.conj.map_det _).symm
  rw [Matrix.det_mul, Matrix.det_mul, hadj] at h
  apply mul_right_cancel₀ J.form_nondegenerate
  calc
    (J.conj u.val.val.det * u.val.val.det) * J.form.det =
        J.conj u.val.val.det * J.form.det * u.val.val.det := by ring
    _ = 1 * J.form.det := by simpa using h

private def correctionGL (u : J.unitarySubgroup) : GL (Fin 5) F where
  val := diagonal ![1,1,1,1,u.val.val.det⁻¹]
  inv := diagonal ![1,1,1,1,u.val.val.det]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [u.val.det_ne_zero]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [u.val.det_ne_zero]

def flagDetCorrection (hJ : J.form=1) (u : J.unitarySubgroup) : J.unitarySubgroup :=
  ⟨correctionGL J u, by
    rw [J.mem_unitarySubgroup_iff,hJ]
    have hn : J.conj (u.val.val.det⁻¹) * u.val.val.det⁻¹ = 1 := by
      rw [map_inv₀,←mul_inv,det_norm_one,inv_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [correctionGL,HermitianForm.conjTranspose,Matrix.mul_apply,Fin.sum_univ_succ]
    simpa only [map_inv₀] using hn⟩

theorem flagDetCorrection_det (hJ : J.form=1) (u : J.unitarySubgroup) :
    GeneralLinearGroup.det (flagDetCorrection J hJ u).val =
      (GeneralLinearGroup.det u.val)⁻¹ := by
  apply Units.ext
  simp [flagDetCorrection,correctionGL,GeneralLinearGroup.val_det_apply,
    Matrix.det_diagonal,Fin.prod_univ_succ]

theorem flagDetCorrection_line (hJ : J.form=1) (u : J.unitarySubgroup) :
    Preserves J (flagDetCorrection J hJ u) (line F) := by
  intro x
  simp [unitaryLinear_apply,flagDetCorrection,correctionGL,mulVec_diagonal,line,
    inv_ne_zero u.val.det_ne_zero]

theorem flagDetCorrection_plane (hJ : J.form=1) (u : J.unitarySubgroup) :
    Preserves J (flagDetCorrection J hJ u) (plane F) := by
  intro x
  simp [unitaryLinear_apply,flagDetCorrection,correctionGL,mulVec_diagonal,plane,
    inv_ne_zero u.val.det_ne_zero]

@[expose] def flagSpecialCorrection (hJ : J.form=1) (u : J.unitarySubgroup) : J.specialSubgroup :=
  ⟨u.val*(flagDetCorrection J hJ u).val,by
    constructor
    · exact J.unitarySubgroup.mul_mem u.property (flagDetCorrection J hJ u).property
    · change GeneralLinearGroup.det (u.val*(flagDetCorrection J hJ u).val)=1
      rw [map_mul,flagDetCorrection_det,mul_inv_cancel]⟩

theorem preserves_of_specialCorrection (hJ : J.form=1) (u : J.unitarySubgroup)
    (W : Submodule F (Fin 5 → F)) (hd : Preserves J (flagDetCorrection J hJ u) W)
    (hs : flagSpecialCorrection J hJ u ∈ specialStabilizer J W) : Preserves J u W := by
  rw [mem_specialStabilizer_iff] at hs
  intro x
  obtain ⟨y,rfl⟩ := (unitaryLinear J (flagDetCorrection J hJ u)).surjective x
  have hh : unitaryLinear J u (unitaryLinear J (flagDetCorrection J hJ u) y) ∈ W ↔ y ∈ W := by
    simpa only [flagSpecialCorrection,Units.val_mul,mulVec_mulVec,unitaryLinear_apply] using hs y
  exact hh.trans (hd y).symm

theorem conj_line (x : Fin 5 → F) : J.conj ∘ x ∈ line F ↔ x ∈ line F := by
  simp [line,J.conj.injective.eq_iff]

theorem conj_plane (x : Fin 5 → F) : J.conj ∘ x ∈ plane F ↔ x ∈ plane F := by
  simp [plane,J.conj.injective.eq_iff]

private theorem graph_matrix_mulVec (hJ : J.form=1) (g : J.specialSubgroup)
    (x : Fin 5 → F) :
    (GraphFixed.matrixAut J hJ g).val.val *ᵥ x =
      J.conj ∘ (g.val.val *ᵥ (J.conj ∘ x)) := by
  have hm : (GraphFixed.matrixAut J hJ g).val.val = g.val.val.map J.conj := by
    ext i j
    exact GraphFixed.matrixAut_apply J hJ g i j
  rw [hm]
  ext i
  symm
  change J.conj.toRingHom ((g.val.val *ᵥ (J.conj ∘ x)) i) = _
  rw [RingHom.map_mulVec]
  congr 2
  exact funext (fun j => J.conj_involutive (x j))

theorem graph_parabolic (hJ : J.form=1) (W : Submodule F (Fin 5 → F))
    (hW : ∀ x, J.conj ∘ x ∈ W ↔ x ∈ W) :
    (parabolic J W).map (GraphFixed.projectiveAut J hJ).toMonoidHom = parabolic J W := by
  have hm (x : ProjectiveSpecialUnitaryMatrixGroup J) :
      GraphFixed.projectiveAut J hJ x ∈ parabolic J W ↔ x ∈ parabolic J W := by
    obtain ⟨g,rfl⟩ := project_surjective J x
    rw [GraphFixed.projectiveAut_project,project_mem_parabolic,project_mem_parabolic,
      mem_specialStabilizer_iff,mem_specialStabilizer_iff]
    constructor
    · intro h y
      have hh := h (J.conj ∘ y)
      rw [graph_matrix_mulVec,hW,hW] at hh
      have hy : J.conj ∘ (J.conj ∘ y) = y := funext (fun i => J.conj_involutive (y i))
      rwa [hy] at hh
    · intro h y
      rw [graph_matrix_mulVec,hW,h (J.conj ∘ y),hW]
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact (hm x).mpr hx
  · intro x hx
    obtain ⟨y,rfl⟩ := (GraphFixed.projectiveAut J hJ).surjective x
    exact ⟨y,(hm y).mp hx,rfl⟩

theorem graph_flag (hJ : J.form=1) :
    GraphFixed.projectiveAut J hJ ∈
      ClassicalUnitary.NativeAmalgamActions.flagAutomorphisms (lineParabolic J) (planeParabolic J) :=
  ⟨graph_parabolic J hJ (line F) (conj_line J),
    graph_parabolic J hJ (plane F) (conj_plane J)⟩

theorem unitaryLinear_pairing (hJ : J.form=1) (u : J.unitarySubgroup)
    (x y : Fin 5 → F) :
    IsotropicGeometry.pairing J (unitaryLinear J u x) (unitaryLinear J u y) =
      IsotropicGeometry.pairing J x y := by
  have hu := (J.mem_unitarySubgroup_iff u.val).mp u.property
  rw [hJ,mul_one] at hu
  change (fun i => J.conj ((u.val.val *ᵥ x) i)) ⬝ᵥ (u.val.val *ᵥ y) = _
  rw [show (fun i => J.conj ((u.val.val *ᵥ x) i)) =
      (u.val.val.map J.conj) *ᵥ (fun i => J.conj (x i)) from
    funext (RingHom.map_mulVec J.conj.toRingHom u.val.val x)]
  rw [←vecMul_transpose,←dotProduct_mulVec,mulVec_mulVec]
  change (fun i => J.conj (x i)) ⬝ᵥ (J.conjTranspose u.val.val*u.val.val) *ᵥ y = _
  rw [hu,one_mulVec]
  rfl

/-- The preimage flag under a descent basis is stable under coefficient conjugation. -/
theorem coboundary_comap_conj (u v : J.unitarySubgroup)
    (huv : u.val=v.val*(GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹)
    (W : Submodule F (Fin 5 → F)) (huW : Preserves J u W)
    (hW : ∀ x, J.conj ∘ x ∈ W ↔ x ∈ W) (x : Fin 5 → F) :
    J.conj ∘ x ∈ W.comap (unitaryLinear J v).toLinearMap ↔
      x ∈ W.comap (unitaryLinear J v).toLinearMap := by
  have he : u.val*GeneralLinearGroup.map J.conj.toRingHom v.val=v.val := by
    rw [huv]
    group
  have hvx : unitaryLinear J v (J.conj ∘ x) =
      unitaryLinear J u (J.conj ∘ unitaryLinear J v x) := by
    rw [unitaryLinear_apply,unitaryLinear_apply,unitaryLinear_apply]
    have hm : J.conj ∘ (v.val.val *ᵥ x) = v.val.val.map J.conj *ᵥ (J.conj ∘ x) :=
      funext (RingHom.map_mulVec J.conj.toRingHom v.val.val x)
    rw [hm,mulVec_mulVec]
    have he' : u.val.val*(v.val.val.map J.conj)=v.val.val := congrArg Units.val he
    rw [he']
  change unitaryLinear J v (J.conj ∘ x) ∈ W ↔ unitaryLinear J v x ∈ W
  rw [hvx,huW,hW]

theorem unitary_comap_finrank (u : J.unitarySubgroup) (W : Submodule F (Fin 5 → F)) :
    Module.finrank F (W.comap (unitaryLinear J u).toLinearMap)=Module.finrank F W := by
  rw [Submodule.comap_equiv_eq_map_symm]
  exact (unitaryLinear J u).symm.finrank_map_eq W

theorem unitary_comap_isotropic (hJ : J.form=1) (u : J.unitarySubgroup)
    (W : Submodule F (Fin 5 → F))
    (hW : ∀ x ∈ W, ∀ y ∈ W, IsotropicGeometry.pairing J x y=0) :
    ∀ x ∈ W.comap (unitaryLinear J u).toLinearMap,
      ∀ y ∈ W.comap (unitaryLinear J u).toLinearMap,
        IsotropicGeometry.pairing J x y=0 := by
  intro x hx y hy
  rw [←unitaryLinear_pairing J hJ u]
  exact hW _ hx _ hy

end Theory.SpecificGroups.UnitaryFive.Descent
