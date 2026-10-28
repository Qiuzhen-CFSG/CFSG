module
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Conjugation
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.Flags

/-!
# Graph on the entire native plane residual

Entrywise Hermitian conjugation acts on all radical coordinates. The chosen
trace-one basis changes by the explicit radical element (x,z)=(0,I); this
accounts for the conjugation of the actual Levi section. Multiplication gives
the graph formula on the full residual, retaining the projective scalar kernel.

Source: the native matrix calculation for Aschbacher–Smith F.4.29(2),
printed p.289 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
open PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

def graphRadical : MulAut (Parameters J) where
  toFun u := ⟨fun i => J.conj (u.x i), u.z.map J.conj, by
    intro i j
    simpa only [Matrix.map_apply,map_add,map_mul,Parameters.conj_conj] using congrArg J.conj (u.relation i j)⟩
  invFun u := ⟨fun i => J.conj (u.x i), u.z.map J.conj, by
    intro i j
    simpa only [Matrix.map_apply,map_add,map_mul,Parameters.conj_conj] using congrArg J.conj (u.relation i j)⟩
  left_inv u := Parameters.ext (by ext i; exact J.conj_involutive _) (by ext i j; exact J.conj_involutive _)
  right_inv u := Parameters.ext (by ext i; exact J.conj_involutive _) (by ext i j; exact J.conj_involutive _)
  map_mul' u v := by
    apply Parameters.ext
    · ext i; exact map_add J.conj _ _
    · ext i j; simp [map_add,map_mul]

omit [CharP F 2] in
@[simp] theorem graphRadical_x (u : Parameters J) (i : Fin 2) :
    (graphRadical J u).x i = J.conj (u.x i) := rfl
omit [CharP F 2] in
@[simp] theorem graphRadical_z (u : Parameters J) (i j : Fin 2) :
    (graphRadical J u).z i j = J.conj (u.z i j) := rfl

theorem graph_toSU (hJ : J.form = 1) (u : Parameters J) :
    GraphFixed.matrixAut J hJ (Parameters.toSU hJ u) = Parameters.toSU hJ (graphRadical J u) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [GraphFixed.matrixAut_apply]
  change J.conj ((Parameters.ambientGL u).val i j) = (Parameters.ambientGL (graphRadical J u)).val i j
  rw [Parameters.ambientGL_val,Parameters.ambientGL_val]
  fin_cases i <;> fin_cases j <;> simp [Parameters.ambientMatrix]

/-- Radical element correcting conjugation of the chosen trace-one basis. -/
def basisShift : Parameters J := ⟨0,1,by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]⟩

theorem conj_planeBasis (c : F) (hc : c + J.conj c = 1) :
    GeneralLinearGroup.map J.conj.toRingHom (planeBasisGL c) =
      Parameters.ambientGL (basisShift J) * planeBasisGL c := by
  have hc' : J.conj c = c + 1 := by
    calc
      J.conj c = c + (c + J.conj c) := by simp [←add_assoc,CharTwo.add_self_eq_zero]
      _ = c + 1 := by rw [hc]
  apply Units.ext
  change (planeBasis c).map J.conj = (Parameters.ambientGL (basisShift J)).val * planeBasis c
  rw [Parameters.ambientGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBasis,Parameters.ambientMatrix,basisShift,Matrix.mul_apply,Fin.sum_univ_succ,hc',
      CharTwo.add_self_eq_zero,add_assoc]

omit [CharP F 2] in
theorem conj_planeBlock (A : GL (Fin 2) F) :
    GeneralLinearGroup.map J.conj.toRingHom (planeBlockGL J A) =
      planeBlockGL J (GeneralLinearGroup.map J.conj.toRingHom A) := by
  apply Units.ext
  have hd : (A.val.map J.conj).det = J.conj A.val.det := (J.conj.map_det A.val).symm
  have hi : (A.val.map J.conj)⁻¹ = A.val⁻¹.map J.conj := by
    have hm (B : GL (Fin 2) F) : (GeneralLinearGroup.map J.conj.toRingHom B).val =
        B.val.map J.conj := rfl
    have hh := (congrArg Units.val (map_inv (GeneralLinearGroup.map J.conj.toRingHom) A)).symm
    rw [GeneralLinearGroup.coe_inv,hm,hm,GeneralLinearGroup.coe_inv] at hh
    exact hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBlockGL,planeBlockMatrix,planeMiddleScalar,planeAdjoint,map_mul,map_inv₀,hd,hi]

theorem graph_planeLevi (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (A : GL (Fin 2) F) :
    GraphFixed.matrixAut J hJ (planeLeviSU J c hc hJ A) =
      Parameters.toSU hJ (basisShift J) *
        planeLeviSU J c hc hJ (GeneralLinearGroup.map J.conj.toRingHom A) *
          (Parameters.toSU hJ (basisShift J))⁻¹ := by
  apply Subtype.ext
  change GeneralLinearGroup.map J.conj.toRingHom
    (planeBasisGL c * planeBlockGL J A * (planeBasisGL c)⁻¹) = _
  rw [map_mul,map_mul,map_inv,conj_planeBasis J c hc,conj_planeBlock]
  change _ = Parameters.ambientGL (basisShift J) *
    (planeBasisGL c * planeBlockGL J (GeneralLinearGroup.map J.conj.toRingHom A) *
      (planeBasisGL c)⁻¹) * (Parameters.ambientGL (basisShift J))⁻¹
  group

omit [CharP F 2] in
/-- Entrywise conjugation commutes with the inclusion of SL₂ in GL₂. -/
theorem conj_planeSLtoGL (A : SpecialLinearGroup (Fin 2) F) :
    GeneralLinearGroup.map J.conj.toRingHom (planeSLtoGL A) =
      planeSLtoGL (SpecialLinearGroup.map J.conj.toRingHom A) := by
  apply Units.ext
  rfl

/-- The exact residual multiplication map into the native projective carrier. -/
def nativePlane (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    PlaneSemidirect J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (planeParabolic J).subtype.comp (planeSemidirectToParabolic J c hc hJ)

@[simp] theorem nativePlane_inl (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (u : Parameters J) :
    nativePlane J c hc hJ (SemidirectProduct.inl u) = project J (Parameters.toSU hJ u) := by
  change (planeSemidirectToParabolic J c hc hJ (SemidirectProduct.inl u)).val = _
  rw [planeSemidirectToParabolic_inl]
  rfl

@[simp] theorem nativePlane_inr (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (A : SpecialLinearGroup (Fin 2) F) :
    nativePlane J c hc hJ (SemidirectProduct.inr A) = project J (planeLeviSL J c hc hJ A) := by
  change (planeSemidirectToParabolic J c hc hJ (SemidirectProduct.inr A)).val = _
  rw [planeSemidirectToParabolic_inr]
  rfl

theorem graph_nativePlane_inl (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (u : Parameters J) :
    GraphFixed.projectiveAut J hJ (nativePlane J c hc hJ (SemidirectProduct.inl u)) =
      nativePlane J c hc hJ (SemidirectProduct.inl (graphRadical J u)) := by
  rw [nativePlane_inl,GraphFixed.projectiveAut_project,graph_toSU,nativePlane_inl]

/-- The chosen Levi is conjugated by the displayed radical element under graph. -/
theorem graph_nativePlane_inr (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (A : SpecialLinearGroup (Fin 2) F) :
    GraphFixed.projectiveAut J hJ (nativePlane J c hc hJ (SemidirectProduct.inr A)) =
      nativePlane J c hc hJ
        (SemidirectProduct.inl (basisShift J) *
          SemidirectProduct.inr (SpecialLinearGroup.map J.conj.toRingHom A) *
          (SemidirectProduct.inl (basisShift J))⁻¹) := by
  rw [map_mul,map_mul,map_inv,nativePlane_inl,nativePlane_inr,nativePlane_inr,
    GraphFixed.projectiveAut_project]
  change project J (GraphFixed.matrixAut J hJ (planeLeviSU J c hc hJ (planeSLtoGL A))) = _
  rw [graph_planeLevi,conj_planeSLtoGL,map_mul,map_mul,map_inv]
  rfl

/-- Literal coordinates of graph on the entire plane residual. -/
def graphPlaneCoordinates (p : PlaneSemidirect J) : PlaneSemidirect J :=
  SemidirectProduct.inl (graphRadical J p.left) * SemidirectProduct.inl (basisShift J) *
    SemidirectProduct.inr (SpecialLinearGroup.map J.conj.toRingHom p.right) *
    (SemidirectProduct.inl (basisShift J))⁻¹

@[simp] theorem graphPlaneCoordinates_right (p : PlaneSemidirect J) :
    (graphPlaneCoordinates J p).right = SpecialLinearGroup.map J.conj.toRingHom p.right := by
  simp [graphPlaneCoordinates]

theorem graph_nativePlane (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (p : PlaneSemidirect J) :
    GraphFixed.projectiveAut J hJ (nativePlane J c hc hJ p) =
      nativePlane J c hc hJ (graphPlaneCoordinates J p) := by
  have hp : nativePlane J c hc hJ p =
      nativePlane J c hc hJ (SemidirectProduct.inl p.left) *
        nativePlane J c hc hJ (SemidirectProduct.inr p.right) := by
    rw [←map_mul,SemidirectProduct.inl_left_mul_inr_right]
  rw [hp,map_mul,graph_nativePlane_inl,graph_nativePlane_inr]
  simp only [graphPlaneCoordinates,map_mul,map_inv,mul_assoc]
end Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
