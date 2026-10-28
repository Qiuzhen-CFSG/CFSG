module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.GraphCoordinates

/-!
# A unitary representative for the whole plane-radical scalar

In the existing hyperbolic basis, diag(k,k,1,conj(k)⁻¹,conj(k)⁻¹)
is unitary for every nonzero k. It preserves the native line and plane,
acts on every radical coordinate by (x,z) ↦ (kx,k·conj(k)z), and centralizes
the actual SL₂ Levi. Conjugating back by the trace-one basis gives a single
five-dimensional unitary matrix. No determinant-one condition or injectivity
of the projective scalar quotient is imposed.

Source: the coordinate reconstruction of Aschbacher–Smith F.4.29(2),
printed p.289 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
open PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- Scalar on the entire plane radical, retaining its norm on the matrix coordinate. -/
def scalarParameter (k : F) (u : Parameters J) : Parameters J where
  x := k • u.x
  z := (k * J.conj k) • u.z
  relation := by
    intro i j
    simp only [Pi.smul_apply, Matrix.smul_apply,smul_eq_mul,map_mul]
    rw [J.conj_involutive k]
    linear_combination (k * J.conj k) * u.relation i j

/-- The unitary diagonal has no determinant-one restriction. -/
def scalarDiagonal : Fˣ →* GL (Fin 5) F where
  toFun k :=
    { val := diagonal ![(k:F),(k:F),1,J.conj (k:F)⁻¹,J.conj (k:F)⁻¹]
      inv := diagonal ![(k:F)⁻¹,(k:F)⁻¹,1,J.conj (k:F),J.conj (k:F)]
      val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [(map_ne_zero J.conj).mpr k.ne_zero]
      inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [(map_ne_zero J.conj).mpr k.ne_zero] }
  map_one' := by apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' k l := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [map_mul,mul_comm]

omit [CharP F 2] in
private theorem scalarDiagonal_preserves (k : Fˣ) :
    J.conjTranspose (scalarDiagonal J k).val * planeGram * (scalarDiagonal J k).val = planeGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarDiagonal,HermitianForm.conjTranspose,planeGram,Matrix.mul_apply,Fin.sum_univ_succ,
      (map_ne_zero J.conj).mpr k.ne_zero]

private theorem scalar_conjugate_mem (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (k : Fˣ) :
    planeBasisGL c * scalarDiagonal J k * (planeBasisGL c)⁻¹ ∈ J.unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff]
  change J.conjTranspose (planeBasis c * (scalarDiagonal J k).val * planeBasisInv c) * J.form *
    (planeBasis c * (scalarDiagonal J k).val * planeBasisInv c) = J.form
  have hct (X Y : Matrix (Fin 5) (Fin 5) F) :
      J.conjTranspose (X*Y) = J.conjTranspose Y * J.conjTranspose X := by
    change ((X*Y).map J.conj).transpose = (Y.map J.conj).transpose * (X.map J.conj).transpose
    rw [Matrix.map_mul,Matrix.transpose_mul]
  have hgram : J.conjTranspose (planeBasis c)*J.form*planeBasis c=planeGram := planeBasis_gram J c hc hJ
  have hi : J.conjTranspose (planeBasisInv c)*J.conjTranspose (planeBasis c)=1 := by
    rw [←hct,planeBasis_mul_inv]
    change ((1 : Matrix (Fin 5) (Fin 5) F).map J.conj).transpose = 1
    simp
  rw [hct,hct]
  calc
    _ = J.conjTranspose (planeBasisInv c) *
        (J.conjTranspose (scalarDiagonal J k).val *
          (J.conjTranspose (planeBasis c)*J.form*planeBasis c) * (scalarDiagonal J k).val) * planeBasisInv c := by
            simp only [mul_assoc]
    _ = J.conjTranspose (planeBasisInv c)*planeGram*planeBasisInv c := by
      rw [hgram,scalarDiagonal_preserves]
    _ = J.form := by
      rw [←hgram]
      calc
        _ = (J.conjTranspose (planeBasisInv c)*J.conjTranspose (planeBasis c))*J.form*
            (planeBasis c*planeBasisInv c) := by simp only [mul_assoc]
        _ = _ := by rw [hi,planeBasis_mul_inv]; simp

/-- One actual five-dimensional unitary representative of every radical scalar. -/
def scalarUnitary (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) : Fˣ →* J.unitarySubgroup :=
  (((MulAut.conj (planeBasisGL c)).toMonoidHom).comp (scalarDiagonal J)).codRestrict _
    (by intro k; exact scalar_conjugate_mem J c hc hJ k)

theorem scalarUnitary_on_plane (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (k : Fˣ) (v : Fin 5 → F) (hv : v ∈ plane F) :
    Descent.unitaryLinear J (scalarUnitary J c hc hJ k) v = (k:F) • v := by
  obtain ⟨h1,h3,h4⟩ := hv
  change (planeBasis c * (scalarDiagonal J k).val * planeBasisInv c) *ᵥ v = _
  rw [←mulVec_mulVec,←mulVec_mulVec]
  have hw : planeBasisInv c *ᵥ v = ![v 0,v 2,0,0,0] := by
    ext i
    fin_cases i <;> simp [planeBasisInv,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h1,h3,h4,
      add_mul,CharTwo.add_self_eq_zero,add_assoc,add_left_comm]
  rw [hw]
  ext i
  fin_cases i <;> simp [scalarDiagonal,planeBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h1,h3,h4]

theorem scalarUnitary_preserves (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (k : Fˣ) (W : Submodule F (Fin 5 → F)) (hW : W ≤ plane F) :
    Descent.Preserves J (scalarUnitary J c hc hJ k) W := by
  intro v
  constructor
  · intro hv
    have hh := scalarUnitary_on_plane J c hc hJ k⁻¹ _ (hW hv)
    have hinv : Descent.unitaryLinear J (scalarUnitary J c hc hJ k⁻¹)
        (Descent.unitaryLinear J (scalarUnitary J c hc hJ k) v) = v := by
      rw [map_inv]
      change (scalarUnitary J c hc hJ k).val.inv *ᵥ ((scalarUnitary J c hc hJ k).val.val *ᵥ v) = v
      rw [mulVec_mulVec,(scalarUnitary J c hc hJ k).val.inv_val,one_mulVec]
    rw [hinv] at hh
    rw [hh]
    exact W.smul_mem ((k⁻¹:Fˣ):F) hv
  · intro hv
    rw [scalarUnitary_on_plane J c hc hJ k v (hW hv)]
    exact W.smul_mem _ hv

/-- The representative preserves both full projective parabolics. -/
theorem scalarUnitary_flag (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) (k : Fˣ) :
    Descent.unitaryConj J (scalarUnitary J c hc hJ k) ∈
      Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.flagAutomorphisms
        (lineParabolic J) (planeParabolic J) :=
  ⟨Descent.unitaryConj_parabolic_of_preserves J _ _
      (scalarUnitary_preserves J c hc hJ k _ (line_le_plane F)),
    Descent.unitaryConj_parabolic_of_preserves J _ _
      (scalarUnitary_preserves J c hc hJ k _ le_rfl)⟩

private theorem scalarDiagonal_radical (k : Fˣ) (u : Parameters J) :
    scalarDiagonal J k * Parameters.toGL u * (scalarDiagonal J k)⁻¹ =
      Parameters.toGL (scalarParameter J (k:F) u) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Units.ext
  change diagonal ![(k:F),(k:F),1,J.conj (k:F)⁻¹,J.conj (k:F)⁻¹] * Parameters.matrix u =
    Parameters.matrix (scalarParameter J (k:F) u) *
      diagonal ![(k:F),(k:F),1,J.conj (k:F)⁻¹,J.conj (k:F)⁻¹]
  ext i j
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [Parameters.matrix,scalarParameter,map_mul,(map_ne_zero J.conj).mpr k.ne_zero,
      mul_assoc,mul_comm,mul_left_comm]
  all_goals field_simp

omit [CharP F 2] in
private theorem scalarDiagonal_levi (k : Fˣ) (A : SpecialLinearGroup (Fin 2) F) :
    Commute (scalarDiagonal J k) (planeBlockGL J (planeSLtoGL A)) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarDiagonal,planeBlockGL,planeBlockMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm]

theorem scalarUnitary_radical (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (k : Fˣ) (u : Parameters J) :
    Descent.unitaryConj J (scalarUnitary J c hc hJ k) (project J (Parameters.toSU hJ u)) =
      project J (Parameters.toSU hJ (scalarParameter J (k:F) u)) := by
  rw [Descent.unitaryConj_project]
  congr 1
  apply Subtype.ext
  rw [Descent.specialUnitaryConj_val]
  change (planeBasisGL c * scalarDiagonal J k * (planeBasisGL c)⁻¹) * Parameters.ambientGL u *
    (planeBasisGL c * scalarDiagonal J k * (planeBasisGL c)⁻¹)⁻¹ = Parameters.ambientGL _
  rw [Parameters.ambientGL_eq_planeBasis c,Parameters.ambientGL_eq_planeBasis c]
  have hh := congrArg (MulAut.conj (planeBasisGL c)) (scalarDiagonal_radical J k u)
  simp only [map_mul,map_inv] at hh
  exact hh

theorem scalarUnitary_levi (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (k : Fˣ) (A : SpecialLinearGroup (Fin 2) F) :
    Descent.unitaryConj J (scalarUnitary J c hc hJ k) (project J (planeLeviSL J c hc hJ A)) =
      project J (planeLeviSL J c hc hJ A) := by
  rw [Descent.unitaryConj_project]
  congr 1
  apply Subtype.ext
  rw [Descent.specialUnitaryConj_val]
  have hh := (scalarDiagonal_levi J k A).map (MulAut.conj (planeBasisGL c)).toMonoidHom
  apply mul_inv_eq_iff_eq_mul.mpr
  exact hh
end Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
