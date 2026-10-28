module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Roots

/-!
# A common unitary diagonal representative on opposite roots

The matrix `diag(t,1,conj(t)⁻¹)` is genuinely unitary. Its composition with a
field automorphism acts on upper coordinates by `(t σ(a), t conj(t) σ(b))`,
and on opposite coordinates with scale `conj(t)⁻¹`. The same unitary matrix
therefore realizes both formulas in the actual projective group.

These are the concrete diagonal normalizations in Steinberg, Theorem 36,
step (4), `refs/KGroup/GLS3/Chapter2St1.tex`, with the actual unitary
representatives required by GLS3, `chapter2.tex`, §2.7. They do not assert
that an arbitrary automorphism has this form.
-/

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private theorem field_conj_commute [Finite E] (σ : E ≃+* E) (a : E) :
    J.conj (σ a) = σ (J.conj a) := by
  let := finiteFieldAut_isCyclic (E := E)
  let := IsCyclic.commGroup (α := E ≃+* E)
  exact congrArg (fun f : E ≃+* E => f a) (Commute.all J.conj σ).eq

private def scaledFieldCoordHom [Finite E] (σ : E ≃+* E) (t : Eˣ) :
    hermitianUnipotentCoord J →* hermitianUnipotentCoord J where
  toFun z := ⟨((t : E) * σ z.val.1, (t : E) * J.conj (t : E) * σ z.val.2), by
    dsimp only
    rw [map_mul, map_mul, map_mul, J.conj_involutive,
      field_conj_commute, field_conj_commute]
    have he := congrArg σ z.property
    simp only [map_add, map_mul, map_zero] at he
    linear_combination (t : E) * J.conj (t : E) * he⟩
  map_one' := by
    apply Subtype.ext
    change ((t : E) * σ 0, (t : E) * J.conj (t : E) * σ 0) = (0, 0)
    simp
  map_mul' z w := by
    apply Subtype.ext
    apply Prod.ext
    · change (t : E) * σ (z.val.1 + w.val.1) =
        (t : E) * σ z.val.1 + (t : E) * σ w.val.1
      rw [map_add, mul_add]
    · change (t : E) * J.conj (t : E) * σ (z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1) =
        (t : E) * J.conj (t : E) * σ z.val.2 + (t : E) * J.conj (t : E) * σ w.val.2 -
          ((t : E) * σ z.val.1) * J.conj ((t : E) * σ w.val.1)
      rw [map_sub, map_add, map_mul, map_mul, field_conj_commute]
      ring

private theorem scaledFieldCoordHom_injective [Finite E] (σ : E ≃+* E) (t : Eˣ) :
    Function.Injective (scaledFieldCoordHom J σ t) := by
  intro z w h
  apply Subtype.ext
  apply Prod.ext
  · apply σ.injective
    exact mul_left_cancel₀ (Units.ne_zero t) (congrArg (fun x : hermitianUnipotentCoord J => x.val.1) h)
  · apply σ.injective
    exact mul_left_cancel₀ (mul_ne_zero (Units.ne_zero t) ((map_ne_zero J.conj).mpr (Units.ne_zero t)))
      (congrArg (fun x : hermitianUnipotentCoord J => x.val.2) h)

public noncomputable def scaledFieldCoordAut [Finite E] (σ : E ≃+* E) (t : Eˣ) :
    MulAut (hermitianUnipotentCoord J) :=
  MulEquiv.ofBijective (scaledFieldCoordHom J σ t)
    ⟨scaledFieldCoordHom_injective J σ t,
      Finite.surjective_of_injective (scaledFieldCoordHom_injective J σ t)⟩

public theorem scaledFieldCoordAut_fst [Finite E] (σ : E ≃+* E) (t : Eˣ)
    (z : hermitianUnipotentCoord J) :
    (scaledFieldCoordAut J σ t z).val.1 = (t : E) * σ z.val.1 := by
  dsimp [scaledFieldCoordAut, scaledFieldCoordHom]
  rfl

public theorem scaledFieldCoordAut_snd [Finite E] (σ : E ≃+* E) (t : Eˣ)
    (z : hermitianUnipotentCoord J) :
    (scaledFieldCoordAut J σ t z).val.2 = (t : E) * J.conj (t : E) * σ z.val.2 := by
  dsimp [scaledFieldCoordAut, scaledFieldCoordHom]
  rfl

public theorem scaledFieldCoordAut_neg_equivariant [Finite E] (σ : E ≃+* E) (t : Eˣ)
    (z : hermitianUnipotentCoord J) :
    scaledFieldCoordAut J σ t (hermitianTorusAction J (-1) z) =
      hermitianTorusAction J (-1) (scaledFieldCoordAut J σ t z) := by
  apply Subtype.ext
  apply Prod.ext
  · simp [scaledFieldCoordAut_fst, hermitianTorusAction_fst]
  · simp [scaledFieldCoordAut_snd, hermitianTorusAction_snd]

private def diagonalGL (t : Eˣ) : GL (Fin 3) E :=
  GeneralLinearGroup.mkOfDetNeZero !![(t : E),0,0; 0,1,0; 0,0,(J.conj (t : E))⁻¹] (by
    simp [Matrix.det_fin_three, Units.ne_zero t])

public def diagonalUnitary (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (t : Eˣ) :
    J.unitarySubgroup :=
  ⟨diagonalGL J t, by
    rw [J.mem_unitarySubgroup_iff, hJ]
    change J.conjTranspose !![(t : E),0,0; 0,1,0; 0,0,(J.conj (t : E))⁻¹] *
      !![0,0,1;0,1,0;1,0,0] * !![(t : E),0,0; 0,1,0; 0,0,(J.conj (t : E))⁻¹] = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
        Units.ne_zero t]
    rw [J.conj_involutive]
    simp⟩

public theorem diagonalUnitary_val (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (t : Eˣ) :
    (diagonalUnitary J hJ t).val.val = !![(t : E),0,0; 0,1,0; 0,0,(J.conj (t : E))⁻¹] := by
  dsimp [diagonalUnitary, diagonalGL]
  rfl

public theorem scaledFieldCoordAut_root [Finite E] (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (σ : E ≃+* E) (t : Eˣ) (z : hermitianUnipotentCoord J) :
    (root J hJ (scaledFieldCoordAut J σ t z)).val =
      ProjGenLinGroup.mk (diagonalUnitary J hJ t).val *
        ProjGenLinGroup.map σ.toRingHom (root J hJ z).val *
        (ProjGenLinGroup.mk (diagonalUnitary J hJ t).val)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  simp only [hermitianUnipotentPSU_val, ProjGenLinGroup.map_mk, ← map_mul]
  congr 1
  apply GeneralLinearGroup.ext
  intro i j
  change (hermitianUnipotentMatrix J (scaledFieldCoordAut J σ t z) *
      (diagonalUnitary J hJ t).val.val) i j =
    ((diagonalUnitary J hJ t).val.val * (hermitianUnipotentMatrix J z).map σ) i j
  rw [diagonalUnitary_val]
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      scaledFieldCoordAut_fst, scaledFieldCoordAut_snd, field_conj_commute]
  all_goals field_simp

private theorem weyl_inv : (hermitianWeylGL : GL (Fin 3) E)⁻¹ = hermitianWeylGL := by
  apply inv_eq_of_mul_eq_one_left
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

private def oppositeGL (z : hermitianUnipotentCoord J) : GL (Fin 3) E :=
  hermitianWeylGL * hermitianUnipotentGL J z * hermitianWeylGL

private theorem oppositeGL_val (z : hermitianUnipotentCoord J) :
    (oppositeGL J z).val = !![1,0,0; J.conj z.val.1,1,0; z.val.2,-z.val.1,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oppositeGL, hermitianWeylGL, hermitianWeylMatrix, hermitianUnipotentGL,
      hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem oppositeRoot_val (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (z : hermitianUnipotentCoord J) :
    (oppositeRoot J hJ z).val = ProjGenLinGroup.mk (oppositeGL J z) := by
  simp only [oppositeRoot_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    hermitianUnipotentPSU_val, hermitianWeylPSU_val, ← map_inv, ← map_mul, weyl_inv]
  rfl

public theorem scaledFieldCoordAut_opposite [Finite E] (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (σ : E ≃+* E) (t : Eˣ) (z : hermitianUnipotentCoord J) :
    (oppositeRoot J hJ (scaledFieldCoordAut J σ (Units.map J.conj.toMonoidHom t)⁻¹ z)).val =
      ProjGenLinGroup.mk (diagonalUnitary J hJ t).val *
        ProjGenLinGroup.map σ.toRingHom (oppositeRoot J hJ z).val *
        (ProjGenLinGroup.mk (diagonalUnitary J hJ t).val)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  simp only [oppositeRoot_val, ProjGenLinGroup.map_mk, ← map_mul]
  congr 1
  apply GeneralLinearGroup.ext
  intro i j
  change ((oppositeGL J (scaledFieldCoordAut J σ (Units.map J.conj.toMonoidHom t)⁻¹ z)).val *
      (diagonalUnitary J hJ t).val.val) i j =
    ((diagonalUnitary J hJ t).val.val * (oppositeGL J z).val.map σ) i j
  rw [diagonalUnitary_val, oppositeGL_val, oppositeGL_val]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, scaledFieldCoordAut_fst,
      scaledFieldCoordAut_snd, field_conj_commute]
  all_goals try rw [J.conj_involutive]
  all_goals field_simp

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
