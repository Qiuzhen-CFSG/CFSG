module

public import Theory.SpecificGroups.SU3.OrthogonalFixed
public import Theory.SpecificGroups.SL3.InvolutionEigenbasis
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Commuting partners for entrywise fixed unitary involutions

In characteristic different from two, a nontrivial determinant-one ternary
involution has a two-dimensional negative eigenspace and a one-dimensional
positive eigenspace. Its symmetric Gram matrix is block diagonal in a linear
eigenbasis. A reflection of the binary block, together with negation on the
positive line, gives a distinct commuting determinant-one involution. The
binary reflection is constructed explicitly, including the hyperbolic case
where both diagonal entries vanish.

The fixed-group equivalence in `OrthogonalFixed` transports this construction
to the original projective special unitary group. Thus entrywise fixation is
preserved without requiring a unitary conjugator to preserve that condition.
No finiteness or simplicity assumption is needed.

This supplies the fixed-involution step used in Aschbacher--Smith E.1.14(7),
printed p.214; compare the involution geometry in A.3.21(a)--(b), printed p.55,
and Aschbacher (1982), Lemma 4.11. It does not assert the full source theorem.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
variable {K : Type*} [Field K]

private theorem block_reflection (a b c d : K) :
    ∃ Q : Matrix (Fin 3) (Fin 3) K,
      Q * Q = 1 ∧ Q.det = 1 ∧ Q 2 2 = -1 ∧
      Q * (Matrix.SL3.standardInvolution K).val =
        (Matrix.SL3.standardInvolution K).val * Q ∧
      Q.transpose * !![a,b,0;b,c,0;0,0,d] * Q = !![a,b,0;b,c,0;0,0,d] := by
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · refine ⟨!![0,1,0;1,0,0;0,0,-1], ?_, ?_, rfl, ?_, ?_⟩
      · ext i j; fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three]
      · simp [Matrix.det_fin_three]
      · ext i j; fin_cases i <;> fin_cases j <;>
          simp [Matrix.SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]
      · subst a; subst c
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three]
    · refine ⟨!![1,0,0; -(2*b/c),-1,0;0,0,-1], ?_, ?_, rfl, ?_, ?_⟩
      · ext i j; fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three]
      · simp [Matrix.det_fin_three]
      · ext i j; fin_cases i <;> fin_cases j <;>
          simp [Matrix.SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]
      · subst a
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring
  · refine ⟨!![-1,-(2*b/a),0;0,1,0;0,0,-1], ?_, ?_, rfl, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

private theorem gram_block (h2 : (2 : K) ≠ 0)
    (A P : GL (Fin 3) K) (J : Matrix (Fin 3) (Fin 3) K)
    (hJs : J.transpose = J) (hA : A.val.transpose * J * A.val = J)
    (hP : P.val * (Matrix.SL3.standardInvolution K).val * (P⁻¹).val = A.val) :
    let G := P.val.transpose * J * P.val
    G = !![G 0 0,G 0 1,0;G 0 1,G 1 1,0;0,0,G 2 2] := by
  let D := (Matrix.SL3.standardInvolution K).val
  let G := P.val.transpose * J * P.val
  have hAP : A.val * P.val = P.val * D := by
    rw [← hP]
    simp [D, mul_assoc]
  have hGs : G.transpose = G := by
    simp only [G, Matrix.transpose_mul, Matrix.transpose_transpose, hJs, mul_assoc]
  have hDG : D.transpose * G * D = G := by
    calc
      _ = (P.val * D).transpose * J * (P.val * D) := by
        simp only [G, Matrix.transpose_mul, mul_assoc]
      _ = (A.val * P.val).transpose * J * (A.val * P.val) := by rw [hAP]
      _ = P.val.transpose * (A.val.transpose * J * A.val) * P.val := by
        simp only [Matrix.transpose_mul, mul_assoc]
      _ = G := by rw [hA]
  have hz (x : K) (hx : -x = x) : x = 0 := by
    apply (mul_eq_zero.mp (show (2 : K) * x = 0 by linear_combination -hx)).resolve_left h2
  have h02 : G 0 2 = 0 := by
    apply hz
    simpa [D, Matrix.SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]
      using congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hDG
  have h12 : G 1 2 = 0 := by
    apply hz
    simpa [D, Matrix.SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]
      using congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 2) hDG
  have hs (i j : Fin 3) : G j i = G i j :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i j) hGs
  change G = !![G 0 0,G 0 1,0;G 0 1,G 1 1,0;0,0,G 2 2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h02, h12, hs 0 1, hs 0 2, hs 1 2]

/-- Every involution in the literal split ternary special orthogonal group
extends to a distinct commuting involution in that same group. -/
public theorem orthogonal_involution_extension (h2 : (2 : K) ≠ 0)
    (w : (splitOrthogonalForm K).specialSubgroup) (hw : orderOf w = 2) :
    ∃ v : (splitOrthogonalForm K).specialSubgroup,
      orderOf v = 2 ∧ v ≠ w ∧ Commute w v := by
  let J := splitOrthogonalForm K
  have hwsq : w.val.val * w.val.val = 1 := by
    have he : w ^ 2 = 1 := hw ▸ pow_orderOf_eq_one w
    simpa only [pow_two, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one,
      Units.val_one] using congrArg (fun x : J.specialSubgroup => x.val.val) he
  have hwne : w.val.val ≠ 1 := by
    intro he
    have : w = 1 := Subtype.ext (Units.ext he)
    simp [this] at hw
  have hwd : w.val.val.det = 1 :=
    congrArg Units.val ((J.mem_specialSubgroup_iff _).mp w.property).2
  obtain ⟨P, hP⟩ := Matrix.SL3.exists_involution_conjugator h2 w.val.val hwsq hwne hwd
  let G := P.val.transpose * J.form * P.val
  have hG := gram_block h2 w.val P J.form (by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl)
    ((J.mem_specialSubgroup_iff _).mp w.property).1 hP
  change G = _ at hG
  obtain ⟨Q, hQsq, hQd, hQ22, hQc, hQg⟩ :=
    block_reflection (G 0 0) (G 0 1) (G 1 1) (G 2 2)
  rw [← hG] at hQg
  let R : GL (Fin 3) K := ⟨Q, Q, hQsq, hQsq⟩
  let V : GL (Fin 3) K := P * R * P⁻¹
  have hVo : V.val.transpose * J.form * V.val = J.form := by
    change (P.val * Q * (P⁻¹).val).transpose * J.form *
      (P.val * Q * (P⁻¹).val) = J.form
    calc
      _ = (P⁻¹).val.transpose * (Q.transpose * G * Q) * (P⁻¹).val := by
        simp only [G, Matrix.transpose_mul, mul_assoc]
      _ = (P⁻¹).val.transpose * G * (P⁻¹).val := by rw [hQg]
      _ = (P.val * (P⁻¹).val).transpose * J.form *
          (P.val * (P⁻¹).val) := by
        simp only [G, Matrix.transpose_mul, mul_assoc]
      _ = J.form := by simp
  have hVd : V.val.det = 1 := by
    change (P.val * Q * (P⁻¹).val).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, hQd, mul_one, ← Matrix.det_mul]
    simp
  let v : J.specialSubgroup := ⟨V, (J.mem_specialSubgroup_iff _).mpr ⟨hVo, Units.ext hVd⟩⟩
  have hRsq : R * R = 1 := Units.ext hQsq
  have hVsq : v ^ 2 = 1 := by
    apply Subtype.ext
    change (P * R * P⁻¹) ^ 2 = 1
    calc
      _ = P * (R * R) * P⁻¹ := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hRsq]; simp
  have hneg : (-1 : K) ≠ 1 := by
    intro he
    apply h2
    linear_combination -he
  have hVne : v ≠ 1 := by
    intro he
    have he' : P * R * P⁻¹ = 1 := congrArg Subtype.val he
    have hR : R = 1 := by
      have := congrArg (fun X : GL (Fin 3) K => P⁻¹ * X * P) he'
      simpa [mul_assoc] using this
    have hh : Q 2 2 = 1 := congrArg (fun X : GL (Fin 3) K => X.val 2 2) hR
    exact hneg (hQ22.symm.trans hh)
  refine ⟨v, orderOf_eq_prime hVsq hVne, ?_, ?_⟩
  · intro he
    have he' : P.val * Q * (P⁻¹).val = w.val.val :=
      congrArg (fun x : J.specialSubgroup => x.val.val) he
    rw [← hP] at he'
    have hQ : Q = (Matrix.SL3.standardInvolution K).val := by
      have := congrArg (fun X : Matrix (Fin 3) (Fin 3) K =>
        (P⁻¹).val * X * P.val) he'
      simpa [mul_assoc] using this
    have hh : Q 2 2 = 1 := congrArg (fun X : Matrix (Fin 3) (Fin 3) K => X 2 2) hQ
    exact hneg (hQ22.symm.trans hh)
  · apply Subtype.ext
    apply Units.ext
    change w.val.val * (P.val * Q * (P⁻¹).val) =
      (P.val * Q * (P⁻¹).val) * w.val.val
    rw [← hP]
    simpa [mul_assoc] using
      congrArg (fun X : Matrix (Fin 3) (Fin 3) K => P.val * X * (P⁻¹).val) hQc.symm

/-- Transport the orthogonal reflection through the actual entrywise-fixed
subgroup equivalence. The resulting partner lies in the original projective
special unitary group and is fixed by the specified entrywise automorphism. -/
public theorem projective_fixed_involution_extension {F : Type*} [Field F]
    (J : HermitianForm 3 F) (h2 : (2 : F) ≠ 0)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hγ : J.IsEntrywiseConjugation γ)
    (w : ProjectiveSpecialUnitaryMatrixGroup J) (hw : orderOf w = 2)
    (hfix : γ w = w) :
    ∃ v : ProjectiveSpecialUnitaryMatrixGroup J,
      orderOf v = 2 ∧ v ≠ w ∧ γ v = v ∧ Commute w v := by
  let K := FixedBy.subfield F J.conj
  have hK2 : (2 : K) ≠ 0 := by
    intro he
    apply h2
    exact_mod_cast congrArg K.subtype he
  let e := projectiveFixedEquivOrthogonal J hJ hγ
  let w' : γ.fixedSubgroup := ⟨w, (MulAut.mem_fixedSubgroup _ _).mpr hfix⟩
  have hw' : orderOf (e w') = 2 := by
    rw [e.orderOf_eq]
    simpa only [← Subgroup.orderOf_coe] using hw
  obtain ⟨v, hv, hne, hc⟩ := orthogonal_involution_extension hK2 (e w') hw'
  let v' : γ.fixedSubgroup := e.symm v
  refine ⟨v'.val, ?_, ?_, (MulAut.mem_fixedSubgroup _ _).mp v'.property, ?_⟩
  · rw [Subgroup.orderOf_coe, e.symm.orderOf_eq]
    exact hv
  · intro he
    apply hne
    have he' : v' = w' := Subtype.ext he
    have := congrArg e he'
    simpa only [v', MulEquiv.apply_symm_apply] using this
  · have he : Commute w' v' := by
      apply e.injective
      simpa only [map_mul, v', MulEquiv.apply_symm_apply] using hc.eq
    exact he.map γ.fixedSubgroup.subtype


end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
