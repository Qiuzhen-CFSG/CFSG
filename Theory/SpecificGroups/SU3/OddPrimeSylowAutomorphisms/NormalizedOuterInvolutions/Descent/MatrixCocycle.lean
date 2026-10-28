module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.SemilinearReduction
import BenderSuzuki.External.Huppert.II.theorem_10_12
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Exact cocycles for involutory odd-prime unitary twists

The square of unitary conjugation followed by entrywise conjugation centralizes
PSU₃ projectively. Three explicit root matrices show that this projective
centralizer consists of scalars. Projective commutation lifts to matrix
commutation using trace three, except when three vanishes: there the scalar
has cube one by determinants, and `(c - 1)³ = 0` forces it to be one.

The resulting scalar matrix norm is fixed by conjugation. Unitarity gives its
scalar square one, and the determinant of the original unitary matrix gives
its cube one. Thus the norm equals one, including fixed-field order three.

The root calculation adapts `ProjectiveOuterInvolutions.Descent.ScalarKernel`;
the square calculation adapts its `Reduction` sibling without importing the
conflicting entrywise-action declaration. Source: GLS3, §2.7 and the A₂ graph
involution analysis of §4.3; Aschbacher–Smith F.6.18(10)–(11), pp.309–310.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent
variable {E : Type*} [Field E]

private theorem commute_of_projective_commute_trace_three
    (A X : GL (Fin 3) E) (hX : X.val.trace = 3)
    (h : Commute (ProjGenLinGroup.mk A) (ProjGenLinGroup.mk X)) : Commute A X := by
  have hp : ProjGenLinGroup.mk (A * X * A⁻¹) = ProjGenLinGroup.mk X := by
    simpa only [map_mul, map_inv] using (mul_inv_eq_iff_eq_mul).mpr h.eq
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have hm : ((A * X * A⁻¹) * GeneralLinearGroup.scalar (Fin 3) c).val =
      (c : E) • (A.val * X.val * (A⁻¹).val) := by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  have ht := congrArg (fun B : GL (Fin 3) E => B.val.trace) hc
  rw [hm, trace_smul, trace_units_conj, hX] at ht
  have hc1 : c = 1 := by
    apply Units.ext
    by_cases h3 : (3 : E) = 0
    · have hd := congrArg (fun B : GL (Fin 3) E => B.val.det) hc
      rw [hm, det_smul, det_units_conj] at hd
      have hc3 : (c : E)^3 = 1 := by
        apply mul_right_cancel₀ X.det_ne_zero
        simpa using hd
      have hnil : ((c : E) - 1)^3 = 0 := by
        linear_combination hc3 - ((c : E)^2 - c) * h3
      exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hnil)
    · exact mul_right_cancel₀ h3 (ht.trans (one_mul _).symm)
  rw [hc1, map_one, mul_one] at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc : A * X = X * A)


variable (J : HermitianForm 3 E)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private def upperRoot (c : E) (hc : c + J.conj c = 0) : J.specialSubgroup :=
  BenderSuzuki.External.hermitianUnipotentSU J hJ ⟨(0, c), by simpa using hc⟩

private def lowerRoot (c : E) (hc : c + J.conj c = 0) : J.specialSubgroup := by
  let L : Matrix (Fin 3) (Fin 3) E := !![1, 0, 0; 0, 1, 0; c, 0, 1]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero L (by simp [L, det_fin_three]), ?_⟩
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hc, add_comm]
  · apply Units.ext
    change L.det = 1
    simp [L, det_fin_three]

include hJ in
/-- The centralizer in PGL of the actual standard PSU₃ image is trivial.
The determinant argument in characteristic three avoids dividing by trace three. -/
public theorem projective_centralizer_scalar (h2 : (2 : E) ≠ 0)
    (hconj : ∃ t : E, J.conj t ≠ t)
    (A : GL (Fin 3) E)
    (hA : ∀ b : ProjectiveSpecialUnitaryMatrixGroup J,
      Commute (ProjGenLinGroup.mk A) b.val) :
    A ∈ Subgroup.center (GL (Fin 3) E) := by
  obtain ⟨t, ht⟩ := hconj
  let c := t - J.conj t
  have hc0 : c ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hc : c + J.conj c = 0 := by
    simp only [c, map_sub, J.conj_involutive t]
    ring
  let b : E := -(2 : E)⁻¹
  have hb : b + J.conj b + 1 = 0 := by
    simp only [b, map_neg, map_inv₀, map_ofNat]
    field_simp
    ring
  let R := BenderSuzuki.External.hermitianUnipotentSU J hJ ⟨(1, b), by simpa using hb⟩
  have hcomm (X : J.specialSubgroup) (htr : X.val.val.trace = 3) :
      A.val * X.val.val = X.val.val * A.val :=
    congrArg Units.val
      (commute_of_projective_commute_trace_three A X.val htr
        (by simpa only [specialToProjective_apply_val] using hA (J.specialToProjective X))).eq
  have hU := hcomm (upperRoot J hJ c hc) (by
    simp [upperRoot, BenderSuzuki.External.hermitianUnipotentSU,
      BenderSuzuki.External.hermitianUnipotentGL, BenderSuzuki.External.hermitianUnipotentMatrix,
      Matrix.trace, Fin.sum_univ_three]; ring)
  have hL := hcomm (lowerRoot J hJ c hc) (by
    simp [lowerRoot, Matrix.trace, Fin.sum_univ_three]; ring)
  have hR := hcomm R (by
    simp [R, BenderSuzuki.External.hermitianUnipotentSU,
      BenderSuzuki.External.hermitianUnipotentGL, BenderSuzuki.External.hermitianUnipotentMatrix,
      Matrix.trace, Fin.sum_univ_three]; ring)
  have hUmat : (upperRoot J hJ c hc).val.val = !![1, 0, c; 0, 1, 0; 0, 0, 1] := by
    simp [upperRoot, BenderSuzuki.External.hermitianUnipotentSU,
      BenderSuzuki.External.hermitianUnipotentGL, BenderSuzuki.External.hermitianUnipotentMatrix]
  rw [hUmat] at hU
  change A.val * !![1, 0, 0; 0, 1, 0; c, 0, 1] =
    !![1, 0, 0; 0, 1, 0; c, 0, 1] * A.val at hL
  have hRmat : R.val.val = !![1, 1, b; 0, 1, -1; 0, 0, 1] := by
    simp [R, BenderSuzuki.External.hermitianUnipotentSU,
      BenderSuzuki.External.hermitianUnipotentGL, BenderSuzuki.External.hermitianUnipotentMatrix]
  rw [hRmat] at hR
  have h20 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 0) hU
  have h21 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) hU
  have hdiag := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) hU
  have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 2) hU
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 2) hL
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 1) hL
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 0) hL
  have hmid := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) hR
  simp [Matrix.mul_apply, Fin.sum_univ_three, hc0, mul_comm, mul_eq_zero] at h20 h21 hdiag h10 h02 h01 h12 hmid
  apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  refine ⟨A.val 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  all_goals grind

/-- The square-one twist hypothesis makes the projective matrix norm centralize PSU₃. -/
public theorem projective_norm_commutes_of_twist_sq
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u : J.unitarySubgroup)
    (hu : (J.unitaryConj u * γ)^2 = 1)
    (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    Commute (Matrix.ProjGenLinGroup.mk
      (u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val)) b.val := by
  have hγγ : γ (γ b) = b := DFunLike.congr_fun hγ.sq_eq_one b
  have h := congrArg (fun a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => (a b).val) hu
  change (J.unitaryConj u (γ (J.unitaryConj u (γ b)))).val = b.val at h
  rw [unitaryConj_apply_val, IsEntrywiseConjugation.apply_val J hγ,
    unitaryConj_apply_val, map_mul, map_mul, map_inv] at h
  rw [← IsEntrywiseConjugation.apply_val J hγ, hγγ, Matrix.ProjGenLinGroup.map_mk] at h
  change _ * _ = _ * _
  apply (mul_inv_eq_iff_eq_mul).mp
  simpa [map_mul, mul_assoc] using h

private theorem map_conj_map_conj (A : GL (Fin 3) E) :
    Matrix.GeneralLinearGroup.map J.conj.toRingHom
      (Matrix.GeneralLinearGroup.map J.conj.toRingHom A) = A := by
  apply Units.ext
  ext i j
  exact J.conj_involutive _

private theorem map_conj_mem_unitary (hJ : J.form.map J.conj = J.form)
    (u : J.unitarySubgroup) :
    Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val ∈ J.unitarySubgroup := by
  rw [mem_unitarySubgroup_iff]
  change J.conjTranspose (u.val.val.map J.conj) * J.form *
    (u.val.val.map J.conj) = J.form
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A.map J.conj)
    ((J.mem_unitarySubgroup_iff u.val).mp u.property)
  have ha : (J.conjTranspose u.val.val).map J.conj =
      J.conjTranspose (u.val.val.map J.conj) := by
    ext i j
    rfl
  simpa only [RingEquiv.mapMatrix_apply, Matrix.map_mul,
    ha, hJ] using h


/-- In dimension three a projectively trivial unitary matrix norm equals one,
in every characteristic: its scalar has square one and cube one. -/
public theorem norm_eq_one_of_projective_norm_eq_one
    (hJ : J.form.map J.conj = J.form) (u : J.unitarySubgroup)
    (hu : Matrix.ProjGenLinGroup.mk
      (u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val) = 1) :
    u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val = 1 := by
  let N := u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val
  have hN : N ∈ Subgroup.center (GL (Fin 3) E) :=
    Matrix.ProjGenLinGroup.mk_eq_one.mp hu
  have hNfix : Matrix.GeneralLinearGroup.map J.conj.toRingHom N = N := by
    apply mul_left_cancel (a := u.val)
    have hc := Subgroup.mem_center_iff.mp hN u.val
    simpa only [N, map_mul, map_conj_map_conj, mul_assoc] using hc.symm
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hN
  have hcfix : J.conj c = c := by
    have h := congrArg (fun A : GL (Fin 3) E => A.val 0 0) hNfix
    change J.conj (N.val 0 0) = N.val 0 0 at h
    simpa [← hc, Matrix.scalar_apply] using h
  have hNu : N ∈ J.unitarySubgroup :=
    J.unitarySubgroup.mul_mem u.property (map_conj_mem_unitary J hJ u)
  have hunitary := (J.mem_unitarySubgroup_iff N).mp hNu
  have hadj : J.conjTranspose (Matrix.scalar (Fin 3) c) = Matrix.scalar (Fin 3) c := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hcfix]
    · simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hij, Ne.symm hij]
  rw [← hc, hadj] at hunitary
  obtain ⟨j, hj⟩ : ∃ j, J.form 0 j ≠ 0 := by
    by_contra h
    push Not at h
    exact J.form_nondegenerate (Matrix.det_eq_zero_of_row_eq_zero 0 h)
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 j) hunitary
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hcsq : c * c = 1 := by
    apply mul_right_cancel₀ hj
    calc
      (c * c) * J.form 0 j = c * J.form 0 j * c := by ring
      _ = J.form 0 j := hentry
      _ = 1 * J.form 0 j := (one_mul _).symm

  have hdu := congrArg Matrix.det ((J.mem_unitarySubgroup_iff u.val).mp u.property)
  have hadet : (J.conjTranspose u.val.val).det = J.conj u.val.val.det := by
    change ((u.val.val.map J.conj).transpose).det = _
    rw [Matrix.det_transpose]
    exact (J.conj.map_det _).symm
  rw [Matrix.det_mul, Matrix.det_mul, hadet] at hdu
  have hdetnorm : J.conj u.val.val.det * u.val.val.det = 1 := by
    apply mul_right_cancel₀ J.form_nondegenerate
    calc
      (J.conj u.val.val.det * u.val.val.det) * J.form.det =
          J.conj u.val.val.det * J.form.det * u.val.val.det := by ring
      _ = J.form.det := hdu
      _ = 1 * J.form.det := (one_mul _).symm
  have hdetN : N.val.det = 1 := by
    change (u.val.val * u.val.val.map J.conj).det = 1
    rw [Matrix.det_mul]
    change u.val.val.det * (J.conj.mapMatrix u.val.val).det = 1
    rw [← RingEquiv.map_det]
    simpa only [mul_comm] using hdetnorm
  have hc3 : c ^ 3 = 1 := by
    rw [← hc] at hdetN
    simpa [Matrix.scalar_apply, Matrix.det_fin_three, pow_succ] using hdetN
  have hc1 : c = 1 := by
    calc
      c = (c * c) * c := by rw [hcsq, one_mul]
      _ = c ^ 3 := by ring
      _ = 1 := hc3
  change N = 1
  apply Units.ext
  rw [← hc, hc1]
  simp

include hJ in
private theorem form_fixed : J.form.map J.conj = J.form := by
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

include hJ in
/-- Every involutory unitary twist on the odd-prime standard model is an exact
matrix cocycle. The case of fixed-field order three is included. -/
public theorem unitary_norm_eq_one_of_twist_sq [Finite E]
    {p : ℕ} (hp : p.Prime) (hmod : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u : J.unitarySubgroup)
    (hu : (J.unitaryConj u * γ) ^ 2 = 1) :
    u.val * GeneralLinearGroup.map J.conj.toRingHom u.val = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite E
  let := charP_of_card_eq_prime_pow (by simpa using hcard : Fintype.card E = p ^ 2)
  have h2 : (2 : E) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime E (p := p) (by decide : Nat.Prime 2) (by intro h; have hm := hmod; rw [h] at hm; norm_num at hm)
  have hconj : ∃ t : E, J.conj t ≠ t := by
    by_contra hn
    push Not at hn
    let e : E ≃ {x : E // J.conj x = x} :=
      { toFun := fun x => ⟨x, hn x⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he := Nat.card_congr e
    rw [hcard, hfixed] at he
    have := hp.two_le
    nlinarith
  apply norm_eq_one_of_projective_norm_eq_one J (form_fixed J hJ) u
  apply ProjGenLinGroup.mk_eq_one.mpr
  apply projective_centralizer_scalar J hJ h2 hconj
  exact projective_norm_commutes_of_twist_sq J hγ u hu

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent
