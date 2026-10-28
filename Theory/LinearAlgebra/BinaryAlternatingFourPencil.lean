module
public import Theory.LinearAlgebra.BinaryAlternatingFour
/-!
# Binary alternating pencils in dimension four

If C is a nondegenerate alternating binary four-form and C composed with
an invertible operator t is alternating, then t satisfies t² = 1 or
 t² + t + 1 = 0. Normalize C to the standard symplectic matrix. The six
entries of the second alternating form give a direct quadratic identity;
invertibility forces its constant coefficient to be one. Conjugation
transports the relation back to the original operator.

This structural calculation avoids enumerating pairs of matrices. It is the
linear-algebra step behind the eight-dimensional orthogonal pair in
Aschbacher--Smith F.9.5(6.ii), pp.319--320, and 12.6.26, p.831.
-/

public section
open Matrix
namespace BinaryAlternatingFour
private def paired (a b c d e f : ZMod 2) : Mat :=
  !![a,0,d,e; 0,a,b,c; c,e,f,0; b,d,0,f]

private theorem paired_eq (a b c d e f : ZMod 2) :
    paired a b c d e f = J4 * alternating a b c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [paired,J4,alternating,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem paired_quadratic (a b c d e f : ZMod 2) :
    (paired a b c d e f)^2 = (a+f) • paired a b c d e f + (a*f+b*e+c*d) • (1:Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [paired,pow_two,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring_nf <;> simp [show (2:ZMod 2)=0 by decide]

private theorem pair_certificate (a b c d e f : ZMod 2)
    (hn : (paired a b c d e f).det ≠ 0) :
    (paired a b c d e f)^2 = 1 ∨
      (paired a b c d e f)^2 + paired a b c d e f + 1 = 0 := by
  let N := paired a b c d e f
  have hq := paired_quadratic a b c d e f
  have hp : a*f+b*e+c*d ≠ 0 := by
    intro hz
    rw [hz,zero_smul,add_zero] at hq
    have hi := Matrix.nonsing_inv_mul N (isUnit_iff_ne_zero.mpr hn)
    have hh := congrArg (fun X : Mat => N⁻¹*X) hq
    change N⁻¹*N^2 = N⁻¹*((a+f) • N) at hh
    rw [pow_two,←mul_assoc,hi,one_mul,Matrix.mul_smul,hi] at hh
    have ha := congrArg (fun X : Mat => X 0 0) hh
    have hf := congrArg (fun X : Mat => X 2 2) hh
    have haa : a=a+f := by simpa [N,paired] using ha
    have hff : f=a+f := by simpa [N,paired] using hf
    have ha0 : a=0 := add_eq_right.mp hff.symm
    have hf0 : f=0 := add_eq_left.mp haa.symm
    rw [ha0,hf0,add_zero,zero_smul] at hh
    exact hn ((congrArg Matrix.det hh).trans Matrix.det_zero)
  have hp1 : a*f+b*e+c*d=1 := (by decide : ∀ x : ZMod 2, x≠0 → x=1) _ hp
  rw [hp1,one_smul] at hq
  rcases (by decide : ∀ x : ZMod 2, x=0 ∨ x=1) (a+f) with h | h
  · left
    simpa [h] using hq
  · right
    rw [h,one_smul] at hq
    rw [hq]
    ext i j
    simp only [Matrix.add_apply]
    ring_nf
    simp [show (2:ZMod 2)=0 by decide]

private theorem j_square : J4 * J4 = 1 := by decide

private theorem standard_pencil (M : Mat) (hM : M.det ≠ 0)
    (ha : (J4*M).toBilin'.IsAlt) : M^2=1 ∨ M^2+M+1=0 := by
  have hd (i) : (J4*M) i i = 0 := by
    simpa only [Matrix.toBilin'_single] using ha.self_eq_zero (Pi.single i 1)
  have hs : J4*M = (J4*M).transpose := by
    ext i j
    simpa only [Matrix.toBilin'_single, ZMod.neg_eq_self_mod_two, Matrix.transpose_apply]
      using ha.neg_eq (Pi.single i 1) (Pi.single j 1)
  have he := matrix_eq_alternating (J4*M) hd hs
  have hm : M = J4 * alternating ((J4*M) 0 1) ((J4*M) 0 2) ((J4*M) 0 3)
      ((J4*M) 1 2) ((J4*M) 1 3) ((J4*M) 2 3) := by
    rw [← he, ← mul_assoc, j_square, one_mul]
  have hm' : M = paired ((J4*M) 0 1) ((J4*M) 0 2) ((J4*M) 0 3)
      ((J4*M) 1 2) ((J4*M) 1 3) ((J4*M) 2 3) := hm.trans (paired_eq _ _ _ _ _ _).symm
  rw [hm'] at hM ⊢
  exact pair_certificate _ _ _ _ _ _ hM

theorem alternating_pencil_relation (F M : Mat)
    (hF : F.toBilin'.IsAlt) (hFn : F.toBilin'.Nondegenerate)
    (hM : M.det ≠ 0) (hFM : (F*M).toBilin'.IsAlt) :
    M^2=1 ∨ M^2+M+1=0 := by
  obtain ⟨P,hP,hPF⟩ := exists_congruence F hF hFn
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hleft := Matrix.nonsing_inv_mul P hu
  have hright := Matrix.mul_nonsing_inv P hu
  let N := P⁻¹*M*P
  have hJN : J4*N = P.transpose*(F*M)*P := by
    rw [←hPF]
    dsimp [N]
    simp only [mul_assoc, ←mul_assoc P P⁻¹, hright, one_mul]
  have hback : P*N*P⁻¹=M := by
    dsimp [N]
    simp only [mul_assoc, ←mul_assoc P P⁻¹, hright, one_mul, mul_one]
  have hN : N.det ≠ 0 := by
    intro hz
    have he := congrArg Matrix.det hback
    rw [det_mul,det_mul,hz,mul_zero,zero_mul] at he
    exact hM he.symm
  have ha : (J4*N).toBilin'.IsAlt := by
    rw [hJN]
    have he : P.transpose*(F*M)*P = ((F*M).toBilin'.comp P.toLin' P.toLin').toMatrix' := by
      rw [LinearMap.BilinForm.toMatrix'_comp,LinearMap.BilinForm.toMatrix'_toBilin',LinearMap.toMatrix'_toLin']
    rw [he,Matrix.toBilin'_toMatrix']
    intro x
    exact hFM (P.toLin' x)
  rcases standard_pencil N hN ha with h | h
  · left
    have he := conjugate_pow P⁻¹ P N hright hleft 2
    rw [hback,h,mul_one,hright] at he
    exact he
  · right
    have hh := congrArg (fun X : Mat => P*X*P⁻¹) h
    have he : P*(N^2+N+1)*P⁻¹ = M^2+M+1 := by
      simp only [pow_two, mul_add, add_mul, mul_one]
      have hh : P*(N*N)*P⁻¹ = M*M := by
        rw [←hback]
        simp only [mul_assoc, ←mul_assoc P⁻¹ P, hleft, one_mul]
      rw [hh,hback,hright]
    simpa only [he,mul_zero,zero_mul] using hh
end BinaryAlternatingFour
