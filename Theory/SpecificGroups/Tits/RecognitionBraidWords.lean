module

public import Theory.SpecificGroups.Tits.RecognitionLocalConjugationRelations

/-!
# The word computations in Parrott's braid argument

The local source equations alone imply the fourth-power conjugation of y and
centralization of dvz by the reflection r(sr)³. Conjugating the latter by s
and imposing (rs)¹⁰ = 1 gives the centralization needed to exclude order ten.

For the displayed equation (*), equation (26) gives sDs = DsD, where D = dvz.
The local conjugation equations show D a D = au, that s centralizes au, and
that r(aD)r = D au. Thus (aD)⁻¹(sDsr)(aD) = sr. Taking fourth powers proves
(*) without even requiring the tenth-power hypothesis. No finiteness or
nontriviality assumption is used.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§6, printed p.684, Verification of VI(i). The exponent in (*) is four;
see `refs/original/n-group-global/parrott-tits-characterization-1972.pdf`.
-/

namespace Tits.ParrottLocalRelations
variable {G : Type*} [Group G] {z t v u w a b c d x y r s : G}
private theorem sqinv {g : G} (hg : g ^ 2 = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hg)
private theorem tail {p q o : G} (hp : p * q = o) (k : G) :
    p * (q * k) = o * k := by rw [← mul_assoc, hp]
private theorem conj_involutive {g : G} (hg : g ^ 2 = 1) :
    Function.Involutive (MulAut.conj g) := by
  intro p
  simp only [MulAut.conj_apply, sqinv hg, mul_assoc, tail (show g*g=1 by simpa [pow_two] using hg), one_mul]
  simp only [show g*g=1 by simpa [pow_two] using hg, mul_one]

variable (h : ParrottLocalRelations z t v u w a b c d x y r s)
include h
private theorem conj_r_z : MulAut.conj r z = z := by
  simp only [MulAut.conj_apply, ← h.comm_zr.eq, mul_assoc, mul_inv_cancel, mul_one]
private theorem conj_r_t : MulAut.conj r t = w*u*v*z := by
  simpa only [MulAut.conj_apply, sqinv h.eq20_r] using h.rtr
private theorem conj_s_t : MulAut.conj s t = z := by
  simpa only [MulAut.conj_apply, sqinv h.s_sq] using h.eq25_ts
private theorem conj_s_y : MulAut.conj s y = w*u*v*z := by
  simpa only [MulAut.conj_apply, sqinv h.s_sq] using h.eq25_ys

/-- Fourth-power conjugation in the verification of VI(i). -/
public theorem braid_fourth_conjugation : (r*s)^4*y*(s*r)^4 = r*y*r := by
  let R := MulAut.conj r
  let S := MulAut.conj s
  have Rt : R t = w*u*v*z := h.conj_r_t
  have Rz : R z = z := h.conj_r_z
  have St : S t = z := h.conj_s_t
  have Sy : S y = w*u*v*z := h.conj_s_y
  have RW : R (w*u*v*z) = t := by rw [← Rt]; exact conj_involutive h.eq20_r t
  have SW : S (w*u*v*z) = y := by rw [← Sy]; exact conj_involutive h.s_sq y
  have Sz : S z = t := by rw [← St]; exact conj_involutive h.s_sq t
  calc
    (r*s)^4*y*(s*r)^4 = R (S (R (S (R (S (R (S y))))))) := by
      simp only [R, S, MulAut.conj_apply, sqinv h.eq20_r, sqinv h.s_sq, pow_succ, pow_zero]
      group
    _ = R y := by rw [Sy, RW, St, Rz, Sz, Rt, SW]
    _ = r*y*r := by simp only [R, MulAut.conj_apply, sqinv h.eq20_r]

private theorem conj_r_A : MulAut.conj r (a*v*z) = d*v*z := by
  have Ra : MulAut.conj r a = d*u := by
    simpa only [MulAut.conj_apply, sqinv h.eq20_r] using h.eq23_ar
  have Rv : MulAut.conj r v = u*v := by
    simpa only [MulAut.conj_apply, sqinv h.eq20_r] using h.eq21_vr
  simp only [map_mul, Ra, Rv, h.conj_r_z, mul_assoc,
    tail (show u*u=1 by simpa [pow_two] using h.u_sq), one_mul]
private theorem conj_r_V : MulAut.conj r (v*z) = u*v*z := by
  have Rv : MulAut.conj r v = u*v := by
    simpa only [MulAut.conj_apply, sqinv h.eq20_r] using h.eq21_vr
  rw [map_mul, Rv, h.conj_r_z]
private theorem conj_s_V : MulAut.conj s (v*z) = v*z := by
  have Sv : MulAut.conj s v = v*t*z := by
    simpa only [MulAut.conj_apply, sqinv h.s_sq] using h.eq25_vs
  have Sz : MulAut.conj s z = t := by
    rw [← h.conj_s_t]; exact conj_involutive h.s_sq t
  rw [map_mul, Sv, Sz]
  simp only [mul_assoc, h.comm_zt.eq, tail (show t*t=1 by simpa [pow_two] using h.t_sq), one_mul]
private theorem conj_s_A : MulAut.conj s (a*v*z) = u*v*z := by
  have Sa : MulAut.conj s a = u := by
    simpa only [MulAut.conj_apply, sqinv h.s_sq] using h.eq25_as
  rw [mul_assoc a, map_mul, Sa, h.conj_s_V, ← mul_assoc]

/-- The intermediate centralizing reflection from Parrott, p.684. -/
public theorem braid_commute_dvz_reflection : Commute (d*v*z) (r*(s*r)^3) := by
  let R := MulAut.conj r
  let S := MulAut.conj s
  have RA : R (a*v*z) = d*v*z := h.conj_r_A
  have RV : R (v*z) = u*v*z := h.conj_r_V
  have SA : S (a*v*z) = u*v*z := h.conj_s_A
  have SV : S (v*z) = v*z := h.conj_s_V
  have RD : R (d*v*z) = a*v*z := by rw [← RA]; exact conj_involutive h.eq20_r _
  have RU : R (u*v*z) = v*z := by rw [← RV]; exact conj_involutive h.eq20_r _
  have SU : S (u*v*z) = a*v*z := by rw [← SA]; exact conj_involutive h.s_sq _
  have hc : (r*(s*r)^3) * (d*v*z) * (r*(s*r)^3)⁻¹ = d*v*z := by
    calc
      _ = R (S (R (S (R (S (R (d*v*z))))))) := by
        simp only [R, S, MulAut.conj_apply, mul_inv_rev, sqinv h.eq20_r,
          sqinv h.s_sq, pow_succ, pow_zero]
        group
      _ = d*v*z := by rw [RD, SA, RU, SV, RV, SU, RA]
  exact (show Commute (r*(s*r)^3) (d*v*z) from
    (mul_inv_eq_iff_eq_mul.mp hc)).symm

/-- Under the tenth-power relation, the involution sdvzs centralizes (rs)⁵r. -/
public theorem braid_ten_commute (h10 : (r*s)^10 = 1) :
    Commute (s*d*v*z*s) ((r*s)^5*r) := by
  have rr : r*r=1 := by simpa only [pow_two] using h.eq20_r
  have ss : s*s=1 := by simpa only [pow_two] using h.s_sq
  have he : MulAut.conj s (r*(s*r)^3) = (r*s)^5*r := by
    apply mul_left_cancel (a := (r*s)^4)
    calc
      (r*s)^4 * MulAut.conj s (r*(s*r)^3) = s := by
        simp only [MulAut.conj_apply, sqinv h.s_sq, pow_succ, pow_zero,
          mul_assoc, tail rr, tail ss, one_mul]
      _ = (r*s)^10*s := by rw [h10, one_mul]
      _ = (r*s)^4*((r*s)^5*r) := by
        simp only [pow_succ, pow_zero, mul_assoc, ss, one_mul, mul_one]
  have hc := congrArg (MulAut.conj s) h.braid_commute_dvz_reflection.eq
  simp only [map_mul, he] at hc
  simpa only [MulAut.conj_apply, sqinv h.s_sq, mul_assoc, tail ss, one_mul,
    Commute, SemiconjBy] using hc

private theorem D_sq : (d*v*z)^2=1 := by
  have AA : (a*v*z)^2=1 := by
    have aa : a*a=1 := by simpa only [pow_two] using h.a_sq
    have vv : v*v=1 := by simpa only [pow_two] using h.v_sq
    have zz : z*z=1 := by simpa only [pow_two] using h.z_sq
    simp only [pow_two, mul_assoc, tail h.comm_az.symm.eq, tail h.comm_av.symm.eq,
      tail h.comm_zv.eq, tail aa, tail vv, zz, one_mul]
  rw [← h.conj_r_A, ← map_pow, AA, map_one]

/-- Equation (26) in its braid form. -/
private theorem D_braid : s*(d*v*z)*s = (d*v*z)*s*(d*v*z) := by
  let D := d*v*z
  have DD : D*D=1 := by simpa only [D, pow_two] using h.D_sq
  have ss : s*s=1 := by simpa only [pow_two] using h.s_sq
  have hc : (s*D)^3=1 := by simpa only [D, mul_assoc] using h.eq26
  calc
    s*D*s = (s*D*s*D*s*D)*(D*s*D) := by
      simp only [mul_assoc, tail DD, tail ss, DD, one_mul, mul_one]
    _ = D*s*D := by
      have he : s*D*s*D*s*D=1 := by simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hc
      rw [he, one_mul]

/-- In fact the two words in (*) are conjugate already before taking powers. -/
public theorem braid_word_conjugation :
    s*d*v*z*s*r = (a*d*v*z)*(s*r)*(a*d*v*z)⁻¹ := by
  let D := d*v*z
  let p := a*u
  let g := a*D
  have DD : D*D=1 := by simpa only [D, pow_two] using h.D_sq
  have Di : D⁻¹=D := sqinv h.D_sq
  have aa : a*a=1 := by simpa only [pow_two] using h.a_sq
  have uu : u*u=1 := by simpa only [pow_two] using h.u_sq
  have pp : p*p=1 := by
    simp only [p, mul_assoc, tail h.comm_au.symm.eq, tail aa, uu, one_mul]
  have DAD : D*a*D=p := by
    have da : d*a*d = a*u := by
      calc
        d*a*d = a*parrottCommutator a d := by
          simp only [parrottCommutator, sqinv h.a_sq, sqinv h.d_sq]
          group
          rw [aa, one_mul]
        _ = a*u := by rw [h.eq11_ad]
    calc
      D*a*D = d*a*(v*z)*D := by
        simp only [D, mul_assoc, tail h.comm_az.symm.eq, tail h.comm_av.symm.eq]
      _ = d*a*d := by
        have vzD : (v*z)*D=d := by
          apply mul_left_cancel (a := d)
          simpa only [D, mul_assoc] using DD.trans (by simpa only [pow_two] using h.d_sq.symm)
        rw [mul_assoc (d*a), vzD]
      _ = p := da
  have Sa : MulAut.conj s a = u := by
    simpa only [MulAut.conj_apply, sqinv h.s_sq] using h.eq25_as
  have Su : MulAut.conj s u = a := by rw [← Sa]; exact conj_involutive h.s_sq a
  have Sp : MulAut.conj s p = p := by
    simp only [p, map_mul, Sa, Su, h.comm_au.symm.eq]
  have sp : s*p=p*s := by
    exact mul_inv_eq_iff_eq_mul.mp Sp
  have Ra : MulAut.conj r a = d*u := by
    simpa only [MulAut.conj_apply, sqinv h.eq20_r] using h.eq23_ar
  have RD : MulAut.conj r D = a*v*z := by
    rw [show D=MulAut.conj r (a*v*z) from h.conj_r_A.symm]
    exact conj_involutive h.eq20_r _
  have Rg : MulAut.conj r g = D*p := by
    rw [show g=a*D from rfl, map_mul, Ra, RD]
    simp only [D, p, mul_assoc,
      tail h.comm_au.symm.eq, tail h.comm_az.symm.eq, tail h.comm_av.symm.eq,
      h.comm_zu.eq, tail h.comm_vu.eq]
  have rg : r*g=D*p*r := mul_inv_eq_iff_eq_mul.mp Rg
  have hc : g⁻¹*(s*D*s*r)*g=s*r := by
    calc
      g⁻¹*(s*D*s*r)*g = (D*a*D)*s*D*(r*g) := by
        rw [show s*D*s=D*s*D from h.D_braid]
        simp only [g, mul_inv_rev, Di, sqinv h.a_sq]
        group
      _ = p*s*D*(D*p*r) := by rw [DAD, rg]
      _ = s*r := by
        simp only [mul_assoc, tail DD, one_mul, tail sp.symm, tail pp]
  calc
    s*d*v*z*s*r = g*(g⁻¹*(s*D*s*r)*g)*g⁻¹ := by dsimp [D]; group
    _ = g*(s*r)*g⁻¹ := by rw [hc]
    _ = _ := by simp only [g, D, mul_assoc]

/-- Parrott's displayed equation (*), with exponent four. -/
public theorem braid_word_fourth_power :
    (s*d*v*z*s*r)^4 = a*d*v*z*(s*r)^4*z*v*d*a := by
  rw [h.braid_word_conjugation]
  have hp := map_pow (MulAut.conj (a*d*v*z)) (s*r) 4
  simp only [MulAut.conj_apply] at hp
  rw [← hp]
  simp only [mul_inv_rev, sqinv h.z_sq, sqinv h.v_sq, sqinv h.d_sq,
    sqinv h.a_sq, mul_assoc]
end Tits.ParrottLocalRelations
