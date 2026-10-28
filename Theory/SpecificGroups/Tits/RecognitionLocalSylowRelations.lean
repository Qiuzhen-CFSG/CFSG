module

public import Theory.SpecificGroups.Tits.RecognitionLocalData

/-!
# The Sylow relations in Parrott's presentation

The supplied local equations imply all 23 presentation relations in groups
I--V. These calculations apply in an arbitrary group: they require neither
existence of a local configuration nor independence of its elementary
generators. The aggregate theorem uses the explicit list of relator indices.

The proof first derives the action of y = x^2 z on v, u and w, and the
commutation of d with v. It then collects the scalar word equations in the
order x, y, d, c, b, a, w, u, v, t, z using inverse-first commutators.
Evaluation of the free-group words, including the previously proved
identities r3 = t and r5 = z, gives the relators.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
sections 3, 5 and 6, pp.678--684. The conventions and scan corrections are
recorded in refs/original/n-group-global/parrott-tits-presentation.md.
-/

namespace Tits.ParrottLocalRelations
variable {G : Type*} [Group G] {z t v u w a b c d x y r s : G}
variable (h : Tits.ParrottLocalRelations z t v u w a b c d x y r s)

private theorem tail {p q o : G} (hp : p * q = o) (k : G) :
    p * (q * k) = o * k := by rw [← mul_assoc, hp]

private theorem sq_inv {p : G} (hp : p ^ 2 = 1) : p⁻¹ = p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)

private theorem reverse {p q o : G} (hp : p * q = q * p * o) :
    q * p = p * q * o⁻¹ := by rw [hp]; group

include h
set_option linter.unusedSimpArgs false in
private theorem y_actions :
    y * v = v * y ∧ y * u = u * y * t ∧ y * w = w * y * v := by
  have vx := reverse ((parrottCommutator_eq_iff x v t).mp h.eq01_xv)
  have ux := reverse ((parrottCommutator_eq_iff x u v).mp h.eq01_xu)
  have wx := reverse ((parrottCommutator_eq_iff x w u).mp h.eq01_xw)
  have tx := ((parrottCommutator_eq_one_iff x t).mp h.eq01_xt).symm.eq
  simp only [sq_inv h.t_sq, sq_inv h.v_sq, sq_inv h.u_sq] at vx ux wx
  have yy : y = x * x * z := by
    apply mul_right_cancel (b := z)
    simp only [mul_assoc, ← pow_two, h.z_sq, mul_one, h.eq04]
  have vv : v*v=1 := by simpa only [pow_two] using h.v_sq
  have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
  have uu : u*u=1 := by simpa only [pow_two] using h.u_sq
  rw [yy]
  constructor
  · simp only [mul_assoc, tail vx, vx, tail tx, tx, tail h.comm_zv.eq,
      h.comm_zv.eq, tail tt, tt, one_mul, mul_one]
  constructor
  · simp only [mul_assoc, tail ux, ux, tail vx, vx, tail h.comm_zu.eq,
      tail h.comm_vu.eq, tail h.comm_zv.eq, tail h.comm_zt.eq,
      tail h.comm_tv.eq, h.comm_zu.eq, h.comm_zv.eq, h.comm_zt.eq,
      h.comm_tv.eq, tail vv, vv, tail tt, tt, one_mul, mul_one]
  · simp only [mul_assoc, tail wx, wx, tail ux, ux, tail h.comm_zw.eq,
      tail h.comm_uw.eq, tail h.comm_zv.eq, tail h.comm_zt.eq,
      tail h.comm_tv.eq, tail h.comm_vu.eq, h.comm_zw.eq, h.comm_zv.eq,
      h.comm_uw.eq, h.comm_vu.eq, tail vv, vv, tail uu, uu, one_mul, mul_one]

private theorem d_v : d * v = v * d := by
  have dd : d*d=1 := by simpa only [pow_two] using h.d_sq
  calc
    d * v = v⁻¹ * d := by
      rw [← h.eq03_db]
      simp only [parrottCommutator, mul_inv_rev, inv_inv, sq_inv h.d_sq]
      group
      simp only [mul_assoc, dd, one_mul, mul_one]
    _ = v * d := by rw [sq_inv h.v_sq]

omit h in
private theorem lift_comm (f : ParrottGenerator → G) (p q : FreeGroup ParrottGenerator) :
    FreeGroup.lift f (parrottCommutator p q) =
      parrottCommutator (FreeGroup.lift f p) (FreeGroup.lift f q) := by
  simp only [parrottCommutator, map_mul, map_inv]

-- One collection pass establishes the scalar equations for all 23 relators.
set_option linter.unusedSimpArgs false in
private theorem sylow_word_relations :
    r ^ 2 = 1 ∧ s ^ 2 = 1 ∧ y ^ 2 = 1 ∧
    (a*v*z) ^ 2 = 1 ∧ (v*z) ^ 2 = 1 ∧ (u*v*z) ^ 2 = 1 ∧
    (d*v*z) ^ 2 = 1 ∧ (b*x*v) ^ 4 = 1 ∧ x ^ 4 = 1 ∧
    (x⁻¹*c*a*w*t*z) ^ 4 = 1 ∧
    parrottCommutator y (a*v*z) = 1 ∧
    parrottCommutator y (b*x*v) = 1 ∧ parrottCommutator y x = 1 ∧
    parrottCommutator y (u*v*z) = t ∧
    parrottCommutator y (x⁻¹*c*a*w*t*z) = (a*v*z)*t*z ∧
    parrottCommutator y (d*v*z) = (x⁻¹*c*a*w*t*z)^2*t*y ∧
    parrottCommutator (a*v*z) (v*z) = 1 ∧
    parrottCommutator (a*v*z) (u*v*z) = 1 ∧
    parrottCommutator (a*v*z) (d*v*z) = (v*z)*(u*v*z) ∧
    parrottCommutator (x⁻¹*c*a*w*t*z) (a*v*z) = (v*z)*z ∧
    parrottCommutator (x⁻¹*c*a*w*t*z) (v*z) = t*z ∧
    parrottCommutator (b*x*v) x = (a*v*z)*t*(v*z) ∧
    parrottCommutator x (v*z) = t := by
  have yv := (y_actions h).1
  have yu := (y_actions h).2.1
  have yw := (y_actions h).2.2
  have dv := d_v h
  have y_eq : y = x ^ 2 * z := by
    apply mul_right_cancel (b := z)
    simp only [mul_assoc, ← pow_two, h.z_sq, mul_one, h.eq04]
  have yx : y*x=x*y := by
    rw [y_eq]
    exact (((Commute.refl x).pow_left 2).mul_left h.comm_zx).eq
  have yt : y*t=t*y := by
    rw [y_eq]
    exact ((((parrottCommutator_eq_one_iff x t).mp h.eq01_xt).pow_left 2).mul_left h.comm_zt).eq
  have ya := (parrottCommutator_eq_one_iff y a).mp h.eq06_ya
  have byc := (parrottCommutator_eq_one_iff b y).mp h.eq18_by
  have ax := (parrottCommutator_eq_one_iff a x).mp h.eq16_ax
  have tx := ((parrottCommutator_eq_one_iff x t).mp h.eq01_xt).symm
  have bw := (parrottCommutator_eq_one_iff b w).mp h.eq02_bw
  have dw := (parrottCommutator_eq_one_iff d w).mp h.eq07_dw
  have du := (parrottCommutator_eq_one_iff d u).mp h.eq08_du
  have cu := (parrottCommutator_eq_one_iff c u).mp h.eq09_cu
  have cw := (parrottCommutator_eq_one_iff c w).mp h.eq09_cw
  have ct := (parrottCommutator_eq_one_iff c t).mp h.eq10_ct
  have bv : Commute b v := by
    rw [← h.eq03_b]
    exact Commute.self_pow b 2
  have vx := reverse ((parrottCommutator_eq_iff x v t).mp h.eq01_xv)
  have ux := reverse ((parrottCommutator_eq_iff x u v).mp h.eq01_xu)
  have wx := reverse ((parrottCommutator_eq_iff x w u).mp h.eq01_xw)
  have cx := reverse ((parrottCommutator_eq_iff x c (a*b*u*v)).mp h.eq19_xc)
  have bx := (parrottCommutator_eq_iff b x a).mp h.eq18_bx
  have aw := (parrottCommutator_eq_iff a w z).mp h.eq02_aw
  have wa := reverse aw
  simp only [sq_inv h.z_sq] at wa
  have ub := reverse ((parrottCommutator_eq_iff b u z).mp h.eq02_bu)
  have bd := reverse ((parrottCommutator_eq_iff d b v).mp h.eq03_db)
  have td := reverse ((parrottCommutator_eq_iff d t z).mp h.eq03_dt)
  have ab := (parrottCommutator_eq_iff a b t).mp h.eq05_ab
  have vc := reverse ((parrottCommutator_eq_iff c v z).mp h.eq10_cv)
  have ad := (parrottCommutator_eq_iff a d u).mp h.eq11_ad
  have ac := (parrottCommutator_eq_iff a c (v*t)).mp h.eq12_ac
  have cd := (parrottCommutator_eq_iff c d (w*u)).mp h.eq14_cd
  have bc := (parrottCommutator_eq_iff b c (u*v)).mp h.eq15_bc
  have cy := reverse ((parrottCommutator_eq_iff y c (a*t*z)).mp h.eq19_yc)
  have dy := reverse ((parrottCommutator_eq_iff y d (b*w)).mp h.eq17_yd)
  have uy := reverse yu
  have wy := reverse yw
  have zz : z*z=1 := by simpa only [pow_two] using h.z_sq
  have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
  have vv : v*v=1 := by simpa only [pow_two] using h.v_sq
  have uu : u*u=1 := by simpa only [pow_two] using h.u_sq
  have ww : w*w=1 := by simpa only [pow_two] using h.w_sq
  have aa : a*a=1 := by simpa only [pow_two] using h.a_sq
  have dd : d*d=1 := by simpa only [pow_two] using h.d_sq
  have yy : y*y=1 := by simpa only [pow_two] using h.y_sq
  have bb : b*b=v := by simpa only [pow_two] using h.eq03_b
  have cc : c*c=w*u := by simpa only [pow_two] using h.eq13
  have xx : x*x=y*z := by simpa only [pow_two] using h.eq04
  have binv : b⁻¹ = b*v := by
    apply inv_eq_of_mul_eq_one_right
    simp only [← mul_assoc, bb, vv]
  have xinv : x⁻¹ = x*y*z := by
    apply inv_eq_of_mul_eq_one_right
    simp only [mul_assoc, tail xx, tail h.comm_zy.eq, tail yy, zz, one_mul]
  simp only [mul_inv_rev, sq_inv h.z_sq, sq_inv h.t_sq, sq_inv h.v_sq,
    sq_inv h.u_sq, sq_inv h.w_sq, sq_inv h.a_sq, binv] at vx ux wx cx ub bd td vc cy dy uy wy
  simp only [parrottCommutator_eq_iff, h.eq20_r, h.s_sq, h.y_sq, h.eq01_x]
  simp only [pow_succ, pow_zero, mul_one, xinv, mul_assoc]
  simp only [mul_assoc, one_mul, mul_one, and_true, true_and,
    tail (vx), vx,
    tail (ux), ux,
    tail (wx), wx,
    tail (cx), cx,
    tail (bx), bx,
    tail (ax.eq), ax.eq,
    tail (tx.eq), tx.eq,
    tail (h.comm_zx.eq), h.comm_zx.eq,
    tail (yx), yx,
    tail (byc.eq), byc.eq,
    tail (cy), cy,
    tail (dy), dy,
    tail (ya.symm.eq), ya.symm.eq,
    tail (uy), uy,
    tail (wy), wy,
    tail (yv.symm), yv.symm,
    tail (yt.symm), yt.symm,
    tail (h.comm_zy.eq), h.comm_zy.eq,
    tail (cd), cd,
    tail (bd), bd,
    tail (ad), ad,
    tail (dw.symm.eq), dw.symm.eq,
    tail (du.symm.eq), du.symm.eq,
    tail (dv.symm), dv.symm,
    tail (td), td,
    tail (h.comm_zd.eq), h.comm_zd.eq,
    tail (bc), bc,
    tail (ac), ac,
    tail (cw.symm.eq), cw.symm.eq,
    tail (cu.symm.eq), cu.symm.eq,
    tail (vc), vc,
    tail (ct.symm.eq), ct.symm.eq,
    tail (h.comm_zc.eq), h.comm_zc.eq,
    tail (ab), ab,
    tail (bw.symm.eq), bw.symm.eq,
    tail (ub), ub,
    tail (bv.symm.eq), bv.symm.eq,
    tail (h.comm_bt.symm.eq), h.comm_bt.symm.eq,
    tail (h.comm_zb.eq), h.comm_zb.eq,
    tail wa, wa,
    tail (h.comm_au.symm.eq), h.comm_au.symm.eq,
    tail (h.comm_av.symm.eq), h.comm_av.symm.eq,
    tail (h.comm_at.symm.eq), h.comm_at.symm.eq,
    tail (h.comm_az.symm.eq), h.comm_az.symm.eq,
    tail (h.comm_uw.eq), h.comm_uw.eq,
    tail (h.comm_vw.eq), h.comm_vw.eq,
    tail (h.comm_tw.eq), h.comm_tw.eq,
    tail (h.comm_zw.eq), h.comm_zw.eq,
    tail (h.comm_vu.eq), h.comm_vu.eq,
    tail (h.comm_tu.eq), h.comm_tu.eq,
    tail (h.comm_zu.eq), h.comm_zu.eq,
    tail (h.comm_tv.eq), h.comm_tv.eq,
    tail (h.comm_zv.eq), h.comm_zv.eq,
    tail (h.comm_zt.eq), h.comm_zt.eq,
    tail (zz), zz,
    tail (tt), tt,
    tail (vv), vv,
    tail (uu), uu,
    tail (ww), ww,
    tail (aa), aa,
    tail (dd), dd,
    tail (yy), yy,
    tail (bb), bb,
    tail (cc), cc,
    tail (xx), xx]

set_option linter.unusedSimpArgs false in
/-- The local equations satisfy precisely the 23 relators in groups I--V. -/
public theorem relators_I_V (i : ParrottRelatorIndex)
    (hi : i ∈ ([.i_r1, .i_r8, .i_s1, .i_s2, .i_s4, .i_s6, .i_s8,
      .i_s3, .i_s5, .i_s7, .ii_s1_s2, .ii_s1_s3, .ii_s1_s5,
      .iii_s1_s6, .iii_s1_s7, .iii_s1_s8, .iv_s2_s4, .iv_s2_s6,
      .iv_s2_s8, .iv_s7_s2, .v_s7_s4, .v_s3_s5, .v_s5_s4] : List ParrottRelatorIndex)) :
    FreeGroup.lift (parrottRecognitionWords z t v u w a b c d x y r s)
      (parrottRelator i) = 1 := by
  rcases sylow_word_relations h with
    ⟨hr, hs, hy, h2, h4, h6, h8, h3, h5, h7,
      h12, h13, h15, h16, h17, h18, h24, h26, h28, h72, h74, h35, h54⟩
  cases i <;> simp at hi
  all_goals simp only [parrottRelator, map_mul, map_pow, map_inv, lift_comm,
    FreeGroup.lift_apply_of, h.r3, h.r5, parrottRecognitionWords]
  all_goals try rw [mul_inv_eq_one]
  all_goals assumption

end Tits.ParrottLocalRelations
