module

public import Theory.SpecificGroups.Tits.RecognitionLocalData

/-!
# The two core coordinate systems in Parrott's Sylow calculation

Equations (1)–(15) have two alternatives. The second is converted to the first
by explicit words in the original group. The first substitution changes v
to vt; conjugation by x restores the prescribed v.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed pp.678–680, especially the displayed substitution on p.680.
-/

namespace Tits

/-- Equations through (15), before the final choices of x and y. The Boolean
records the primed Case 2 equations; the a,x alternative is established on p.678. -/
public structure ParrottSylowSeedRelations {G : Type*} [Group G]
    (caseTwo : Bool) (z t v u w a b c d x : G) : Prop where
  z_sq : z ^ 2 = 1
  t_sq : t ^ 2 = 1
  v_sq : v ^ 2 = 1
  u_sq : u ^ 2 = 1
  w_sq : w ^ 2 = 1
  a_sq : a ^ 2 = 1
  comm_zt : Commute z t
  comm_zv : Commute z v
  comm_zu : Commute z u
  comm_zw : Commute z w
  comm_tv : Commute t v
  comm_tu : Commute t u
  comm_tw : Commute t w
  comm_vu : Commute v u
  comm_vw : Commute v w
  comm_uw : Commute u w
  comm_az : Commute a z
  comm_at : Commute a t
  comm_av : Commute a v
  comm_au : Commute a u
  comm_zb : Commute z b
  comm_zc : Commute z c
  comm_zd : Commute z d
  comm_zx : Commute z x
  comm_bt : Commute b t
  d_sq : d ^ 2 = 1
  eq01_x : x ^ 4 = 1
  eq01_xt : parrottCommutator x t = 1
  eq01_xv : parrottCommutator x v = t
  eq01_xu : parrottCommutator x u = v
  eq01_xw : parrottCommutator x w = u
  eq02_bw : parrottCommutator b w = 1
  eq02_aw : parrottCommutator a w = z
  eq02_bu : parrottCommutator b u = z
  eq03_db : parrottCommutator d b = v
  eq03_dt : parrottCommutator d t = z
  eq05_ab : parrottCommutator a b = t
  eq07_dw : parrottCommutator d w = 1
  eq08_du : parrottCommutator d u = 1
  eq09_cu : parrottCommutator c u = 1
  eq09_cw : parrottCommutator c w = 1
  eq10_ct : parrottCommutator c t = 1
  eq10_cv : parrottCommutator c v = z
  eq11_ad : parrottCommutator a d = if caseTwo then u * v else u
  eq12_ac : parrottCommutator a c = if caseTwo then v else v * t
  eq14_cd : parrottCommutator c d = if caseTwo then w else w * u
  eq15_bc : parrottCommutator b c = if caseTwo then u * t else u * v
  eq03_b : b ^ 2 = v
  eq13 : c ^ 2 = if caseTwo then w else w * u
  ax_alternative : parrottCommutator a x = 1 ∨ parrottCommutator a x = t

namespace ParrottSylowSeedRelations

variable {G H : Type*} [Group G] [Group H]
variable {caseTwo : Bool} {z t v u w a b c d x : G}

/-- Transport every seed relation along a homomorphism. -/
public theorem map (h : ParrottSylowSeedRelations caseTwo z t v u w a b c d x)
    (f : G →* H) : ParrottSylowSeedRelations caseTwo
      (f z) (f t) (f v) (f u) (f w) (f a) (f b) (f c) (f d) (f x) := by
  have hc (g k : G) : f (parrottCommutator g k) =
      parrottCommutator (f g) (f k) := by simp only [parrottCommutator, map_mul, map_inv]
  constructor
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.z_sq
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.t_sq
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.v_sq
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.u_sq
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.w_sq
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.a_sq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_zt.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_zv.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_zu.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_zw.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_tv.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_tu.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_tw.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_vu.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_vw.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_uw.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_az.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_at.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_av.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_au.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_zb.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_zc.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_zd.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_zx.eq
  · simpa only [Commute, SemiconjBy, map_mul] using congrArg f h.comm_bt.eq
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.d_sq
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq01_x
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq01_xt
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq01_xv
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq01_xu
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq01_xw
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq02_bw
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq02_aw
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq02_bu
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq03_db
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq03_dt
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq05_ab
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq07_dw
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq08_du
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq09_cu
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq09_cw
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq10_ct
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq10_cv
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq11_ad
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq12_ac
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq14_cd
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq15_bc
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq03_b
  · simpa only [hc, map_pow, map_one, map_mul, apply_ite] using congrArg f h.eq13
  · rcases h.ax_alternative with ha | ha
    · exact Or.inl (by simpa only [hc, map_one] using congrArg f ha)
    · exact Or.inr (by simpa only [hc] using congrArg f ha)

private theorem sqinv {p : G} (hp : p ^ 2 = 1) : p⁻¹ = p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem reverse {p q r : G} (h : p*q=q*p*r) : q*p=p*q*r⁻¹ := by rw [h]; group

set_option maxHeartbeats 1200000 in
set_option linter.unusedSimpArgs false in
/-- The printed Case 2 substitution, with the necessary inversion of x.
The temporary marked vector is vt; the subsequent conjugation restores v. -/
public theorem caseTwo_raw (h : ParrottSylowSeedRelations true z t v u w a b c d x) :
    ParrottSylowSeedRelations false z t (v*t) u (w*u) a (a*b*t) c (c*d*u) x⁻¹ := by
  have dv : d*v=v*d := by
    have dd : d*d=1 := by simpa only [pow_two] using h.d_sq
    calc
      d*v = v⁻¹*d := by
        rw [← h.eq03_db]
        simp -failIfUnchanged only [parrottCommutator, mul_inv_rev, inv_inv, sqinv h.d_sq]
        group
        simp -failIfUnchanged only [mul_assoc, dd, one_mul, mul_one]
      _ = v*d := by rw [sqinv h.v_sq]
  have bv : b*v=v*b := by
    rw [← h.eq03_b]
    exact (Commute.self_pow b 2).eq
  have zt := h.comm_zt.eq
  have zv := h.comm_zv.eq
  have zu := h.comm_zu.eq
  have zw := h.comm_zw.eq
  have tv := h.comm_tv.eq
  have tu := h.comm_tu.eq
  have tw := h.comm_tw.eq
  have vu := h.comm_vu.eq
  have vw := h.comm_vw.eq
  have uw := h.comm_uw.eq
  have za := h.comm_az.symm.eq
  have ta := h.comm_at.symm.eq
  have va := h.comm_av.symm.eq
  have ua := h.comm_au.symm.eq
  have zb := h.comm_zb.eq
  have zc := h.comm_zc.eq
  have zd := h.comm_zd.eq
  have zx := h.comm_zx.eq
  have tb := h.comm_bt.symm.eq
  have tx := ((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt).symm.eq
  have wb := ((parrottCommutator_eq_one_iff _ _).mp h.eq02_bw).symm.eq
  have wd := ((parrottCommutator_eq_one_iff _ _).mp h.eq07_dw).symm.eq
  have ud := ((parrottCommutator_eq_one_iff _ _).mp h.eq08_du).symm.eq
  have uc := ((parrottCommutator_eq_one_iff _ _).mp h.eq09_cu).symm.eq
  have wc := ((parrottCommutator_eq_one_iff _ _).mp h.eq09_cw).symm.eq
  have tc := ((parrottCommutator_eq_one_iff _ _).mp h.eq10_ct).symm.eq
  have vx := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq01_xv)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at vx
  have ux := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq01_xu)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ux
  have wx := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq01_xw)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at wx
  have wa := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_aw)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at wa
  have ub := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_bu)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ub
  have bd := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_db)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bd
  have td := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_dt)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at td
  have ab := ((parrottCommutator_eq_iff _ _ _).mp h.eq05_ab)
  have vc := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq10_cv)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at vc
  have ad := ((parrottCommutator_eq_iff _ _ _).mp h.eq11_ad)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ad
  have ac := ((parrottCommutator_eq_iff _ _ _).mp h.eq12_ac)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ac
  have cd := ((parrottCommutator_eq_iff _ _ _).mp h.eq14_cd)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at cd
  have bc := ((parrottCommutator_eq_iff _ _ _).mp h.eq15_bc)
  simp -failIfUnchanged only [Bool.true_eq, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bc
  have vd := dv.symm
  have vb := bv.symm
  have zz : z*z=1 := by simpa only [pow_two, Bool.true_eq, ↓reduceIte] using h.z_sq
  have tt : t*t=1 := by simpa only [pow_two, Bool.true_eq, ↓reduceIte] using h.t_sq
  have vv : v*v=1 := by simpa only [pow_two, Bool.true_eq, ↓reduceIte] using h.v_sq
  have uu : u*u=1 := by simpa only [pow_two, Bool.true_eq, ↓reduceIte] using h.u_sq
  have ww : w*w=1 := by simpa only [pow_two, Bool.true_eq, ↓reduceIte] using h.w_sq
  have aa : a*a=1 := by simpa only [pow_two, Bool.true_eq, ↓reduceIte] using h.a_sq
  have dd : d*d=1 := by simpa only [pow_two, Bool.true_eq, ↓reduceIte] using h.d_sq
  have bb : b*b=v := by simpa only [pow_two, Bool.true_eq, ↓reduceIte] using h.eq03_b
  have cc : c*c=w := by simpa only [pow_two, Bool.true_eq, ↓reduceIte] using h.eq13
  have binv : b⁻¹=b*v := by
    apply inv_eq_of_mul_eq_one_right
    simp -failIfUnchanged only [← mul_assoc, bb, vv]
  have cinv : c⁻¹=c*w := by
    apply inv_eq_of_mul_eq_one_right
    simp -failIfUnchanged only [← mul_assoc, cc, ww]
  have xinv : x⁻¹=x*x*x := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h.eq01_x
  have xxxx : x*(x*(x*x))=1 := by
    simpa only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h.eq01_x
  have xxxx_tail (k : G) : x*(x*(x*(x*k)))=k := by
    calc
      x*(x*(x*(x*k))) = (x*(x*(x*x)))*k := by simp -failIfUnchanged only [mul_assoc]
      _ = k := by rw [xxxx, one_mul]
  rcases h.ax_alternative with hax | hax
  all_goals
    have ax := (parrottCommutator_eq_iff _ _ _).mp hax
    constructor
    all_goals
      simp -failIfUnchanged only [parrottCommutator_eq_iff, Commute, SemiconjBy, Bool.false_eq_true, ↓reduceIte]
      simp -failIfUnchanged only [pow_succ, pow_zero, mul_one, mul_inv_rev, inv_inv, sqinv h.z_sq,
        sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq,
        sqinv h.a_sq, sqinv h.d_sq, binv, cinv, xinv, mul_assoc]
      simp -failIfUnchanged only [mul_assoc, one_mul, mul_one, true_or, or_true, xxxx, xxxx_tail,
        tail zt, zt,
        tail zv, zv,
        tail zu, zu,
        tail zw, zw,
        tail tv, tv,
        tail tu, tu,
        tail tw, tw,
        tail vu, vu,
        tail vw, vw,
        tail uw, uw,
        tail za, za,
        tail ta, ta,
        tail va, va,
        tail ua, ua,
        tail zb, zb,
        tail zc, zc,
        tail zd, zd,
        tail zx, zx,
        tail tb, tb,
        tail tx, tx,
        tail wb, wb,
        tail wd, wd,
        tail ud, ud,
        tail uc, uc,
        tail wc, wc,
        tail tc, tc,
        tail vx, vx,
        tail ux, ux,
        tail wx, wx,
        tail wa, wa,
        tail ub, ub,
        tail bd, bd,
        tail td, td,
        tail ab, ab,
        tail vc, vc,
        tail ad, ad,
        tail ac, ac,
        tail cd, cd,
        tail bc, bc,
        tail vd, vd,
        tail vb, vb,
        tail zz, zz,
        tail tt, tt,
        tail vv, vv,
        tail uu, uu,
        tail ww, ww,
        tail aa, aa,
        tail dd, dd,
        tail bb, bb,
        tail cc, cc,
        tail ax, ax]

end ParrottSylowSeedRelations
end Tits
