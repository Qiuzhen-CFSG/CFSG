module
public import Theory.SpecificGroups.Tits.RecognitionSylowOuterParameters
public import Theory.SpecificGroups.Tits.RecognitionSylowResidualSymmetry

/-!
# Coupled parameters for Parrott's last outer images

Once [a,x]=1 and [b,x]=a, the elementary error bounds leave three Boolean
coordinates in each of the c and d images. Conjugating [b,c], [d,b], and [c,d]
eliminates three independent bits. The prescribed action of y=x²z on d
identifies the remaining c bits. Thus the two left errors are respectively
(1,1), (1,z), (tz,vt), or (tz,vtz).

In the first pair of cases the original coordinates satisfy the last outer
equations. In the second pair, the simultaneous substitution
(a,b,c,d) ↦ (at,bv,cu,dw) does so. These are word calculations in an arbitrary
group with the seed relations; no completed frame or presentation is assumed.
The finite case splits are staged by the four constraints to limit elaboration
and kernel-checking cost.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.680, the computations preceding equation (19).
-/

open Subgroup Tits
namespace Tits.ParrottSylowSeedRelations
variable {G : Type*} [Group G] {z t v u w a b c d x : G}
private theorem sqinv {p : G} (hp : p^2=1) : p⁻¹=p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem reverse {p q r : G} (h : p*q=q*p*r) : q*p=p*q*r⁻¹ := by rw [h]; group
private theorem pc_conj {p q r : G} (hr : parrottCommutator p q = r) :
    q⁻¹*p*q=p*r := by rw [← hr, parrottCommutator]; group
private theorem pc_conj_rev {p q r : G} (hr : parrottCommutator p q = r) :
    p⁻¹*q*p=q*r⁻¹ := by rw [← hr, parrottCommutator]; group
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000 in
/-- The middle equations and the square action restrict the two left errors
to the four coupled possibilities needed for the last coordinate choice. -/
public theorem last_image_alternatives
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hz : z ≠ 1) (hax : parrottCommutator a x = 1)
    (hbx : parrottCommutator b x = a)
    (hyc : parrottCommutator (x^2*z) c = a*t*z)
    (hyd : parrottCommutator (x^2*z) d = b*w)
    (ci cj ck di dj dk : Bool)
    (hc : x⁻¹*c*x = (c*(a*b*u*v)⁻¹)*z^ci.toNat*t^cj.toNat*(u*v)^ck.toNat)
    (hd : x⁻¹*d*x = (d*(a*b*c*u*v)⁻¹)*z^di.toNat*(t*u)^dj.toNat*(v*u)^dk.toNat) :
    (x⁻¹*c*x = c*(a*b*u*v)⁻¹ ∧
      (x⁻¹*d*x = d*(a*b*c*u*v)⁻¹ ∨ x⁻¹*d*x = z*(d*(a*b*c*u*v)⁻¹))) ∨
    (x⁻¹*c*x = (t*z)*(c*(a*b*u*v)⁻¹) ∧
      (x⁻¹*d*x = (v*t)*(d*(a*b*c*u*v)⁻¹) ∨
       x⁻¹*d*x = (v*t*z)*(d*(a*b*c*u*v)⁻¹))) := by
  let P : G ≃* G := MulAut.conj x⁻¹
  have pe (g : G) : P g = x⁻¹*g*x := by simp [P]
  have pz : P z = z := by rw [pe, mul_assoc, h.comm_zx.eq, inv_mul_cancel_left]
  have pt : P t = t := by rw [pe]; simpa using pc_conj_rev h.eq01_xt
  have pv : P v = v*t := by rw [pe]; simpa only [sqinv h.t_sq] using pc_conj_rev h.eq01_xv
  have pu : P u = u*v := by rw [pe]; simpa only [sqinv h.v_sq] using pc_conj_rev h.eq01_xu
  have pw : P w = w*u := by rw [pe]; simpa only [sqinv h.u_sq] using pc_conj_rev h.eq01_xw
  have pa : P a = a := by rw [pe]; simpa using pc_conj hax
  have pb : P b = b*a := by rw [pe]; exact pc_conj hbx
  have pc : P c = _ := (pe c).trans hc
  have pd : P d = _ := (pe d).trans hd
  have map_pc (p q : G) : P (parrottCommutator p q) = parrottCommutator (P p) (P q) := by
    simp only [parrottCommutator, map_mul, map_inv]
  have hbc := congrArg P h.eq15_bc
  have hdb := congrArg P h.eq03_db
  have hcd := congrArg P h.eq14_cd
  have p2 (g : G) (hg : Commute z g) : P (P g) = (x^2*z)⁻¹*g*(x^2*z) := by
    rw [pe, pe]
    have hxz := h.comm_zx.eq
    simp only [pow_two, mul_inv_rev]
    calc
      _ = x⁻¹*x⁻¹*g*x*x := by group
      _ = z⁻¹*(x⁻¹*x⁻¹*g*x*x)*z := by
        have he : Commute z (x⁻¹*x⁻¹*g*x*x) :=
          ((((h.comm_zx.inv_right).mul_right h.comm_zx.inv_right).mul_right hg).mul_right h.comm_zx).mul_right h.comm_zx
        have heq : z⁻¹*((x⁻¹*x⁻¹*g*x*x)*z) = x⁻¹*x⁻¹*g*x*x := by
          rw [← he.eq, inv_mul_cancel_left]
        simpa only [mul_assoc] using heq.symm
      _ = _ := by group
  have hcc : P (P c) = c*(a*t*z)⁻¹ := (p2 c h.comm_zc).trans (pc_conj_rev hyc)
  have hdd : P (P d) = d*(b*w)⁻¹ := (p2 d h.comm_zd).trans (pc_conj_rev hyd)
  simp only [map_pc, map_mul, map_inv, map_pow, map_one,
    pz, pt, pv, pu, pw, pa, pb, pc, pd, Bool.false_eq_true, ↓reduceIte] at hbc hdb hcd hcc hdd
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
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at vx
  have ux := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq01_xu)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ux
  have wx := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq01_xw)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at wx
  have wa := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_aw)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at wa
  have ub := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_bu)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ub
  have bd := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_db)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bd
  have td := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_dt)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at td
  have ab := ((parrottCommutator_eq_iff _ _ _).mp h.eq05_ab)
  have vc := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq10_cv)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at vc
  have ad := ((parrottCommutator_eq_iff _ _ _).mp h.eq11_ad)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ad
  have ac := ((parrottCommutator_eq_iff _ _ _).mp h.eq12_ac)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ac
  have cd := ((parrottCommutator_eq_iff _ _ _).mp h.eq14_cd)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at cd
  have bc := ((parrottCommutator_eq_iff _ _ _).mp h.eq15_bc)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bc
  have vd := dv.symm
  have vb := bv.symm
  have zz : z*z=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.z_sq
  have tt : t*t=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.t_sq
  have vv : v*v=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.v_sq
  have uu : u*u=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.u_sq
  have ww : w*w=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.w_sq
  have aa : a*a=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.a_sq
  have dd : d*d=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.d_sq
  have bb : b*b=v := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.eq03_b
  have cc : c*c=w*u := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.eq13
  have binv : b⁻¹=b*v := by
    apply inv_eq_of_mul_eq_one_right
    simp only [← mul_assoc, bb, vv]
  have cinv : c⁻¹=c*w*u := by
    apply inv_eq_of_mul_eq_one_right
    simp only [mul_assoc, tail cc, cc, tail uw, uw, tail uu, uu, tail ww, ww, mul_one, one_mul]
  have hk : ck = false := by
    cases ci <;> cases cj <;> cases ck <;> first | rfl | skip
    all_goals
      simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true,
        pow_zero, pow_one, pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq,
        sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc,
        one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu,
        tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va,
        tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx,
        tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx,
        tail ux, ux, tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab,
        tail vc, vc, tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb,
        tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd,
        tail bb, bb, tail cc, cc] at hbc
    all_goals
      simp only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right, left_eq_mul,
        right_eq_mul, hz, Ne.symm hz] at hbc
  subst ck
  have hjk : dk = dj := by
    cases di <;> cases dj <;> cases dk <;> first | rfl | skip
    all_goals
      simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true,
        pow_zero, pow_one, pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq,
        sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc,
        one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu,
        tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va,
        tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx,
        tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx,
        tail ux, ux, tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab,
        tail vc, vc, tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb,
        tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd,
        tail bb, bb, tail cc, cc] at hdb
    all_goals
      simp only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right, left_eq_mul,
        right_eq_mul, hz, Ne.symm hz] at hdb
  subst dk
  have hjd : dj = cj := by
    cases ci <;> cases cj <;> cases di <;> cases dj <;> first | rfl | skip
    all_goals
      simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true,
        pow_zero, pow_one, pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq,
        sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc,
        one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu,
        tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va,
        tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx,
        tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx,
        tail ux, ux, tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab,
        tail vc, vc, tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb,
        tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd,
        tail bb, bb, tail cc, cc] at hcd
    all_goals
      simp only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right, left_eq_mul,
        right_eq_mul, hz, Ne.symm hz] at hcd
  subst dj
  have hij : ci = cj := by
    cases ci <;> cases cj <;> cases di <;> first | rfl | skip
    all_goals
      simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true,
        pow_zero, pow_one, pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq,
        sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc,
        one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu,
        tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va,
        tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx,
        tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx,
        tail ux, ux, tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab,
        tail vc, vc, tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb,
        tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd,
        tail bb, bb, tail cc, cc] at hdd
    all_goals
      simp only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right, left_eq_mul,
        right_eq_mul, hz, Ne.symm hz] at hdd
  subst ci
  rw [hc, hd]
  cases cj <;> cases di
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
      pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
      sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one,
      tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw,
      tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va, tail ua, ua,
      tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx, tail wb, wb,
      tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx, tail ux, ux,
      tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc,
      tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz,
      tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb,
      tail cc, cc, and_true, true_and, true_or, or_true]

private theorem pc_from_conj (p q : G) :
    parrottCommutator p q = (q⁻¹*(p⁻¹*q*p))⁻¹ := by
  simp only [parrottCommutator, mul_inv_rev, inv_inv]
  group

set_option maxHeartbeats 2400000 in
/-- The two coupled image alternatives are normalized either in the original
coordinates or by the residual substitution. -/
public theorem normalize_last_images
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (halt :
    (x⁻¹*c*x = c*(a*b*u*v)⁻¹ ∧
      (x⁻¹*d*x = d*(a*b*c*u*v)⁻¹ ∨ x⁻¹*d*x = z*(d*(a*b*c*u*v)⁻¹))) ∨
    (x⁻¹*c*x = (t*z)*(c*(a*b*u*v)⁻¹) ∧
      (x⁻¹*d*x = (v*t)*(d*(a*b*c*u*v)⁻¹) ∨
       x⁻¹*d*x = (v*t*z)*(d*(a*b*c*u*v)⁻¹)))) :
    (parrottCommutator x c = a*b*u*v ∧
      (parrottCommutator x d = a*b*c*u*v ∨ parrottCommutator x d = (a*b*c*u*v)*z)) ∨
    (parrottCommutator x (c*u) = (a*t)*(b*v)*u*v ∧
      (parrottCommutator x (d*w) = (a*t)*(b*v)*(c*u)*u*v ∨
       parrottCommutator x (d*w) = ((a*t)*(b*v)*(c*u)*u*v)*z)) := by
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
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at vx
  have ux := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq01_xu)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ux
  have wx := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq01_xw)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at wx
  have wa := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_aw)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at wa
  have ub := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_bu)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ub
  have bd := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_db)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bd
  have td := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_dt)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at td
  have ab := ((parrottCommutator_eq_iff _ _ _).mp h.eq05_ab)
  have vc := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq10_cv)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at vc
  have ad := ((parrottCommutator_eq_iff _ _ _).mp h.eq11_ad)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ad
  have ac := ((parrottCommutator_eq_iff _ _ _).mp h.eq12_ac)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ac
  have cd := ((parrottCommutator_eq_iff _ _ _).mp h.eq14_cd)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at cd
  have bc := ((parrottCommutator_eq_iff _ _ _).mp h.eq15_bc)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bc
  have vd := dv.symm
  have vb := bv.symm
  have zz : z*z=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.z_sq
  have tt : t*t=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.t_sq
  have vv : v*v=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.v_sq
  have uu : u*u=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.u_sq
  have ww : w*w=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.w_sq
  have aa : a*a=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.a_sq
  have dd : d*d=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.d_sq
  have bb : b*b=v := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.eq03_b
  have cc : c*c=w*u := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.eq13
  have binv : b⁻¹=b*v := by
    apply inv_eq_of_mul_eq_one_right
    simp only [← mul_assoc, bb, vv]
  have cinv : c⁻¹=c*w*u := by
    apply inv_eq_of_mul_eq_one_right
    simp only [mul_assoc, tail cc, cc, tail uw, uw, tail uu, uu, tail ww, ww, mul_one, one_mul]

  have hxu : x⁻¹*u*x = u*v := by simpa only [sqinv h.v_sq] using pc_conj_rev h.eq01_xu
  have hxw : x⁻¹*w*x = w*u := by simpa only [sqinv h.u_sq] using pc_conj_rev h.eq01_xw
  have hcu : x⁻¹*(c*u)*x = (x⁻¹*c*x)*(u*v) := by rw [← hxu]; group
  have hdw : x⁻¹*(d*w)*x = (x⁻¹*d*x)*(w*u) := by rw [← hxw]; group
  rcases halt with ⟨hc, hd | hd⟩ | ⟨hc, hd | hd⟩
  · left
    constructor
    · simp only [pc_from_conj, hc, inv_mul_cancel_left, inv_inv]
    · left; simp only [pc_from_conj, hd, inv_mul_cancel_left, inv_inv]
  · left
    constructor
    · simp only [pc_from_conj, hc, inv_mul_cancel_left, inv_inv]
    · right
      rw [pc_from_conj, hd]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
        pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
        sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one,
        tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw,
        tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va, tail ua, ua,
        tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx, tail wb, wb,
        tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx, tail ux, ux,
        tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc,
        tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz,
        tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb,
        tail cc, cc]
  · right
    constructor
    · rw [pc_from_conj, hcu, hc]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
        pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
        sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one,
        tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw,
        tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va, tail ua, ua,
        tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx, tail wb, wb,
        tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx, tail ux, ux,
        tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc,
        tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz,
        tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb,
        tail cc, cc]
    · left
      rw [pc_from_conj, hdw, hd]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
        pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
        sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one,
        tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw,
        tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va, tail ua, ua,
        tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx, tail wb, wb,
        tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx, tail ux, ux,
        tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc,
        tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz,
        tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb,
        tail cc, cc]
  · right
    constructor
    · rw [pc_from_conj, hcu, hc]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
        pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
        sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one,
        tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw,
        tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va, tail ua, ua,
        tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx, tail wb, wb,
        tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx, tail ux, ux,
        tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc,
        tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz,
        tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb,
        tail cc, cc]
    · right
      rw [pc_from_conj, hdw, hd]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
        pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
        sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one,
        tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw,
        tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va, tail ua, ua,
        tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx, tail wb, wb,
        tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx, tail ux, ux,
        tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc,
        tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz,
        tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb,
        tail cc, cc]

end Tits.ParrottSylowSeedRelations
