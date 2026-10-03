module

public import Theory.SpecificGroups.Tits.RecognitionSylowMiddleAdjustment
public import Theory.SpecificGroups.Tits.RecognitionSylowOuterParameters

/-!
# Compatibility of Parrott's middle commutators

Under (16) and (17), the b,x commutator cannot have a t-error. Use the
outer-image parameters supplied by the seed relations. Conjugating [b,c]
eliminates the (u*v)-coordinate of the c-image. Conjugating [d,b] relates
the two noncentral d-image coordinates to the proposed t-error. Finally,
apply [c, -] to the equality for the second x-conjugate of d supplied by
(17): the error would force z = 1. The finite Boolean calculation uses only
these three equalities and the seed's group relations.

The remaining z-error is removed by x ↦ xu. Its prescribed square changes
y = x²z to yv, and v centralizes both d and bw, so (17) is preserved.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed p.680, equations (16)–(18). The collection rules follow the
existing proofs in RecognitionSylowMiddleAdjustment.
-/

open Subgroup
namespace Tits.ParrottSylowSeedRelations
variable {G : Type*} [Group G] {z t v u w a b c d x : G}
private theorem sqinv {p : G} (hp : p ^ 2 = 1) : p⁻¹ = p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem reverse {p q r : G} (h : p*q=q*p*r) : q*p=p*q*r⁻¹ := by rw [h]; group
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
private theorem exclude_t_parameter
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) (hz : z ≠ 1)
    (i ci cj ck di dj dk : Bool)
    (P : G ≃* G)
    (Pz : P z = z) (Pt : P t = t) (Pv : P v = v*t)
    (Pu : P u = u*v) (Pa : P a = a)
    (Pb : P b = (b*a)*z^i.toNat*t)
    (Pc : P c = (c*(a*b*u*v)⁻¹)*z^ci.toNat*t^cj.toNat*(u*v)^ck.toNat)
    (Pd : P d = (d*(a*b*c*u*v)⁻¹)*z^di.toNat*(t*u)^dj.toNat*(v*u)^dk.toNat)
    (P2d : P (P d) = d*(b*w)⁻¹) : False := by
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
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at vx
  have ux := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq01_xu)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ux
  have wx := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq01_xw)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at wx
  have wa := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_aw)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at wa
  have ub := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_bu)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ub
  have bd := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_db)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bd
  have td := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_dt)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at td
  have ab := ((parrottCommutator_eq_iff _ _ _).mp h.eq05_ab)
  have vc := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq10_cv)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at vc
  have ad := ((parrottCommutator_eq_iff _ _ _).mp h.eq11_ad)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ad
  have ac := ((parrottCommutator_eq_iff _ _ _).mp h.eq12_ac)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ac
  have cd := ((parrottCommutator_eq_iff _ _ _).mp h.eq14_cd)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at cd
  have bc := ((parrottCommutator_eq_iff _ _ _).mp h.eq15_bc)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bc
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
    simp -failIfUnchanged only [← mul_assoc, bb, vv]
  have cinv : c⁻¹=c*u*w := by
    apply inv_eq_of_mul_eq_one_right
    simp -failIfUnchanged only [mul_assoc, tail uc, uc, tail wc, wc, tail uw, uw, tail cc, cc, tail ww, ww, tail uu, uu, one_mul, mul_one]
  have hbc := congrArg P ((parrottCommutator_eq_iff _ _ _).mp h.eq15_bc)
  have hdb := congrArg P ((parrottCommutator_eq_iff _ _ _).mp h.eq03_db)
  have hdd := congrArg (fun g => parrottCommutator c (d⁻¹*g*(b*w))) P2d
  simp only [Pd, map_mul, map_inv, map_pow, Pb, Pc, Pa, Pu, Pv, Pz, Pt] at hdd
  simp only [map_mul, Pb, Pc, Pd, Pu, Pv, Bool.false_eq_true, ↓reduceIte] at hbc hdb
  have hck : ck = false := by
    cases ck
    · rfl
    · cases i <;> cases ci <;> cases cj
      all_goals
        simp -failIfUnchanged only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
          pow_two, parrottCommutator, inv_one, mul_inv_rev, inv_inv, sqinv h.z_sq,
          sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq,
          sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one,
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
          tail cc, cc] at hbc
        simp -failIfUnchanged only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right,
          left_eq_mul, right_eq_mul, hz, Ne.symm hz] at hbc
  subst ck
  have hdjk : dj ≠ dk := by
    intro he
    subst dk
    cases i <;> cases di <;> cases dj
    all_goals
      simp -failIfUnchanged only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
        pow_two, parrottCommutator, inv_one, mul_inv_rev, inv_inv, sqinv h.z_sq,
        sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq,
        sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one,
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
        tail cc, cc] at hdb
      simp -failIfUnchanged only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right,
        left_eq_mul, right_eq_mul, hz, Ne.symm hz] at hdb
  cases dj <;> cases dk <;> simp -failIfUnchanged only [ne_self_iff_false] at hdjk
  all_goals
    cases i <;> cases ci <;> cases cj <;> cases di
    all_goals
      simp -failIfUnchanged only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
        pow_two, parrottCommutator, inv_one, mul_inv_rev, inv_inv, sqinv h.z_sq,
        sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq,
        sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one,
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
        tail cc, cc] at hdd
      simp -failIfUnchanged only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right,
        left_eq_mul, right_eq_mul, hz, Ne.symm hz] at hdd

private theorem right_conj {g k r : G}
    (hr : parrottCommutator g k = r) (hr2 : r^2=1) : g⁻¹*k*g=k*r := by
  have hswap := (parrottCommutator_eq_iff _ _ _).mp hr
  have hrr : r*r=1 := by simpa only [pow_two] using hr2
  have heq := congrArg (fun p : G => g⁻¹*p*r) hswap
  simpa only [mul_assoc, inv_mul_cancel_left, hrr, mul_one] using heq.symm

private theorem conj_of_commute {g k : G} (h : Commute g k) : g⁻¹*k*g=k := by
  rw [mul_assoc, h.symm.eq, inv_mul_cancel_left]

/-- Equation (17) excludes the t-factor in the b,x commutator. -/
public theorem bx_ne_mul_t_of_eq17
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hz : z ≠ 1) (hax : parrottCommutator a x = 1)
    (hyd : parrottCommutator (x^2*z) d = b*w)
    (hb : x⁻¹*b*x*(b*a)⁻¹ ∈ closure ({z,t,v,u,w} : Set G))
    (hc : x⁻¹*c*x*(c*(a*b*u*v)⁻¹)⁻¹ ∈ closure ({z,t,v,u,w} : Set G))
    (hd : x⁻¹*d*x*(d*(a*b*c*u*v)⁻¹)⁻¹ ∈ closure ({z,t,v,u,w} : Set G))
    (i : Bool) : parrottCommutator b x ≠ a*z^i.toNat*t := by
  intro hbx
  obtain ⟨_, ⟨ci,cj,ck,hc⟩, ⟨di,dj,dk,hd⟩⟩ :=
    h.outer_image_parameters hz hax hb hc hd
  let P : G ≃* G := MulAut.conj x⁻¹
  have Peq (s : G) : P s = x⁻¹*s*x := by simp [P]
  have Pz : P z = z := by
    rw [Peq]; exact conj_of_commute h.comm_zx.symm
  have Pt : P t = t := by
    rw [Peq]; exact conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt)
  have Pv : P v = v*t := by rw [Peq]; exact right_conj h.eq01_xv h.t_sq
  have Pu : P u = u*v := by rw [Peq]; exact right_conj h.eq01_xu h.v_sq
  have Pa : P a = a := by
    rw [Peq]; exact conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp hax).symm
  have Pb : P b = (b*a)*z^i.toNat*t := by
    rw [Peq]
    calc
      _ = b*parrottCommutator b x := by rw [parrottCommutator]; group
      _ = _ := by rw [hbx]; group
  have P2 : P (P d) = (x^2*z)⁻¹*d*(x^2*z) := by
    rw [Peq, Peq]
    calc
      _ = (x^2)⁻¹*d*x^2 := by rw [pow_two, mul_inv_rev]; group
      _ = (x^2)⁻¹*(z⁻¹*d*z)*x^2 := by rw [conj_of_commute h.comm_zd]
      _ = (z*x^2)⁻¹*d*(z*x^2) := by rw [mul_inv_rev]; group
      _ = _ := by rw [(h.comm_zx.pow_right 2).eq]
  have P2' : P (P d) = (b*w)*d := by
    rw [P2]
    calc
      _ = parrottCommutator (x^2*z) d * d := by
        rw [parrottCommutator, sqinv h.d_sq]
        have dd : d*d=1 := by simpa only [pow_two] using h.d_sq
        simp only [mul_assoc, dd, mul_one]
      _ = _ := by rw [hyd]
  have P2d : P (P d) = d*(b*w)⁻¹ := by
    calc
      _ = (P (P d))⁻¹ := by rw [← map_inv, ← map_inv, sqinv h.d_sq]
      _ = ((b*w)*d)⁻¹ := by rw [P2']
      _ = _ := by rw [mul_inv_rev, sqinv h.d_sq]
  exact exclude_t_parameter h hz i ci cj ck di dj dk P Pz Pt Pv Pu Pa Pb
    (by simpa only [Peq] using hc) (by simpa only [Peq] using hd) P2d

/-- Multiplication of x by u preserves the already normalized equation (17). -/
public theorem adjust_xu_eq17
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hyd : parrottCommutator (x^2*z) d = b*w) :
    parrottCommutator ((x*u)^2*z) d = b*w := by
  have dv : d*v=v*d := by
    have dd : d*d=1 := by simpa only [pow_two] using h.d_sq
    calc
      d*v = v⁻¹*d := by
        rw [← h.eq03_db]
        simp only [parrottCommutator, mul_inv_rev, inv_inv, sqinv h.d_sq]
        group
        simp only [mul_assoc, dd, one_mul, mul_one]
      _ = v*d := by rw [sqinv h.v_sq]
  have vb : Commute v b := (h.eq03_b ▸ Commute.self_pow b 2).symm
  have vr := vb.mul_right h.comm_vw
  rw [h.adjust_xu_square]
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have he := (parrottCommutator_eq_iff _ _ _).mp hyd
  calc
    (x^2*z*v)*d = ((x^2*z)*d)*v := by rw [mul_assoc, ← dv, ← mul_assoc]
    _ = (d*(x^2*z)*(b*w))*v := by rw [he]
    _ = d*(x^2*z*v)*(b*w) := by rw [mul_assoc (d*(x^2*z)), ← vr.eq]; group

end Tits.ParrottSylowSeedRelations
