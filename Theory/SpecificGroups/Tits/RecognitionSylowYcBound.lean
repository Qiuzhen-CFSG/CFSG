module
public import Theory.SpecificGroups.Tits.RecognitionSylowSeed
/-!
# The square action on Parrott's c coordinate

Conjugating the relation [b,c]=uv by x, with [b,x]=a, eliminates the
uv-coordinate in the elementary error of the c-image. Applying the same
conjugation twice then gives [x²z,c]=atz: both remaining central parameters
cancel. These are word identities for an arbitrary group with the seed
relations, without a completed frame or a global conjugacy-class choice.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.680, the calculation preceding equation (19). The collection uses
the same right-conjugation convention as RecognitionSylowLastParameters.
-/

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
private theorem pc_from_conj (p q : G) :
    parrottCommutator p q = (q⁻¹*(p⁻¹*q*p))⁻¹ := by
  simp only [parrottCommutator, mul_inv_rev, inv_inv]
  group
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000 in
/-- Once (16) and (18) hold, the c-image parameters force the exact square
commutator. In particular, no global class assumption on x²z is needed. -/
public theorem yc_of_image_parameters
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hz : z ≠ 1) (hax : parrottCommutator a x = 1)
    (hbx : parrottCommutator b x = a)
    (ci cj ck : Bool)
    (hc : x⁻¹*c*x = (c*(a*b*u*v)⁻¹)*z^ci.toNat*t^cj.toNat*(u*v)^ck.toNat) :
    parrottCommutator (x^2*z) c = a*t*z := by
  let P : G ≃* G := MulAut.conj x⁻¹
  have pe (g : G) : P g = x⁻¹*g*x := by simp [P]
  have pz : P z = z := by rw [pe, mul_assoc, h.comm_zx.eq, inv_mul_cancel_left]
  have pt : P t = t := by rw [pe]; simpa using pc_conj_rev h.eq01_xt
  have pv : P v = v*t := by rw [pe]; simpa only [sqinv h.t_sq] using pc_conj_rev h.eq01_xv
  have pu : P u = u*v := by rw [pe]; simpa only [sqinv h.v_sq] using pc_conj_rev h.eq01_xu
  have pa : P a = a := by rw [pe]; simpa using pc_conj hax
  have pb : P b = b*a := by rw [pe]; exact pc_conj hbx
  have pc : P c = _ := (pe c).trans hc
  have map_pc (p q : G) : P (parrottCommutator p q) = parrottCommutator (P p) (P q) := by
    simp only [parrottCommutator, map_mul, map_inv]
  have hbc := congrArg P h.eq15_bc
  have p2 (g : G) (hg : Commute z g) : P (P g) = (x^2*z)⁻¹*g*(x^2*z) := by
    rw [pe, pe]
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
  simp only [map_pc, map_mul, map_inv, map_pow, map_one,
    pz, pt, pv, pu, pa, pb, pc, Bool.false_eq_true, ↓reduceIte] at hbc

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

  have tb := h.comm_bt.symm.eq

  have wb := ((parrottCommutator_eq_one_iff _ _).mp h.eq02_bw).symm.eq

  have uc := ((parrottCommutator_eq_one_iff _ _).mp h.eq09_cu).symm.eq
  have wc := ((parrottCommutator_eq_one_iff _ _).mp h.eq09_cw).symm.eq
  have tc := ((parrottCommutator_eq_one_iff _ _).mp h.eq10_ct).symm.eq

  have wa := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_aw)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at wa
  have ub := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_bu)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ub

  have ab := ((parrottCommutator_eq_iff _ _ _).mp h.eq05_ab)
  have vc := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq10_cv)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at vc

  have ac := ((parrottCommutator_eq_iff _ _ _).mp h.eq12_ac)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ac

  have bc := ((parrottCommutator_eq_iff _ _ _).mp h.eq15_bc)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq, sqinv h.t_sq,
    sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bc

  have vb := bv.symm
  have zz : z*z=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.z_sq
  have tt : t*t=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.t_sq
  have vv : v*v=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.v_sq
  have uu : u*u=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.u_sq
  have ww : w*w=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.w_sq
  have aa : a*a=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.a_sq

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
        sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, binv, cinv, mul_assoc,
        one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu,
        tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va,
        tail ua, ua, tail zb, zb, tail zc, zc, tail tb, tb,
        tail wb, wb, tail uc, uc, tail wc, wc, tail tc, tc,
        tail wa, wa, tail ub, ub, tail ab, ab,
        tail vc, vc, tail ac, ac, tail bc, bc, tail vb, vb,
        tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa,
        tail bb, bb, tail cc, cc] at hbc
    all_goals
      simp only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right, left_eq_mul,
        right_eq_mul, hz, Ne.symm hz] at hbc
  subst ck
  rw [pc_from_conj, ← p2 c h.comm_zc]
  simp only [pc, map_mul, map_inv, map_pow, pz, pt, pv, pu, pa, pb, pc]
  cases ci <;> cases cj
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
      pow_two, parrottCommutator, mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
      sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, binv, cinv, mul_assoc, one_mul, mul_one,
      tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw,
      tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va, tail ua, ua,
      tail zb, zb, tail zc, zc, tail tb, tb, tail wb, wb,
      tail uc, uc, tail wc, wc, tail tc, tc,
      tail wa, wa, tail ub, ub, tail ab, ab, tail vc, vc,
      tail ac, ac, tail bc, bc, tail vb, vb, tail zz, zz,
      tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail bb, bb,
      tail cc, cc]
end Tits.ParrottSylowSeedRelations
