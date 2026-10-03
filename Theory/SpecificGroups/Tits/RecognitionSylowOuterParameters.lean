module

public import Theory.SpecificGroups.Tits.RecognitionSylowSeed
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Parameters of the outer images in Parrott's Sylow calculation

The discrepancies of the three outer images lie in the elementary closure
of z,t,v,u,w. Every element of that closure has five Boolean coordinates.
Conjugating the a-commutator relations by x excludes the w coordinate;
comparing squares then imposes one linear condition on the remaining bits.
Word collection also converts the input left errors to the stated right errors.
Only the seed relations through (15) and the hypothesis [a,x] = 1 are used.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–680.
-/

open Subgroup Tits
namespace Tits.ParrottSylowSeedRelations
variable {G : Type*} [Group G] {z t v u w a b c d x : G}
private theorem sqinv {p : G} (hp : p^2=1) : p⁻¹=p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem reverse {p q r : G} (h : p*q=q*p*r) : q*p=p*q*r⁻¹ := by rw [h]; group
set_option linter.unusedSimpArgs false
/-- Boolean coordinates do not require independence of the five generators. -/
private theorem elementary_coordinates
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    {e : G} (he : e ∈ closure ({z,t,v,u,w} : Set G)) :
    ∃ i j k l m : Bool, e = z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat := by
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
  have zz : z*z=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.z_sq
  have tt : t*t=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.t_sq
  have vv : v*v=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.v_sq
  have uu : u*u=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.u_sq
  have ww : w*w=1 := by simpa only [pow_two, Bool.false_eq_true, ↓reduceIte] using h.w_sq
  let P := fun e : G => ∃ i j k l m : Bool,
    e = z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat
  have step (g : G) (hg : g ∈ ({z,t,v,u,w} : Set G)) (e : G) (he : P e) : P (g*e) := by
    obtain ⟨i,j,k,l,m,rfl⟩ := he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · refine ⟨!i,j,k,l,m, ?_⟩
      cases i <;> cases j <;> cases k <;> cases l <;> cases m <;>
        simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true, pow_zero, pow_one,
          mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv,
          tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail zz, zz, tail tt, tt, tail
          vv, vv, tail uu, uu, tail ww, ww]
    · refine ⟨i,!j,k,l,m, ?_⟩
      cases i <;> cases j <;> cases k <;> cases l <;> cases m <;>
        simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true, pow_zero, pow_one,
          mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv,
          tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail zz, zz, tail tt, tt, tail
          vv, vv, tail uu, uu, tail ww, ww]
    · refine ⟨i,j,!k,l,m, ?_⟩
      cases i <;> cases j <;> cases k <;> cases l <;> cases m <;>
        simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true, pow_zero, pow_one,
          mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv,
          tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail zz, zz, tail tt, tt, tail
          vv, vv, tail uu, uu, tail ww, ww]
    · refine ⟨i,j,k,!l,m, ?_⟩
      cases i <;> cases j <;> cases k <;> cases l <;> cases m <;>
        simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true, pow_zero, pow_one,
          mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv,
          tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail zz, zz, tail tt, tt, tail
          vv, vv, tail uu, uu, tail ww, ww]
    · refine ⟨i,j,k,l,!m, ?_⟩
      cases i <;> cases j <;> cases k <;> cases l <;> cases m <;>
        simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true, pow_zero, pow_one,
          mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv,
          tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail zz, zz, tail tt, tt, tail
          vv, vv, tail uu, uu, tail ww, ww]
  apply closure_induction_left (p := fun e _ => P e) ?_ ?_ ?_ he
  · exact ⟨false,false,false,false,false, by simp⟩
  · intro g hg e _ he
    exact step g hg e he
  · intro g hg e _ he
    have hg2 : g⁻¹ = g := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact sqinv h.z_sq
      · exact sqinv h.t_sq
      · exact sqinv h.v_sq
      · exact sqinv h.u_sq
      · exact sqinv h.w_sq
    rw [hg2]
    exact step g hg e he
set_option maxHeartbeats 1200000 in
private theorem collect_b_parameters
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) (hz : z ≠ 1) :
    (∀ i j k l m : Bool,
      a*((z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(b*a)) =
        ((z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(b*a))*a*(t) →
      ((z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(b*a))^2 = v*t →
      ∃ p q r : Bool, (z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(b*a) =
        (b*a)*z^p.toNat*t^q.toNat*v^r.toNat) := by
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
  intro i j k l m ha hs
  refine ⟨i,j,k,?_⟩
  cases i <;> cases j <;> cases k <;> cases l <;> cases m
  all_goals
    simp -failIfUnchanged only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, pow_two,
      mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv
      h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu,
      zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail
      za, za, tail ta, ta, tail va, va, tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx,
      tail tb, tb, tail tx, tx, tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc,
      tc, tail vx, vx, tail ux, ux, tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail
      ab, ab, tail vc, vc, tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb,
      tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb,
      bb, tail cc, cc] at ha
  all_goals
    simp -failIfUnchanged only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right,
      left_eq_mul, right_eq_mul, hz, Ne.symm hz] at ha
  all_goals
    simp -failIfUnchanged only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, pow_two,
      mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv
      h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu,
      zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail
      za, za, tail ta, ta, tail va, va, tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx,
      tail tb, tb, tail tx, tx, tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc,
      tc, tail vx, vx, tail ux, ux, tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail
      ab, ab, tail vc, vc, tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb,
      tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb,
      bb, tail cc, cc] at hs
  all_goals
    simp -failIfUnchanged only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right,
      left_eq_mul, right_eq_mul, hz, Ne.symm hz] at hs
  all_goals
    simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, mul_inv_rev, inv_inv, sqinv h.z_sq,
      sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv,
      mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail
      tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va,
      tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx, tail wb,
      wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx, tail ux, ux, tail
      wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc, tail ad, ad,
      tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz, tail tt, tt, tail vv,
      vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb, tail cc, cc]

set_option maxHeartbeats 1200000 in
private theorem collect_c_parameters
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) (hz : z ≠ 1) :
    (∀ i j k l m : Bool,
      a*((z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(c*(a*b*u*v)⁻¹)) =
        ((z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(c*(a*b*u*v)⁻¹))*a*(v) →
      ((z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(c*(a*b*u*v)⁻¹))^2 = w*v →
      ∃ p q r : Bool, (z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(c*(a*b*u*v)⁻¹) =
        (c*(a*b*u*v)⁻¹)*z^p.toNat*t^q.toNat*(u*v)^r.toNat) := by
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
  intro i j k l m ha hs
  refine ⟨i,j,k,?_⟩
  cases i <;> cases j <;> cases k <;> cases l <;> cases m
  all_goals
    simp -failIfUnchanged only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, pow_two,
      mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv
      h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu,
      zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail
      za, za, tail ta, ta, tail va, va, tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx,
      tail tb, tb, tail tx, tx, tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc,
      tc, tail vx, vx, tail ux, ux, tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail
      ab, ab, tail vc, vc, tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb,
      tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb,
      bb, tail cc, cc] at ha
  all_goals
    simp -failIfUnchanged only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right,
      left_eq_mul, right_eq_mul, hz, Ne.symm hz] at ha
  all_goals
    simp -failIfUnchanged only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, pow_two,
      mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv
      h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu,
      zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail
      za, za, tail ta, ta, tail va, va, tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx,
      tail tb, tb, tail tx, tx, tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc,
      tc, tail vx, vx, tail ux, ux, tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail
      ab, ab, tail vc, vc, tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb,
      tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb,
      bb, tail cc, cc] at hs
  all_goals
    simp -failIfUnchanged only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right,
      left_eq_mul, right_eq_mul, hz, Ne.symm hz] at hs
  all_goals
    simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, mul_inv_rev, inv_inv, sqinv h.z_sq,
      sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv,
      mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail
      tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va,
      tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx, tail wb,
      wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx, tail ux, ux, tail
      wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc, tail ad, ad,
      tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz, tail tt, tt, tail vv,
      vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb, tail cc, cc]

set_option maxHeartbeats 1200000 in
private theorem collect_d_parameters
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) (hz : z ≠ 1) :
    (∀ i j k l m : Bool,
      a*((z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(d*(a*b*c*u*v)⁻¹)) =
        ((z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(d*(a*b*c*u*v)⁻¹))*a*(u*v) →
      ((z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(d*(a*b*c*u*v)⁻¹))^2 = 1 →
      ∃ p q r : Bool, (z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*(d*(a*b*c*u*v)⁻¹) =
        (d*(a*b*c*u*v)⁻¹)*z^p.toNat*(t*u)^q.toNat*(v*u)^r.toNat) := by
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
  intro i j k l m ha hs
  refine ⟨i,j,k,?_⟩
  cases i <;> cases j <;> cases k <;> cases l <;> cases m
  all_goals
    simp -failIfUnchanged only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, pow_two,
      mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv
      h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu,
      zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail
      za, za, tail ta, ta, tail va, va, tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx,
      tail tb, tb, tail tx, tx, tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc,
      tc, tail vx, vx, tail ux, ux, tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail
      ab, ab, tail vc, vc, tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb,
      tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb,
      bb, tail cc, cc] at ha
  all_goals
    simp -failIfUnchanged only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right,
      left_eq_mul, right_eq_mul, hz, Ne.symm hz] at ha
  all_goals
    simp -failIfUnchanged only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, pow_two,
      mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv
      h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu,
      zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail
      za, za, tail ta, ta, tail va, va, tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx,
      tail tb, tb, tail tx, tx, tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc,
      tc, tail vx, vx, tail ux, ux, tail wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail
      ab, ab, tail vc, vc, tail ad, ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb,
      tail zz, zz, tail tt, tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb,
      bb, tail cc, cc] at hs
  all_goals
    simp -failIfUnchanged only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right,
      left_eq_mul, right_eq_mul, hz, Ne.symm hz] at hs
  all_goals
    simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, mul_inv_rev, inv_inv, sqinv h.z_sq,
      sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv,
      mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu, zu, tail zw, zw, tail tv, tv, tail
      tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw, uw, tail za, za, tail ta, ta, tail va, va,
      tail ua, ua, tail zb, zb, tail zc, zc, tail zd, zd, tail zx, zx, tail tb, tb, tail tx, tx, tail wb,
      wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc, tc, tail vx, vx, tail ux, ux, tail
      wx, wx, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc, tail ad, ad,
      tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz, tail tt, tt, tail vv,
      vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb, tail cc, cc]
private theorem right_conj {g k r : G}
    (hr : parrottCommutator g k = r) (hr2 : r^2=1) : g⁻¹*k*g=k*r := by
  have hswap := (parrottCommutator_eq_iff _ _ _).mp hr
  have hrr : r*r=1 := by simpa only [pow_two] using hr2
  have heq := congrArg (fun p : G => g⁻¹*p*r) hswap
  simpa only [mul_assoc, inv_mul_cancel_left, hrr, mul_one] using heq.symm

private theorem conj_of_commute {g k : G} (h : Commute g k) : g⁻¹*k*g=k := by
  rw [mul_assoc, h.symm.eq, inv_mul_cancel_left]

private theorem conjugated_constraints
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hax : parrottCommutator a x = 1) :
    (a*(x⁻¹*b*x) = (x⁻¹*b*x)*a*t ∧ (x⁻¹*b*x)^2 = v*t) ∧
    (a*(x⁻¹*c*x) = (x⁻¹*c*x)*a*v ∧ (x⁻¹*c*x)^2 = w*v) ∧
    (a*(x⁻¹*d*x) = (x⁻¹*d*x)*a*(u*v) ∧ (x⁻¹*d*x)^2 = 1) := by
  let P : G ≃* G := MulAut.conj x⁻¹
  have ht : P t = t := by
    simpa [P] using conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt)
  have hv : P v = v*t := by simpa [P] using right_conj h.eq01_xv h.t_sq
  have hu : P u = u*v := by simpa [P] using right_conj h.eq01_xu h.v_sq
  have hw : P w = w*u := by simpa [P] using right_conj h.eq01_xw h.u_sq
  have ha : P a = a := by
    simpa [P] using conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp hax).symm
  have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
  have uu : u*u=1 := by simpa only [pow_two] using h.u_sq
  have hab := congrArg P ((parrottCommutator_eq_iff _ _ _).mp h.eq05_ab)
  have hac := congrArg P ((parrottCommutator_eq_iff _ _ _).mp h.eq12_ac)
  have had := congrArg P ((parrottCommutator_eq_iff _ _ _).mp h.eq11_ad)
  have hbs := congrArg P h.eq03_b
  have hcs := congrArg P h.eq13
  have hds := congrArg P h.d_sq
  simp only [Bool.false_eq_true, ↓reduceIte, map_mul, map_pow, map_one,
    ha, ht, hv, hu, hw, mul_assoc, tail tt, tt, tail uu, uu, mul_one, one_mul] at hab hac had hbs hcs hds
  simpa only [P, MulAut.conj_apply, inv_inv, mul_assoc] using
    And.intro (And.intro hab hbs) (And.intro (And.intro hac hcs) (And.intro had hds))

/-- The square and a-commutator relations narrow the three outer images to
exactly the indicated right-error coordinates. -/
public theorem outer_image_parameters
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hz : z ≠ 1) (hax : parrottCommutator a x = 1)
    (hb : x⁻¹*b*x*(b*a)⁻¹ ∈ closure ({z,t,v,u,w} : Set G))
    (hc : x⁻¹*c*x*(c*(a*b*u*v)⁻¹)⁻¹ ∈ closure ({z,t,v,u,w} : Set G))
    (hd : x⁻¹*d*x*(d*(a*b*c*u*v)⁻¹)⁻¹ ∈ closure ({z,t,v,u,w} : Set G)) :
    (∃ i j k : Bool, x⁻¹*b*x = (b*a)*z^i.toNat*t^j.toNat*v^k.toNat) ∧
    (∃ i j k : Bool, x⁻¹*c*x = (c*(a*b*u*v)⁻¹)*z^i.toNat*t^j.toNat*(u*v)^k.toNat) ∧
    (∃ i j k : Bool, x⁻¹*d*x = (d*(a*b*c*u*v)⁻¹)*z^i.toNat*(t*u)^j.toNat*(v*u)^k.toNat) := by
  have coordinates (y r : G) (hy : y*r⁻¹ ∈ closure ({z,t,v,u,w} : Set G)) :
      ∃ i j k l m : Bool, y = (z^i.toNat*t^j.toNat*v^k.toNat*u^l.toNat*w^m.toNat)*r := by
    obtain ⟨i,j,k,l,m,he⟩ := elementary_coordinates h hy
    refine ⟨i,j,k,l,m, ?_⟩
    rw [← he, inv_mul_cancel_right]
  obtain ⟨⟨hab,hbs⟩,⟨hac,hcs⟩,⟨had,hds⟩⟩ := conjugated_constraints h hax
  have cb := collect_b_parameters h hz
  have cc := collect_c_parameters h hz
  have cd := collect_d_parameters h hz
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨i,j,k,l,m,he⟩ := coordinates _ _ hb
    rw [he] at hab hbs ⊢
    exact cb i j k l m hab hbs
  · obtain ⟨i,j,k,l,m,he⟩ := coordinates _ _ hc
    rw [he] at hac hcs ⊢
    exact cc i j k l m hac hcs
  · obtain ⟨i,j,k,l,m,he⟩ := coordinates _ _ hd
    rw [he] at had hds ⊢
    exact cd i j k l m had hds

end Tits.ParrottSylowSeedRelations
