module

public import Theory.SpecificGroups.Tits.RecognitionSylowSeed
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Outer images modulo the elementary centralizer

The action of x on z,t,v,u,w determines the images of b,c,d modulo the
centralizer of their generated subgroup. Compare right conjugation by the
images with right conjugation by the expected representatives, on the
transformed basis z,t,vt,uv,wu. Their discrepancies centralize that basis.
For a self-centralizing elementary subgroup this gives actual coset bounds,
without any chosen three-subgroup or extra outer commutator equations.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–680, especially the coset observations following (10).
-/

open Subgroup Tits
namespace Tits.ParrottSylowSeedRelations
variable {G : Type*} [Group G] {z t v u w a b c d x : G}
private theorem sqinv {p : G} (hp : p^2=1) : p⁻¹=p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem reverse {p q r : G} (h : p*q=q*p*r) : q*p=p*q*r⁻¹ := by rw [h]; group
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
private theorem representative_actions (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    (b*a)⁻¹*z*(b*a) = z ∧
    (b*a)⁻¹*t*(b*a) = t ∧
    (b*a)⁻¹*(v*t)*(b*a) = v*t ∧
    (b*a)⁻¹*(u*v)*(b*a) = u*v*z ∧
    (b*a)⁻¹*(w*u)*(b*a) = w*u ∧
    (c*(a*b*u*v)⁻¹)⁻¹*z*(c*(a*b*u*v)⁻¹) = z ∧
    (c*(a*b*u*v)⁻¹)⁻¹*t*(c*(a*b*u*v)⁻¹) = t ∧
    (c*(a*b*u*v)⁻¹)⁻¹*(v*t)*(c*(a*b*u*v)⁻¹) = v*t*z ∧
    (c*(a*b*u*v)⁻¹)⁻¹*(u*v)*(c*(a*b*u*v)⁻¹) = u*v ∧
    (c*(a*b*u*v)⁻¹)⁻¹*(w*u)*(c*(a*b*u*v)⁻¹) = w*u ∧
    (d*(a*b*c*u*v)⁻¹)⁻¹*z*(d*(a*b*c*u*v)⁻¹) = z ∧
    (d*(a*b*c*u*v)⁻¹)⁻¹*t*(d*(a*b*c*u*v)⁻¹) = t*z ∧
    (d*(a*b*c*u*v)⁻¹)⁻¹*(v*t)*(d*(a*b*c*u*v)⁻¹) = v*t ∧
    (d*(a*b*c*u*v)⁻¹)⁻¹*(u*v)*(d*(a*b*c*u*v)⁻¹) = u*v ∧
    (d*(a*b*c*u*v)⁻¹)⁻¹*(w*u)*(d*(a*b*c*u*v)⁻¹) = w*u := by
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
    simp only [← mul_assoc, bb, vv]
  have cinv : c⁻¹=c*w*u := by
    apply inv_eq_of_mul_eq_one_right
    simp only [mul_assoc, tail cc, cc, tail uw, uw, tail uu, uu, tail ww, ww, mul_one, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [mul_inv_rev, inv_inv, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
      sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc]
    simp only [mul_assoc, one_mul, mul_one,
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
      tail cc, cc]

private theorem outer_derived_closure :
    closure ({z,t,v*t,u*v,w*u} : Set G) = closure ({z,t,v,u,w} : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hz : z ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have ht : t ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have hv : v ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have hu : u ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have hw : w ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hz
    · exact ht
    · exact mul_mem hv ht
    · exact mul_mem hu hv
    · exact mul_mem hw hu
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    let L := closure ({z,t,v*t,u*v,w*u} : Set G)
    have hz : z ∈ L := subset_closure (by simp [L])
    have ht : t ∈ L := subset_closure (by simp [L])
    have hv : v ∈ L := (L.mul_mem_cancel_right ht).mp (subset_closure (by simp [L]))
    have hu : u ∈ L := (L.mul_mem_cancel_right hv).mp (subset_closure (by simp [L]))
    have hw : w ∈ L := (L.mul_mem_cancel_right hu).mp (subset_closure (by simp [L]))
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem discrepancy_commute (P : G ≃* G) {g r s : G}
    (h : r⁻¹ * P s * r = P (g⁻¹*s*g)) : Commute (P s) (P g*r⁻¹) := by
  simp only [map_mul, map_inv] at h
  have he := congrArg (fun q => P g * q * r⁻¹) h
  change P s * (P g*r⁻¹) = (P g*r⁻¹) * P s
  simpa only [mul_assoc, mul_inv_cancel_right, mul_inv_cancel_left, mul_inv_cancel, mul_one] using he.symm

private theorem right_conj {g k r : G}
    (hr : parrottCommutator g k = r) (hr2 : r^2=1) : g⁻¹*k*g=k*r := by
  have hswap := (parrottCommutator_eq_iff _ _ _).mp hr
  have hrr : r*r=1 := by simpa only [pow_two] using hr2
  have heq := congrArg (fun p : G => g⁻¹*p*r) hswap
  simpa only [mul_assoc, inv_mul_cancel_left, hrr, mul_one] using heq.symm

private theorem conj_of_commute {g k : G} (h : Commute g k) : g⁻¹*k*g=k := by
  rw [mul_assoc, h.symm.eq, inv_mul_cancel_left]

/-- The prescribed outer action determines the three core images modulo the
centralizer of the elementary derived subgroup. -/
public theorem outer_discrepancies_centralize
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    x⁻¹*b*x*(b*a)⁻¹ ∈ centralizer (closure ({z,t,v,u,w} : Set G) : Set G) ∧
    x⁻¹*c*x*(c*(a*b*u*v)⁻¹)⁻¹ ∈ centralizer (closure ({z,t,v,u,w} : Set G) : Set G) ∧
    x⁻¹*d*x*(d*(a*b*c*u*v)⁻¹)⁻¹ ∈ centralizer (closure ({z,t,v,u,w} : Set G) : Set G) := by
  let P : G ≃* G := MulAut.conj x⁻¹
  have hz : P z = z := by simpa [P] using conj_of_commute h.comm_zx.symm
  have ht : P t = t := by simpa [P] using conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt)
  have hv : P v = v*t := by simpa [P] using right_conj h.eq01_xv h.t_sq
  have hu : P u = u*v := by simpa [P] using right_conj h.eq01_xu h.v_sq
  have hw : P w = w*u := by simpa [P] using right_conj h.eq01_xw h.u_sq
  have bv : Commute b v := by rw [← h.eq03_b]; exact Commute.self_pow b 2
  have dv : Commute d v := by
    have dd : d*d=1 := by simpa only [pow_two] using h.d_sq
    change d*v=v*d
    calc
      d*v = v⁻¹*d := by
        rw [← h.eq03_db]
        simp only [parrottCommutator, mul_inv_rev, inv_inv, sqinv h.d_sq]
        group
        simp only [mul_assoc, dd, one_mul, mul_one]
      _ = v*d := by rw [sqinv h.v_sq]
  have cbz := conj_of_commute h.comm_zb.symm
  have cbt := conj_of_commute h.comm_bt
  have cbv := conj_of_commute bv
  have cbu := right_conj h.eq02_bu h.z_sq
  have cbw := conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq02_bw)
  have ccz := conj_of_commute h.comm_zc.symm
  have cct := conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq10_ct)
  have ccv := right_conj h.eq10_cv h.z_sq
  have ccu := conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq09_cu)
  have ccw := conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq09_cw)
  have cdz := conj_of_commute h.comm_zd.symm
  have cdt := right_conj h.eq03_dt h.z_sq
  have cdv := conj_of_commute dv
  have cdu := conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq08_du)
  have cdw := conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq07_dw)
  obtain ⟨hbz,hbt,hbv,hbu,hbw,hcz,hct,hcv,hcu,hcw,hdz,hdt,hdv,hdu,hdw⟩ :=
    representative_actions h
  have step (g r : G)
      (hs : ∀ q ∈ ({z,t,v,u,w} : Set G), r⁻¹*P q*r = P (g⁻¹*q*g)) :
      P g*r⁻¹ ∈ centralizer (closure ({z,t,v,u,w} : Set G) : Set G) := by
    rw [← outer_derived_closure, centralizer_closure]
    apply mem_centralizer_iff.mpr
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · simpa only [hz] using (discrepancy_commute P (hs q (by simp))).eq
    · simpa only [ht] using (discrepancy_commute P (hs q (by simp))).eq
    · simpa only [hv] using (discrepancy_commute P (hs v (by simp))).eq
    · simpa only [hu] using (discrepancy_commute P (hs u (by simp))).eq
    · simpa only [hw] using (discrepancy_commute P (hs w (by simp))).eq
  suffices P b*(b*a)⁻¹ ∈ centralizer (closure ({z,t,v,u,w} : Set G) : Set G) ∧
      P c*(c*(a*b*u*v)⁻¹)⁻¹ ∈ centralizer (closure ({z,t,v,u,w} : Set G) : Set G) ∧
      P d*(d*(a*b*c*u*v)⁻¹)⁻¹ ∈ centralizer (closure ({z,t,v,u,w} : Set G) : Set G) by
    simpa [P] using this
  refine ⟨step _ _ ?_, step _ _ ?_, step _ _ ?_⟩
  all_goals
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [cbz,cbt,cbv,cbu,cbw,ccz,cct,ccv,ccu,ccw,cdz,cdt,cdv,cdu,cdw,
        map_mul,hz,ht,hv,hu,hw]
      assumption

end Tits.ParrottSylowSeedRelations
