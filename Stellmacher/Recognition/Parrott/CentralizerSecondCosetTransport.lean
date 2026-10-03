module

public import Stellmacher.Recognition.Parrott.CentralizerCompatibleParameters

/-!
# Transporting the second centralizer action coset

For compatible parameters (true,true,false,false), replace
b,c,d,x,y by bz,ctz,dv,xv,yt, respectively, and retain a,u,w,r.
Collecting with the supplied Sylow relations verifies every relation of the
new frame and the four unprimed action equations (23). The corrected image
of c is cdawt, with no u factor.

The words b², [a,b], and [c,v] recover v,t,z in either core generating set,
so the change preserves the actual core and Sylow subgroup. The elementary
bases are unchanged. Finally, yt is the conjugate of y by u, and u commutes
with r, which transports the fifth-power relation. Everything is proved
from the supplied involution frame; no global existence or recognition
hypothesis is used.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–681, especially the two a-image alternatives preceding (23).
-/

namespace Stellmacher.Recognition

private def act {G : Type*} [Group G] (g : G) : G →* G where
  toFun j := g⁻¹ * j * g
  map_one' := by simp
  map_mul' j k := by simp [mul_assoc]

private theorem act_mul {G : Type*} [Group G] (g h j : G) :
    act (g * h) j = act h (act g j) := by simp [act, mul_assoc]

private theorem act_comm {G : Type*} [Group G] {g j : G} (h : Commute j g) :
    act g j = j := by
  change g⁻¹ * j * g = j
  rw [mul_assoc, h.eq, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem act_of_commutator {G : Type*} [Group G] {g j k : G}
    (h : Tits.parrottCommutator j g = k) : act g j = j * k := by
  have h := (Tits.parrottCommutator_eq_iff _ _ _).mp h
  change g⁻¹ * j * g = j * k
  rw [mul_assoc, h]
  group

private theorem act_of_reverse_commutator {G : Type*} [Group G] {g j k : G}
    (h : Tits.parrottCommutator g j = k) : act g j = j * k⁻¹ := by
  have h := (Tits.parrottCommutator_eq_iff _ _ _).mp h
  apply mul_right_cancel (b := k)
  change g⁻¹ * j * g * k = j * k⁻¹ * k
  calc
    _ = g⁻¹ * (j * g * k) := by group
    _ = g⁻¹ * (g * j) := by rw [← h]
    _ = _ := by group

private theorem tail {G : Type*} [Group G] {a b c : G} (h : a * b = c) (k : G) :
    a * (b * k) = c * k := by rw [← mul_assoc, h]

private theorem sqinv {G : Type*} [Group G] {a : G} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

private theorem revswap {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) : b * a = a * b * c⁻¹ := by rw [h]; group

variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
  {n : ParrottNormalizerFusionData e}

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-- Collection in the order x,y,d,c,b,a,w,u,v,t,z verifies the changed words. -/
private theorem transported_relations (f : ParrottCentralizerInvolutionData n)
    (hp : f.HasCompatibleActionParameters true true false false) :
    z ^ 2 = 1 ∧
    n.t ^ 2 = 1 ∧
    n.v ^ 2 = 1 ∧
    f.u ^ 2 = 1 ∧
    f.w ^ 2 = 1 ∧
    f.a ^ 2 = 1 ∧
    Commute z n.t ∧
    Commute z n.v ∧
    Commute z f.u ∧
    Commute z f.w ∧
    Commute n.t n.v ∧
    Commute n.t f.u ∧
    Commute n.t f.w ∧
    Commute n.v f.u ∧
    Commute n.v f.w ∧
    Commute f.u f.w ∧
    Commute f.a z ∧
    Commute f.a n.t ∧
    Commute f.a n.v ∧
    Commute f.a f.u ∧
    Commute z (f.b * z) ∧
    Commute z (f.c * n.t * z) ∧
    Commute z (f.d * n.v) ∧
    Commute z (f.x * n.v) ∧
    Commute z (f.y * n.t) ∧
    Commute (f.b * z) n.t ∧
    (f.y * n.t) ^ 2 = 1 ∧
    (f.d * n.v) ^ 2 = 1 ∧
    (f.x * n.v) ^ 4 = 1 ∧
    Tits.parrottCommutator (f.x * n.v) n.t = 1 ∧
    Tits.parrottCommutator (f.x * n.v) n.v = n.t ∧
    Tits.parrottCommutator (f.x * n.v) f.u = n.v ∧
    Tits.parrottCommutator (f.x * n.v) f.w = f.u ∧
    Tits.parrottCommutator (f.b * z) f.w = 1 ∧
    Tits.parrottCommutator f.a f.w = z ∧
    Tits.parrottCommutator (f.b * z) f.u = z ∧
    Tits.parrottCommutator (f.d * n.v) (f.b * z) = n.v ∧
    Tits.parrottCommutator (f.d * n.v) n.t = z ∧
    Tits.parrottCommutator f.a (f.b * z) = n.t ∧
    Tits.parrottCommutator (f.y * n.t) f.a = 1 ∧
    Tits.parrottCommutator (f.d * n.v) f.w = 1 ∧
    Tits.parrottCommutator (f.d * n.v) f.u = 1 ∧
    Tits.parrottCommutator (f.c * n.t * z) f.u = 1 ∧
    Tits.parrottCommutator (f.c * n.t * z) f.w = 1 ∧
    Tits.parrottCommutator (f.c * n.t * z) n.t = 1 ∧
    Tits.parrottCommutator (f.c * n.t * z) n.v = z ∧
    Tits.parrottCommutator f.a (f.d * n.v) = f.u ∧
    Tits.parrottCommutator f.a (f.c * n.t * z) = n.v * n.t ∧
    Tits.parrottCommutator (f.c * n.t * z) (f.d * n.v) = f.w * f.u ∧
    Tits.parrottCommutator (f.b * z) (f.c * n.t * z) = f.u * n.v ∧
    Tits.parrottCommutator f.a (f.x * n.v) = 1 ∧
    Tits.parrottCommutator (f.y * n.t) (f.d * n.v) = (f.b * z) * f.w ∧
    Tits.parrottCommutator (f.b * z) (f.x * n.v) = f.a ∧
    Tits.parrottCommutator (f.b * z) (f.y * n.t) = 1 ∧
    Tits.parrottCommutator (f.y * n.t) (f.c * n.t * z) = f.a * n.t * z ∧
    Tits.parrottCommutator (f.x * n.v) (f.c * n.t * z) = f.a * (f.b * z) * f.u * n.v ∧
    Tits.parrottCommutator (f.x * n.v) (f.d * n.v) = f.a * (f.b * z) * (f.c * n.t * z) * f.u * n.v ∧
    (f.b * z) ^ 2 = n.v ∧
    (f.x * n.v) ^ 2 = (f.y * n.t) * z ∧
    (f.c * n.t * z) ^ 2 = f.w * f.u ∧
    act f.u f.y = f.y * n.t ∧
    act f.r f.a = (f.d * n.v) * f.u ∧
    act f.r (f.d * n.v) = f.a * f.u ∧
    act f.r (f.c * n.t * z) = (f.c * n.t * z) * (f.d * n.v) * f.a * f.u ∧
    act f.r (f.b * z) = (f.d * n.v) * (f.c * n.t * z) * (f.b * z) * n.v * n.t := by
  -- Collection rules for the core, with the elementary tail ordered w,u,v,t,z.
  have sq_z : z * z = 1 := by simpa only [pow_two] using f.z_sq
  have sq_t : n.t * n.t = 1 := by simpa only [pow_two] using f.t_sq
  have sq_v : n.v * n.v = 1 := by simpa only [pow_two] using f.v_sq
  have sq_u : f.u * f.u = 1 := by simpa only [pow_two] using f.u_sq
  have sq_w : f.w * f.w = 1 := by simpa only [pow_two] using f.w_sq
  have sq_a : f.a * f.a = 1 := by simpa only [pow_two] using f.a_sq
  have sq_d : f.d * f.d = 1 := by simpa only [pow_two] using f.d_sq
  have sq_b : f.b * f.b = n.v := by simpa only [pow_two] using f.eq03_b
  have sq_c : f.c * f.c = f.w * f.u := by simpa only [pow_two] using f.eq13
  have dv : f.d * n.v = n.v * f.d := by
    calc
      f.d * n.v = n.v⁻¹ * f.d := by
        rw [← f.eq03_db]
        simp only [Tits.parrottCommutator, mul_inv_rev, inv_inv, sqinv f.d_sq]
        group
        simp only [mul_assoc, sq_d, one_mul, mul_one]
      _ = n.v * f.d := by rw [sqinv f.v_sq]
  have bv : Commute f.b n.v := by
    rw [← f.eq03_b]
    exact Commute.self_pow f.b 2
  have swap_zt := f.comm_zt.eq
  have swap_zv := f.comm_zv.eq
  have swap_zu := f.comm_zu.eq
  have swap_zw := f.comm_zw.eq
  have swap_tv := f.comm_tv.eq
  have swap_tu := f.comm_tu.eq
  have swap_tw := f.comm_tw.eq
  have swap_vu := f.comm_vu.eq
  have swap_vw := f.comm_vw.eq
  have swap_uw := f.comm_uw.eq
  have swap_az := f.comm_az.symm.eq
  have swap_at := f.comm_at.symm.eq
  have swap_av := f.comm_av.symm.eq
  have swap_au := f.comm_au.symm.eq
  have swap_zb := f.comm_zb.eq
  have swap_zc := f.comm_zc.eq
  have swap_zd := f.comm_zd.eq
  have swap_bt := f.comm_bt.symm.eq
  have swap_dv := dv.symm
  have swap_bv := bv.symm.eq
  have swap_bw := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_bw
  have swap_bw := revswap swap_bw
  simp only [inv_one, mul_one] at swap_bw
  have swap_aw := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_aw
  have swap_aw := revswap swap_aw
  simp only [sqinv f.z_sq] at swap_aw
  have swap_bu := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_bu
  have swap_bu := revswap swap_bu
  simp only [sqinv f.z_sq] at swap_bu
  have swap_db := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq03_db
  have swap_db := revswap swap_db
  simp only [sqinv f.v_sq] at swap_db
  have swap_dt := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq03_dt
  have swap_dt := revswap swap_dt
  simp only [sqinv f.z_sq] at swap_dt
  have swap_ab := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq05_ab
  have swap_dw := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq07_dw
  have swap_dw := revswap swap_dw
  simp only [inv_one, mul_one] at swap_dw
  have swap_du := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq08_du
  have swap_du := revswap swap_du
  simp only [inv_one, mul_one] at swap_du
  have swap_cu := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq09_cu
  have swap_cu := revswap swap_cu
  simp only [inv_one, mul_one] at swap_cu
  have swap_cw := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq09_cw
  have swap_cw := revswap swap_cw
  simp only [inv_one, mul_one] at swap_cw
  have swap_ct := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq10_ct
  have swap_ct := revswap swap_ct
  simp only [inv_one, mul_one] at swap_ct
  have swap_cv := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq10_cv
  have swap_cv := revswap swap_cv
  simp only [sqinv f.z_sq] at swap_cv
  have swap_ad := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq11_ad
  have swap_ac := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq12_ac
  have swap_cd := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq14_cd
  have swap_bc := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq15_bc
  have inv_b : f.b⁻¹ = f.b * n.v := by
    apply inv_eq_of_mul_eq_one_right
    simp only [← mul_assoc, sq_b, sq_v]
  have inv_c : f.c⁻¹ = f.c * f.u * f.w := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, ← mul_assoc, sq_c]
    simp only [mul_assoc, tail sq_u, one_mul, sq_w]
  -- Right conjugation by x and the word expression for y.
  have Xz := act_comm f.comm_zx
  have Xt := act_comm (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt).symm)
  have Xv := act_of_reverse_commutator f.eq01_xv
  have Xu := act_of_reverse_commutator f.eq01_xu
  have Xw := act_of_reverse_commutator f.eq01_xw
  have Xa := act_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq16_ax)
  have Xb := act_of_commutator f.eq18_bx
  have Xc := act_of_reverse_commutator f.eq19_xc
  have Xd := act_of_reverse_commutator f.eq19_xd
  have y_word : f.y = f.x * f.x * z := by
    apply mul_right_cancel (b := z)
    simp only [mul_assoc, ← pow_two, f.z_sq, mul_one, f.eq04]
  have Zz := act_comm (Commute.refl z)
  have Zt := act_comm f.comm_zt.symm
  have Zv := act_comm f.comm_zv.symm
  have Zu := act_comm f.comm_zu.symm
  have Zw := act_comm f.comm_zw.symm
  have Za := act_comm f.comm_az
  have Zb := act_comm f.comm_zb.symm
  have Zc := act_comm f.comm_zc.symm
  have Zd := act_comm f.comm_zd.symm
  -- The supplied y-actions and its derived action on the elementary tail.
  have Yz := act_comm f.comm_zy
  have Ya := act_comm (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq06_ya).symm)
  have Yb := act_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq18_by)
  have Yc := act_of_reverse_commutator f.eq19_yc
  have Yd := act_of_reverse_commutator f.eq17_yd
  have Y : act f.y n.t = n.t ∧
      act f.y n.v = n.v ∧
      act f.y f.u = f.u * n.t ∧
      act f.y f.w = f.w * n.v := by
    rw [y_word]
    simp only [act_mul, map_mul, map_inv, Xz, Xt, Xv, Xu, Xw, Xa, Xb, Xc, Xd, Zz, Zt, Zv, Zu, Zw, Za, Zb, Zc, Zd]
    simp only [and_self, mul_assoc, one_mul, mul_one, mul_inv_rev,
    inv_b, inv_c, sqinv f.z_sq, sqinv f.t_sq, sqinv f.v_sq,
    sqinv f.u_sq, sqinv f.w_sq, sqinv f.a_sq, sqinv f.d_sq, tail swap_zt,
    swap_zt, tail swap_zv, swap_zv, tail swap_zu, swap_zu,
    tail swap_zw, swap_zw, tail swap_tv, swap_tv, tail swap_tu,
    swap_tu, tail swap_tw, swap_tw, tail swap_vu, swap_vu,
    tail swap_vw, swap_vw, tail swap_uw, swap_uw, tail swap_az,
    swap_az, tail swap_at, swap_at, tail swap_av, swap_av,
    tail swap_au, swap_au, tail swap_zb, swap_zb, tail swap_zc,
    swap_zc, tail swap_zd, swap_zd, tail swap_bt, swap_bt,
    tail swap_dv, swap_dv, tail swap_bv, swap_bv, tail swap_bw,
    swap_bw, tail swap_aw, swap_aw, tail swap_bu, swap_bu,
    tail swap_db, swap_db, tail swap_dt, swap_dt, tail swap_ab,
    swap_ab, tail swap_dw, swap_dw, tail swap_du, swap_du,
    tail swap_cu, swap_cu, tail swap_cw, swap_cw, tail swap_ct,
    swap_ct, tail swap_cv, swap_cv, tail swap_ad, swap_ad,
    tail swap_ac, swap_ac, tail swap_cd, swap_cd, tail swap_bc,
    swap_bc, tail sq_z, sq_z, tail sq_t, sq_t,
    tail sq_v, sq_v, tail sq_u, sq_u, tail sq_w,
    sq_w, tail sq_a, sq_a, tail sq_d, sq_d,
    tail sq_b, sq_b, tail sq_c, sq_c]
  rcases Y with ⟨Yt, Yv, Yu, Yw⟩

  have swap_of_act {j k q : G} (hh : act k j = q) : j * k = k * q := by
    rw [← hh]
    simp [act, mul_assoc]
  have swap_zx := swap_of_act Xz
  have swap_tx := swap_of_act Xt
  have swap_vx := swap_of_act Xv
  have swap_ux := swap_of_act Xu
  have swap_wx := swap_of_act Xw
  have swap_ax := swap_of_act Xa
  have swap_bx := swap_of_act Xb
  have swap_cx := swap_of_act Xc
  have swap_dx := swap_of_act Xd
  have swap_zy := swap_of_act Yz
  have swap_ty := swap_of_act Yt
  have swap_vy := swap_of_act Yv
  have swap_uy := swap_of_act Yu
  have swap_wy := swap_of_act Yw
  have swap_ay := swap_of_act Ya
  have swap_by := swap_of_act Yb
  have swap_cy := swap_of_act Yc
  have swap_dy := swap_of_act Yd
  have swap_yx : f.y * f.x = f.x * f.y := by
    rw [y_word]
    simp only [mul_assoc, tail f.comm_zx.eq, f.comm_zx.eq]
  have sq_x : f.x * f.x = f.y * z := by simpa only [pow_two] using f.eq04
  have sq_y : f.y * f.y = 1 := by simpa only [pow_two] using f.y_sq
  have Rz := act_comm f.comm_zr
  have Rt : act f.r n.t = _ := f.eq20_tr
  have Rv : act f.r n.v = _ := f.eq21_vr
  have Ra : act f.r f.a = f.d * f.u * n.v := by
    simpa [act, ParrottCentralizerInvolutionData.HasCompatibleActionParameters] using hp.1
  have Rd : act f.r f.d = f.a * n.v := by
    simpa [act, ParrottCentralizerInvolutionData.HasCompatibleActionParameters] using hp.2.1
  have Rc : act f.r f.c = f.c * f.d * f.a * f.w * n.t := by
    simpa [act, ParrottCentralizerInvolutionData.HasCompatibleActionParameters] using hp.2.2.1
  have Rb : act f.r f.b = f.d * f.c * f.b := by
    simpa [act, ParrottCentralizerInvolutionData.HasCompatibleActionParameters] using hp.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    try simp only [map_mul, Rz, Rt, Rv, Ra, Rd, Rc, Rb]
    try simp only [act, MonoidHom.coe_mk, OneHom.coe_mk, sqinv f.u_sq]
    try simp only [Tits.parrottCommutator_eq_iff, SemiconjBy, Commute, pow_succ, pow_zero, mul_one]
    simp only [and_self, mul_assoc, one_mul, mul_one, mul_inv_rev,
    inv_b, inv_c, sqinv f.z_sq, sqinv f.t_sq, sqinv f.v_sq,
    sqinv f.u_sq, sqinv f.w_sq, sqinv f.a_sq, sqinv f.d_sq, tail swap_zt,
    swap_zt, tail swap_zv, swap_zv, tail swap_zu, swap_zu,
    tail swap_zw, swap_zw, tail swap_tv, swap_tv, tail swap_tu,
    swap_tu, tail swap_tw, swap_tw, tail swap_vu, swap_vu,
    tail swap_vw, swap_vw, tail swap_uw, swap_uw, tail swap_az,
    swap_az, tail swap_at, swap_at, tail swap_av, swap_av,
    tail swap_au, swap_au, tail swap_zb, swap_zb, tail swap_zc,
    swap_zc, tail swap_zd, swap_zd, tail swap_bt, swap_bt,
    tail swap_dv, swap_dv, tail swap_bv, swap_bv, tail swap_bw,
    swap_bw, tail swap_aw, swap_aw, tail swap_bu, swap_bu,
    tail swap_db, swap_db, tail swap_dt, swap_dt, tail swap_ab,
    swap_ab, tail swap_dw, swap_dw, tail swap_du, swap_du,
    tail swap_cu, swap_cu, tail swap_cw, swap_cw, tail swap_ct,
    swap_ct, tail swap_cv, swap_cv, tail swap_ad, swap_ad,
    tail swap_ac, swap_ac, tail swap_cd, swap_cd, tail swap_bc,
    swap_bc, tail sq_z, sq_z, tail sq_t, sq_t,
    tail sq_v, sq_v, tail sq_u, sq_u, tail sq_w,
    sq_w, tail sq_a, sq_a, tail sq_d, sq_d,
    tail sq_b, sq_b, tail sq_c, sq_c,
    tail swap_zx, swap_zx, tail swap_tx, swap_tx, tail swap_vx, swap_vx, tail swap_ux, swap_ux, tail
    swap_wx, swap_wx, tail swap_ax, swap_ax, tail swap_bx, swap_bx, tail swap_cx, swap_cx, tail
    swap_dx, swap_dx, tail swap_zy, swap_zy, tail swap_ty, swap_ty, tail swap_vy, swap_vy, tail
    swap_uy, swap_uy, tail swap_wy, swap_wy, tail swap_ay, swap_ay, tail swap_by, swap_by, tail
    swap_cy, swap_cy, tail swap_dy, swap_dy, tail swap_yx, swap_yx, tail sq_x, sq_x, tail sq_y,
    sq_y]

private theorem commutator_mem (K : Subgroup G) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    Tits.parrottCommutator a b ∈ K :=
  K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem ha) (K.inv_mem hb)) ha) hb

/-- Three short words recover the tail needed for the change of generators. -/
private theorem tail_mem (K : Subgroup G) {a b c t v z : G}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (bb : b ^ 2 = v) (ab : Tits.parrottCommutator a b = t)
    (cv : Tits.parrottCommutator c v = z) : v ∈ K ∧ t ∈ K ∧ z ∈ K := by
  have hv : v ∈ K := bb ▸ K.pow_mem hb 2
  exact ⟨hv, ab ▸ commutator_mem K ha hb, cv ▸ commutator_mem K hc hv⟩

/-- Normalize the second a-image coset by changing the entire Sylow frame.
The original elementary subgroup, Sylow subgroup, z, t, v, and r are retained. -/
public def ParrottCentralizerInvolutionData.toActionDataOfSecondCoset
    (f : ParrottCentralizerInvolutionData n)
    (hp : f.HasCompatibleActionParameters true true false false) :
    ParrottCentralizerActionData n := by
  obtain ⟨z_sq, t_sq, v_sq, u_sq, w_sq, a_sq, comm_zt, comm_zv, comm_zu, comm_zw, comm_tv, comm_tu,
    comm_tw, comm_vu, comm_vw, comm_uw, comm_az, comm_at, comm_av, comm_au, comm_zb, comm_zc,
    comm_zd, comm_zx, comm_zy, comm_bt, y_sq, d_sq, eq01_x, eq01_xt, eq01_xv, eq01_xu, eq01_xw,
    eq02_bw, eq02_aw, eq02_bu, eq03_db, eq03_dt, eq05_ab, eq06_ya, eq07_dw, eq08_du, eq09_cu,
    eq09_cw, eq10_ct, eq10_cv, eq11_ad, eq12_ac, eq14_cd, eq15_bc, eq16_ax, eq17_yd, eq18_bx,
    eq18_by, eq19_yc, eq19_xc, eq19_xd, eq03_b, eq04, eq13, uy, ar, dr, cr, br⟩ :=
    transported_relations f hp
  have core_mem (K : Subgroup G) :
      (f.a ∈ K ∧ f.b ∈ K ∧ f.c ∈ K ∧ f.d ∈ K) ↔
      (f.a ∈ K ∧ f.b * z ∈ K ∧ f.c * n.t * z ∈ K ∧ f.d * n.v ∈ K) := by
    constructor
    · rintro ⟨ha, hb, hc, hd⟩
      obtain ⟨hv, ht, hz⟩ := tail_mem K ha hb hc f.eq03_b f.eq05_ab f.eq10_cv
      exact ⟨ha, K.mul_mem hb hz, K.mul_mem (K.mul_mem hc ht) hz, K.mul_mem hd hv⟩
    · rintro ⟨ha, hb, hc, hd⟩
      obtain ⟨hv, ht, hz⟩ := tail_mem K ha hb hc eq03_b eq05_ab eq10_cv
      exact ⟨ha, (K.mul_mem_cancel_right hz).mp hb,
        (K.mul_mem_cancel_right ht).mp ((K.mul_mem_cancel_right hz).mp hc),
        (K.mul_mem_cancel_right hv).mp hd⟩
  have core_eq : Subgroup.closure ({f.a, f.b * z, f.c * n.t * z, f.d * n.v} : Set G) =
      Subgroup.closure ({f.a, f.b, f.c, f.d} : Set G) := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      have hh := (core_mem (Subgroup.closure ({f.a, f.b, f.c, f.d} : Set G))).mp
        ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
          Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
      simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe] using hh
    · apply (Subgroup.closure_le _).mpr
      have hh := (core_mem (Subgroup.closure
          ({f.a, f.b * z, f.c * n.t * z, f.d * n.v} : Set G))).mpr
        ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
          Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
      simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe] using hh
  have sylow_mem (K : Subgroup G) :
      (f.x ∈ K ∧ f.a ∈ K ∧ f.b ∈ K ∧ f.c ∈ K ∧ f.d ∈ K) ↔
      (f.x * n.v ∈ K ∧ f.a ∈ K ∧ f.b * z ∈ K ∧
        f.c * n.t * z ∈ K ∧ f.d * n.v ∈ K) := by
    constructor
    · rintro ⟨hx, hh⟩
      have hv : n.v ∈ K := f.eq03_b ▸ K.pow_mem hh.2.1 2
      exact ⟨K.mul_mem hx hv, (core_mem K).mp hh⟩
    · rintro ⟨hx, hh⟩
      have hv : n.v ∈ K := eq03_b ▸ K.pow_mem hh.2.1 2
      exact ⟨(K.mul_mem_cancel_right hv).mp hx, (core_mem K).mpr hh⟩
  have sylow_eq :
      Subgroup.closure ({f.x * n.v, f.a, f.b * z, f.c * n.t * z, f.d * n.v} : Set G) =
      Subgroup.closure ({f.x, f.a, f.b, f.c, f.d} : Set G) := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      have hh := (sylow_mem (Subgroup.closure ({f.x, f.a, f.b, f.c, f.d} : Set G))).mp
        ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
          Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
          Subgroup.subset_closure (by simp)⟩
      simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe] using hh
    · apply (Subgroup.closure_le _).mpr
      have hh := (sylow_mem (Subgroup.closure
          ({f.x * n.v, f.a, f.b * z, f.c * n.t * z, f.d * n.v} : Set G))).mpr
        ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
          Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
          Subgroup.subset_closure (by simp)⟩
      simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe] using hh
  have ur : Commute f.u f.r := by
    show f.u * f.r = f.r * f.u
    have hh := congrArg (fun q => f.r * q) f.eq22_ur
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
  have fifth : (f.r * (f.y * n.t)) ^ 5 = 1 := by
    have hh := congrArg (act f.u) f.eq20_ry
    simpa only [map_pow, map_mul, map_one, act_comm ur.symm, uy] using hh
  exact {
    u := f.u
    w := f.w
    a := f.a
    b := f.b * z
    c := f.c * n.t * z
    d := f.d * n.v
    x := f.x * n.v
    y := f.y * n.t
    derived_basis := f.derived_basis
    elementary_basis := f.elementary_basis
    core_generators := core_eq.trans f.core_generators
    sylow_generators := sylow_eq.trans f.sylow_generators
    z_sq := z_sq
    t_sq := t_sq
    v_sq := v_sq
    u_sq := u_sq
    w_sq := w_sq
    a_sq := a_sq
    comm_zt := comm_zt
    comm_zv := comm_zv
    comm_zu := comm_zu
    comm_zw := comm_zw
    comm_tv := comm_tv
    comm_tu := comm_tu
    comm_tw := comm_tw
    comm_vu := comm_vu
    comm_vw := comm_vw
    comm_uw := comm_uw
    comm_az := comm_az
    comm_at := comm_at
    comm_av := comm_av
    comm_au := comm_au
    comm_zb := comm_zb
    comm_zc := comm_zc
    comm_zd := comm_zd
    comm_zx := comm_zx
    comm_zy := comm_zy
    comm_bt := comm_bt
    y_sq := y_sq
    d_sq := d_sq
    eq01_x := eq01_x
    eq01_xt := eq01_xt
    eq01_xv := eq01_xv
    eq01_xu := eq01_xu
    eq01_xw := eq01_xw
    eq02_bw := eq02_bw
    eq02_aw := eq02_aw
    eq02_bu := eq02_bu
    eq03_db := eq03_db
    eq03_dt := eq03_dt
    eq05_ab := eq05_ab
    eq06_ya := eq06_ya
    eq07_dw := eq07_dw
    eq08_du := eq08_du
    eq09_cu := eq09_cu
    eq09_cw := eq09_cw
    eq10_ct := eq10_ct
    eq10_cv := eq10_cv
    eq11_ad := eq11_ad
    eq12_ac := eq12_ac
    eq14_cd := eq14_cd
    eq15_bc := eq15_bc
    eq16_ax := eq16_ax
    eq17_yd := eq17_yd
    eq18_bx := eq18_bx
    eq18_by := eq18_by
    eq19_yc := eq19_yc
    eq19_xc := eq19_xc
    eq19_xd := eq19_xd
    eq03_b := eq03_b
    eq04 := eq04
    eq13 := eq13
    r := f.r
    centralizer_generators := f.centralizer_generators
    r_order := f.r_order
    r_conjugate := f.r_conjugate
    comm_zr := f.comm_zr
    eq20_r := f.eq20_r
    eq20_ry := fifth
    eq20_tr := f.eq20_tr
    eq21_vr := f.eq21_vr
    eq22_ur := f.eq22_ur
    eq22_wr := f.eq22_wr
    eq23_ar := ar
    eq23_dr := dr
    eq23_cr := cr
    eq23_br := br }

/-- The normalized second coset supplies a complete unprimed action frame. -/
public theorem ParrottCentralizerInvolutionData.nonempty_action_of_second_coset
    (f : ParrottCentralizerInvolutionData n)
    (hp : f.HasCompatibleActionParameters true true false false) :
    Nonempty (ParrottCentralizerActionData n) :=
  ⟨f.toActionDataOfSecondCoset hp⟩

end Stellmacher.Recognition
