module

public import Stellmacher.Recognition.Parrott.CentralizerCommutatorCoefficients
public import Stellmacher.Recognition.Parrott.CentralizerCompatibleParameters

/-!
# Existence of the compatible centralizer action parameters

The commutator coefficient certificate leaves seven binary choices. Applying r
again to its b-image fixes the remaining central coefficient in the c-image.
The supplied relation (ry)^5 = 1 gives the braid identity `r*y*r*y*r = y*r*y*r*y`.
Conjugating a by its two sides rules out the three unwanted choices of the
remaining w- and u-coefficients: their discrepancy would fail to commute with
a or b, forcing z = 1. This leaves exactly the corrected four-parameter family.

All equations retain the supplied involution, Sylow frame, elementary subgroup,
and normalizer data. No presentation relators are assumed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.680–681, equations (20)–(23); the c-image coefficient is the one forced by
the actual relation [b,c] = uv.
-/

namespace Stellmacher.Recognition
private def act {G : Type*} [Group G] (g : G) : G →* G where
  toFun j := g⁻¹ * j * g
  map_one' := by simp
  map_mul' j k := by simp [mul_assoc]

private theorem act_comm {G : Type*} [Group G] {g j : G} (h : Commute j g) :
    act g j = j := by
  change g⁻¹ * j * g = j
  rw [mul_assoc, h.eq, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem tail {G : Type*} [Group G] {a b c : G} (h : a * b = c) (k : G) :
    a * (b * k) = c * k := by rw [← mul_assoc, h]

private theorem sqinv {G : Type*} [Group G] {a : G} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

private theorem revswap {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) : b * a = a * b * c⁻¹ := by rw [h]; group

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem nontrivial (h : ParrottCentralizerHypotheses z) : z ≠ 1 := by
  intro hz
  have ho := h.involution
  rw [hz, orderOf_one] at ho
  omega

set_option linter.unusedSimpArgs false

macro "collect_core " f:term "," n:term "," z:term loc:Lean.Parser.Tactic.location " using " tac:Lean.Parser.Tactic.tacticSeq : tactic => `(tactic| (
  -- Collection rules for the core, with the elementary tail ordered w,u,v,t,z.
  have sq_z : $z * $z = 1 := by simpa only [pow_two] using ($f).z_sq
  have sq_t : ($n).t * ($n).t = 1 := by simpa only [pow_two] using ($f).t_sq
  have sq_v : ($n).v * ($n).v = 1 := by simpa only [pow_two] using ($f).v_sq
  have sq_u : ($f).u * ($f).u = 1 := by simpa only [pow_two] using ($f).u_sq
  have sq_w : ($f).w * ($f).w = 1 := by simpa only [pow_two] using ($f).w_sq
  have sq_a : ($f).a * ($f).a = 1 := by simpa only [pow_two] using ($f).a_sq
  have sq_d : ($f).d * ($f).d = 1 := by simpa only [pow_two] using ($f).d_sq
  have sq_b : ($f).b * ($f).b = ($n).v := by simpa only [pow_two] using ($f).eq03_b
  have sq_c : ($f).c * ($f).c = ($f).w * ($f).u := by simpa only [pow_two] using ($f).eq13
  have dv : ($f).d * ($n).v = ($n).v * ($f).d := by
    calc
      ($f).d * ($n).v = ($n).v⁻¹ * ($f).d := by
        rw [← ($f).eq03_db]
        simp only [Tits.parrottCommutator, mul_inv_rev, inv_inv, sqinv ($f).d_sq]
        group
        simp only [mul_assoc, sq_d, one_mul, mul_one]
      _ = ($n).v * ($f).d := by rw [sqinv ($f).v_sq]
  have bv : Commute ($f).b ($n).v := by
    rw [← ($f).eq03_b]
    exact Commute.self_pow ($f).b 2
  have swap_zt := ($f).comm_zt.eq
  have swap_zv := ($f).comm_zv.eq
  have swap_zu := ($f).comm_zu.eq
  have swap_zw := ($f).comm_zw.eq
  have swap_tv := ($f).comm_tv.eq
  have swap_tu := ($f).comm_tu.eq
  have swap_tw := ($f).comm_tw.eq
  have swap_vu := ($f).comm_vu.eq
  have swap_vw := ($f).comm_vw.eq
  have swap_uw := ($f).comm_uw.eq
  have swap_az := ($f).comm_az.symm.eq
  have swap_at := ($f).comm_at.symm.eq
  have swap_av := ($f).comm_av.symm.eq
  have swap_au := ($f).comm_au.symm.eq
  have swap_zb := ($f).comm_zb.eq
  have swap_zc := ($f).comm_zc.eq
  have swap_zd := ($f).comm_zd.eq
  have swap_bt := ($f).comm_bt.symm.eq
  have swap_dv := dv.symm
  have swap_bv := bv.symm.eq
  have swap_bw := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq02_bw
  have swap_bw := revswap swap_bw
  simp only [inv_one, mul_one] at swap_bw
  have swap_aw := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq02_aw
  have swap_aw := revswap swap_aw
  simp only [sqinv ($f).z_sq] at swap_aw
  have swap_bu := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq02_bu
  have swap_bu := revswap swap_bu
  simp only [sqinv ($f).z_sq] at swap_bu
  have swap_db := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq03_db
  have swap_db := revswap swap_db
  simp only [sqinv ($f).v_sq] at swap_db
  have swap_dt := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq03_dt
  have swap_dt := revswap swap_dt
  simp only [sqinv ($f).z_sq] at swap_dt
  have swap_ab := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq05_ab
  have swap_dw := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq07_dw
  have swap_dw := revswap swap_dw
  simp only [inv_one, mul_one] at swap_dw
  have swap_du := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq08_du
  have swap_du := revswap swap_du
  simp only [inv_one, mul_one] at swap_du
  have swap_cu := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq09_cu
  have swap_cu := revswap swap_cu
  simp only [inv_one, mul_one] at swap_cu
  have swap_cw := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq09_cw
  have swap_cw := revswap swap_cw
  simp only [inv_one, mul_one] at swap_cw
  have swap_ct := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq10_ct
  have swap_ct := revswap swap_ct
  simp only [inv_one, mul_one] at swap_ct
  have swap_cv := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq10_cv
  have swap_cv := revswap swap_cv
  simp only [sqinv ($f).z_sq] at swap_cv
  have swap_ad := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq11_ad
  have swap_ac := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq12_ac
  have swap_cd := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq14_cd
  have swap_bc := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq15_bc
  have inv_b : ($f).b⁻¹ = ($f).b * ($n).v := by
    apply inv_eq_of_mul_eq_one_right
    simp only [← mul_assoc, sq_b, sq_v]
  have inv_c : ($f).c⁻¹ = ($f).c * ($f).u * ($f).w := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, ← mul_assoc, sq_c]
    simp only [mul_assoc, tail sq_u, one_mul, sq_w]

  ($tac)
  all_goals simp only [and_self, mul_assoc, one_mul, mul_one, mul_inv_rev,
  inv_b, inv_c, sqinv ($f).z_sq, sqinv ($f).t_sq, sqinv ($f).v_sq,
  sqinv ($f).u_sq, sqinv ($f).w_sq, sqinv ($f).a_sq, sqinv ($f).d_sq, tail swap_zt,
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
  tail sq_b, sq_b, tail sq_c, sq_c] $loc
))

private theorem act_mul {G : Type*} [Group G] (g h j : G) :
    act (g * h) j = act h (act g j) := by simp [act, mul_assoc]

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

private theorem act_twice (f : ParrottCentralizerInvolutionData n) (x : G) :
    act f.r (act f.r x) = x := by
  rw [← act_mul]
  have rr : f.r * f.r = 1 := by simpa only [pow_two] using f.eq20_r
  simp [rr, act]

private theorem braid (f : ParrottCentralizerInvolutionData n) :
    f.r * f.y * f.r * f.y * f.r = f.y * f.r * f.y * f.r * f.y := by
  apply eq_of_mul_inv_eq_one
  simpa only [mul_inv_rev, sqinv f.eq20_r, sqinv f.y_sq, pow_succ, pow_zero,
    one_mul, mul_one, mul_assoc] using f.eq20_ry

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem involutive_coeff (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (i j k m jb mb mc : Bool)
    (Ra : act f.r f.a = f.d * f.w ^ i.toNat * f.u ^ j.toNat * n.v ^ k.toNat * z ^ m.toNat)
    (Rd : act f.r f.d = f.a * f.u ^ (j.xor k).toNat * n.v ^ (i.xor k).toNat * n.t ^ i.toNat * z ^ (i.xor m).toNat)
    (Rb : act f.r f.b = f.d * f.c * f.b * f.w ^ (!j).toNat * f.u ^ jb.toNat * n.v ^ (jb.xor (j.xor k)).toNat * n.t ^ (j.xor k).toNat * z ^ mb.toNat)
    (Rc : act f.r f.c = f.c * f.d * f.a * f.w ^ k.toNat * f.u ^ (jb.xor (j.xor k)).toNat * n.v ^ i.toNat * n.t ^ (i.xor k).toNat * z ^ mc.toNat)
    : mc = (i.xor m).xor jb := by
  have Rz := act_comm f.comm_zr
  have Rt : act f.r n.t = _ := f.eq20_tr
  have Rv : act f.r n.v = _ := f.eq21_vr
  have Ru : act f.r f.u = _ := f.eq22_ur
  have Rw : act f.r f.w = _ := f.eq22_wr
  have hh := congrArg (act f.r) Rb
  rw [act_twice] at hh
  simp only [map_mul, map_pow, Ra, Rb, Rc, Rd, Rz, Rt, Rv, Ru, Rw] at hh
  collect_core f, n, z at hh using
    (cases i <;> cases j <;> cases k <;> cases m <;> cases jb <;> cases mb <;> cases mc
     all_goals first | rfl | exfalso
     all_goals simp only [Bool.toNat_false, Bool.toNat_true, Bool.xor_false, Bool.xor_true,
       Bool.not_false, Bool.not_true, pow_zero, pow_one, mul_one] at hh)
  all_goals exact nontrivial h (by simpa using hh)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem y_tail (f : ParrottCentralizerInvolutionData n) :
    act f.y n.t = n.t ∧ act f.y n.v = n.v ∧
    act f.y f.u = f.u * n.t ∧ act f.y f.w = f.w * n.v := by
  have Xz := act_comm f.comm_zx
  have Xt := act_comm (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt).symm)
  have Xv := act_of_reverse_commutator f.eq01_xv
  have Xu := act_of_reverse_commutator f.eq01_xu
  have Xw := act_of_reverse_commutator f.eq01_xw
  have y_word : f.y = f.x * f.x * z := by
    apply mul_right_cancel (b := z)
    simp only [mul_assoc, ← pow_two, f.z_sq, mul_one, f.eq04]
  have Zz := act_comm (Commute.refl z)
  have Zt := act_comm f.comm_zt.symm
  have Zv := act_comm f.comm_zv.symm
  have Zu := act_comm f.comm_zu.symm
  have Zw := act_comm f.comm_zw.symm
  rw [y_word]
  simp only [act_mul, map_mul, map_inv, Xz, Xt, Xv, Xu, Xw, Zz, Zt, Zv, Zu, Zw]
  collect_core f, n, z at ⊢ using skip

private theorem commutes_of_one (x : G) {q : G} (hq : q = 1) : x*q=q*x := by
  rw [hq]
  simp

set_option maxRecDepth 4000 in
macro "reject_fifth_case " probe:term "," f:term "," n:term "," z:term "," h:term "," j:term "," k:term "," m:term "," mb:term "," Ra:term "," Rd:term "," Rb:term "," Rc:term : tactic => `(tactic| (
  -- Collection rules for the core, with the elementary tail ordered w,u,v,t,z.
    have sq_z : ($z) * ($z) = 1 := by simpa only [pow_two] using ($f).z_sq
    have sq_t : ($n).t * ($n).t = 1 := by simpa only [pow_two] using ($f).t_sq
    have sq_v : ($n).v * ($n).v = 1 := by simpa only [pow_two] using ($f).v_sq
    have sq_u : ($f).u * ($f).u = 1 := by simpa only [pow_two] using ($f).u_sq
    have sq_w : ($f).w * ($f).w = 1 := by simpa only [pow_two] using ($f).w_sq
    have sq_a : ($f).a * ($f).a = 1 := by simpa only [pow_two] using ($f).a_sq
    have sq_d : ($f).d * ($f).d = 1 := by simpa only [pow_two] using ($f).d_sq
    have sq_b : ($f).b * ($f).b = ($n).v := by simpa only [pow_two] using ($f).eq03_b
    have sq_c : ($f).c * ($f).c = ($f).w * ($f).u := by simpa only [pow_two] using ($f).eq13
    have dv : ($f).d * ($n).v = ($n).v * ($f).d := by
      calc
        ($f).d * ($n).v = ($n).v⁻¹ * ($f).d := by
          rw [← ($f).eq03_db]
          simp only [Tits.parrottCommutator, mul_inv_rev, inv_inv, sqinv ($f).d_sq]
          group
          simp only [mul_assoc, sq_d, one_mul, mul_one]
        _ = ($n).v * ($f).d := by rw [sqinv ($f).v_sq]
    have bv : Commute ($f).b ($n).v := by
      rw [← ($f).eq03_b]
      exact Commute.self_pow ($f).b 2
    have swap_zt := ($f).comm_zt.eq
    have swap_zv := ($f).comm_zv.eq
    have swap_zu := ($f).comm_zu.eq
    have swap_zw := ($f).comm_zw.eq
    have swap_tv := ($f).comm_tv.eq
    have swap_tu := ($f).comm_tu.eq
    have swap_tw := ($f).comm_tw.eq
    have swap_vu := ($f).comm_vu.eq
    have swap_vw := ($f).comm_vw.eq
    have swap_uw := ($f).comm_uw.eq
    have swap_az := ($f).comm_az.symm.eq
    have swap_at := ($f).comm_at.symm.eq
    have swap_av := ($f).comm_av.symm.eq
    have swap_au := ($f).comm_au.symm.eq
    have swap_zb := ($f).comm_zb.eq
    have swap_zc := ($f).comm_zc.eq
    have swap_zd := ($f).comm_zd.eq
    have swap_bt := ($f).comm_bt.symm.eq
    have swap_dv := dv.symm
    have swap_bv := bv.symm.eq
    have swap_bw := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq02_bw
    have swap_bw := revswap swap_bw
    simp only [inv_one, mul_one] at swap_bw
    have swap_aw := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq02_aw
    have swap_aw := revswap swap_aw
    simp only [sqinv ($f).z_sq] at swap_aw
    have swap_bu := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq02_bu
    have swap_bu := revswap swap_bu
    simp only [sqinv ($f).z_sq] at swap_bu
    have swap_db := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq03_db
    have swap_db := revswap swap_db
    simp only [sqinv ($f).v_sq] at swap_db
    have swap_dt := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq03_dt
    have swap_dt := revswap swap_dt
    simp only [sqinv ($f).z_sq] at swap_dt
    have swap_ab := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq05_ab
    have swap_dw := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq07_dw
    have swap_dw := revswap swap_dw
    simp only [inv_one, mul_one] at swap_dw
    have swap_du := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq08_du
    have swap_du := revswap swap_du
    simp only [inv_one, mul_one] at swap_du
    have swap_cu := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq09_cu
    have swap_cu := revswap swap_cu
    simp only [inv_one, mul_one] at swap_cu
    have swap_cw := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq09_cw
    have swap_cw := revswap swap_cw
    simp only [inv_one, mul_one] at swap_cw
    have swap_ct := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq10_ct
    have swap_ct := revswap swap_ct
    simp only [inv_one, mul_one] at swap_ct
    have swap_cv := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq10_cv
    have swap_cv := revswap swap_cv
    simp only [sqinv ($f).z_sq] at swap_cv
    have swap_ad := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq11_ad
    have swap_ac := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq12_ac
    have swap_cd := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq14_cd
    have swap_bc := (Tits.parrottCommutator_eq_iff _ _ _).mp ($f).eq15_bc
    have inv_b : ($f).b⁻¹ = ($f).b * ($n).v := by
      apply inv_eq_of_mul_eq_one_right
      simp only [← mul_assoc, sq_b, sq_v]
    have inv_c : ($f).c⁻¹ = ($f).c * ($f).u * ($f).w := by
      apply inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, ← mul_assoc, sq_c]
      simp only [mul_assoc, tail sq_u, one_mul, sq_w]

    have Rz := act_comm ($f).comm_zr
    have Rt : act ($f).r ($n).t = _ := ($f).eq20_tr
    have Rv : act ($f).r ($n).v = _ := ($f).eq21_vr
    have Ru : act ($f).r ($f).u = _ := ($f).eq22_ur
    have Rw : act ($f).r ($f).w = _ := ($f).eq22_wr
    have Yz := act_comm ($f).comm_zy
    have Ya := act_comm (((Tits.parrottCommutator_eq_one_iff _ _).mp ($f).eq06_ya).symm)
    have Yb := act_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp ($f).eq18_by)
    have Yc := act_of_reverse_commutator ($f).eq19_yc
    have Yd := act_of_reverse_commutator ($f).eq17_yd
    obtain ⟨Yt, Yv, Yu, Yw⟩ := y_tail ($f)
    have hh := congrArg (fun q => act q ($f).a) (braid ($f))
    cases ($j) <;> cases ($k) <;> cases ($m) <;> cases ($mb)
    all_goals
      simp only [Bool.toNat_false, Bool.toNat_true, Bool.xor_false, Bool.xor_true,
        Bool.not_false, Bool.not_true, pow_zero, pow_one, act_mul, map_mul, map_pow, map_inv, ($Ra), ($Rb), ($Rc), ($Rd), Rz, Rt, Rv, Ru, Rw,
        Ya, Yb, Yc, Yd, Yz, Yt, Yv, Yu, Yw, and_self, mul_assoc, one_mul, mul_one, mul_inv_rev,
        inv_b, inv_c, sqinv ($f).z_sq, sqinv ($f).t_sq, sqinv ($f).v_sq,
        sqinv ($f).u_sq, sqinv ($f).w_sq, sqinv ($f).a_sq, sqinv ($f).d_sq, tail swap_zt,
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
        tail sq_b, sq_b, tail sq_c, sq_c] at hh
      have hx := commutes_of_one ($probe) (mul_inv_eq_one.mpr hh)
      simp only [and_self, mul_assoc, one_mul, mul_one, mul_inv_rev,
        inv_b, inv_c, sqinv ($f).z_sq, sqinv ($f).t_sq, sqinv ($f).v_sq,
        sqinv ($f).u_sq, sqinv ($f).w_sq, sqinv ($f).a_sq, sqinv ($f).d_sq, tail swap_zt,
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
        tail sq_b, sq_b, tail sq_c, sq_c] at hx
      exact nontrivial ($h) (by simpa using hx)
))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem fifth_coeff_01 (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (j k m mb : Bool)
    (Ra : act f.r f.a = f.d * f.w ^ false.toNat * f.u ^ j.toNat * n.v ^ k.toNat * z ^ m.toNat)
    (Rd : act f.r f.d = f.a * f.u ^ (j.xor k).toNat * n.v ^ (false.xor k).toNat * n.t ^ false.toNat * z ^ (false.xor m).toNat)
    (Rb : act f.r f.b = f.d * f.c * f.b * f.w ^ (!j).toNat * f.u ^ true.toNat * n.v ^ (true.xor (j.xor k)).toNat * n.t ^ (j.xor k).toNat * z ^ mb.toNat)
    (Rc : act f.r f.c = f.c * f.d * f.a * f.w ^ k.toNat * f.u ^ (true.xor (j.xor k)).toNat * n.v ^ false.toNat * n.t ^ (false.xor k).toNat * z ^ ((false.xor m).xor true).toNat)
    : False := by
  reject_fifth_case f.a, f, n, z, h, j, k, m, mb, Ra, Rd, Rb, Rc

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem fifth_coeff_10 (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (j k m mb : Bool)
    (Ra : act f.r f.a = f.d * f.w ^ true.toNat * f.u ^ j.toNat * n.v ^ k.toNat * z ^ m.toNat)
    (Rd : act f.r f.d = f.a * f.u ^ (j.xor k).toNat * n.v ^ (true.xor k).toNat * n.t ^ true.toNat * z ^ (true.xor m).toNat)
    (Rb : act f.r f.b = f.d * f.c * f.b * f.w ^ (!j).toNat * f.u ^ false.toNat * n.v ^ (false.xor (j.xor k)).toNat * n.t ^ (j.xor k).toNat * z ^ mb.toNat)
    (Rc : act f.r f.c = f.c * f.d * f.a * f.w ^ k.toNat * f.u ^ (false.xor (j.xor k)).toNat * n.v ^ true.toNat * n.t ^ (true.xor k).toNat * z ^ ((true.xor m).xor false).toNat)
    : False := by
  reject_fifth_case f.a, f, n, z, h, j, k, m, mb, Ra, Rd, Rb, Rc

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem fifth_coeff_11 (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (j k m mb : Bool)
    (Ra : act f.r f.a = f.d * f.w ^ true.toNat * f.u ^ j.toNat * n.v ^ k.toNat * z ^ m.toNat)
    (Rd : act f.r f.d = f.a * f.u ^ (j.xor k).toNat * n.v ^ (true.xor k).toNat * n.t ^ true.toNat * z ^ (true.xor m).toNat)
    (Rb : act f.r f.b = f.d * f.c * f.b * f.w ^ (!j).toNat * f.u ^ true.toNat * n.v ^ (true.xor (j.xor k)).toNat * n.t ^ (j.xor k).toNat * z ^ mb.toNat)
    (Rc : act f.r f.c = f.c * f.d * f.a * f.w ^ k.toNat * f.u ^ (true.xor (j.xor k)).toNat * n.v ^ true.toNat * n.t ^ (true.xor k).toNat * z ^ ((true.xor m).xor true).toNat)
    : False := by
  reject_fifth_case f.b, f, n, z, h, j, k, m, mb, Ra, Rd, Rb, Rc

private theorem fifth_coeff (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (i j k m jb mb : Bool)
    (Ra : act f.r f.a = f.d * f.w ^ i.toNat * f.u ^ j.toNat * n.v ^ k.toNat * z ^ m.toNat)
    (Rd : act f.r f.d = f.a * f.u ^ (j.xor k).toNat * n.v ^ (i.xor k).toNat * n.t ^ i.toNat * z ^ (i.xor m).toNat)
    (Rb : act f.r f.b = f.d * f.c * f.b * f.w ^ (!j).toNat * f.u ^ jb.toNat * n.v ^ (jb.xor (j.xor k)).toNat * n.t ^ (j.xor k).toNat * z ^ mb.toNat)
    (Rc : act f.r f.c = f.c * f.d * f.a * f.w ^ k.toNat * f.u ^ (jb.xor (j.xor k)).toNat * n.v ^ i.toNat * n.t ^ (i.xor k).toNat * z ^ ((i.xor m).xor jb).toNat)
    : i = false ∧ jb = false := by
  cases i <;> cases jb
  · exact ⟨rfl, rfl⟩
  · exact False.elim (fifth_coeff_01 f h j k m mb Ra Rd Rb Rc)
  · exact False.elim (fifth_coeff_10 f h j k m mb Ra Rd Rb Rc)
  · exact False.elim (fifth_coeff_11 f h j k m mb Ra Rd Rb Rc)

/-- The corrected core-action parameters exist on the supplied Sylow frame,
without changing the involution or the elementary and normalizer data. -/
public theorem ParrottCentralizerInvolutionData.exists_compatible_action_parameters
    [Finite G] (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) :
    ∃ α β δ γ : Bool, f.HasCompatibleActionParameters α β δ γ := by
  obtain ⟨i, j, k, m, jb, mb, mc, Ra, Rd, Rb, Rc⟩ :=
    f.core_image_seven_coefficients h
  change act f.r f.a = _ at Ra
  change act f.r f.d = _ at Rd
  change act f.r f.b = _ at Rb
  change act f.r f.c = _ at Rc
  have hmc := involutive_coeff f h i j k m jb mb mc Ra Rd Rb Rc
  subst mc
  obtain ⟨hi, hjb⟩ := fifth_coeff f h i j k m jb mb Ra Rd Rb Rc
  subst i
  subst jb
  change f.r⁻¹ * f.a * f.r = _ at Ra
  change f.r⁻¹ * f.d * f.r = _ at Rd
  change f.r⁻¹ * f.b * f.r = _ at Rb
  change f.r⁻¹ * f.c * f.r = _ at Rc
  refine ⟨j, k, m, mb, ?_, ?_, ?_, ?_⟩
  · simpa only [Bool.toNat_false, pow_zero, mul_one] using Ra
  · simpa only [Bool.false_xor, Bool.toNat_false, pow_zero, mul_one] using Rd
  · simpa only [Bool.false_xor, Bool.xor_false, Bool.toNat_false, pow_zero, mul_one] using Rc
  · have hv (p : Bool) : (n.v * n.t) ^ p.toNat = n.v ^ p.toNat * n.t ^ p.toNat := by
      cases p <;> simp
    simpa only [Bool.false_xor, Bool.toNat_false, pow_zero, mul_one, hv, mul_assoc] using Rb

end Stellmacher.Recognition
