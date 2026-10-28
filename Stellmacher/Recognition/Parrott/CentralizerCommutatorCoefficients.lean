module

public import Stellmacher.Recognition.Parrott.CentralizerCompatibleImageCoefficients

/-!
# Core-image coefficients forced by the commutator table

The binary expansions of the transported core generators initially have fourteen
coefficients after involutivity determines the d-image. Squaring b and c and
transporting the six core commutators leaves seven coefficients. Every rejected
choice would make the distinguished involution z trivial. All calculations use
the actual Sylow frame; no presentation relators or replacement frame are used.
The remaining involutivity and fifth-power restrictions are handled by
`CentralizerCompatibleParameterExistence`.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.680–681, equations (20)–(23), with the c-image correction forced by [b,c].
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem b_square_coeff (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (ib jb kb lb mb : Bool)
    (Rb : act f.r f.b = f.d * f.c * f.b * f.w ^ ib.toNat * f.u ^ jb.toNat * n.v ^ kb.toNat * n.t ^ lb.toNat * z ^ mb.toNat)
    : lb = jb.xor kb := by
  have Rz := act_comm f.comm_zr
  have Rt : act f.r n.t = _ := f.eq20_tr
  have Rv : act f.r n.v = _ := f.eq21_vr
  have Ru : act f.r f.u = _ := f.eq22_ur
  have Rw : act f.r f.w = _ := f.eq22_wr
  have hh := congrArg (act f.r) f.eq03_b
  simp only [map_mul, map_pow, Rb, Rz, Rt, Rv, Ru, Rw] at hh
  collect_core f, n, z at hh using
    (cases ib <;> cases jb <;> cases kb <;> cases lb <;> cases mb
     all_goals first | rfl | exfalso
     all_goals simp only [Bool.toNat_false, Bool.toNat_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, pow_zero, pow_one, mul_one, pow_two] at hh)
  all_goals exact nontrivial h (by simpa using hh)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem c_square_coeff (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (ic jc kc lc mc : Bool)
    (Rc : act f.r f.c = f.c * f.d * f.a * f.w ^ ic.toNat * f.u ^ jc.toNat * n.v ^ kc.toNat * n.t ^ lc.toNat * z ^ mc.toNat)
    : lc = ic.xor kc := by
  have Rz := act_comm f.comm_zr
  have Rt : act f.r n.t = _ := f.eq20_tr
  have Rv : act f.r n.v = _ := f.eq21_vr
  have Ru : act f.r f.u = _ := f.eq22_ur
  have Rw : act f.r f.w = _ := f.eq22_wr
  have hh := congrArg (act f.r) f.eq13
  simp only [map_mul, map_pow, Rc, Rz, Rt, Rv, Ru, Rw] at hh
  collect_core f, n, z at hh using
    (cases ic <;> cases jc <;> cases kc <;> cases lc <;> cases mc
     all_goals first | rfl | exfalso
     all_goals simp only [Bool.toNat_false, Bool.toNat_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, pow_zero, pow_one, mul_one, pow_two] at hh)
  all_goals exact nontrivial h (by simpa using hh)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem ab_coeff (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (i j k m ib jb kb mb : Bool)
    (Ra : act f.r f.a = f.d * f.w ^ i.toNat * f.u ^ j.toNat * n.v ^ k.toNat * z ^ m.toNat)
    (Rb : act f.r f.b = f.d * f.c * f.b * f.w ^ ib.toNat * f.u ^ jb.toNat * n.v ^ kb.toNat * n.t ^ (jb.xor kb).toNat * z ^ mb.toNat)
    : jb.xor kb = j.xor k := by
  have Rz := act_comm f.comm_zr
  have Rt : act f.r n.t = _ := f.eq20_tr
  have Rv : act f.r n.v = _ := f.eq21_vr
  have Ru : act f.r f.u = _ := f.eq22_ur
  have Rw : act f.r f.w = _ := f.eq22_wr
  have hh := congrArg (act f.r) ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq05_ab)
  simp only [map_mul, map_pow, Ra, Rb, Rz, Rt, Rv, Ru, Rw] at hh
  collect_core f, n, z at hh using
    (cases i <;> cases j <;> cases k <;> cases m <;> cases ib <;> cases jb <;> cases kb <;> cases mb
     all_goals first | rfl | exfalso
     all_goals simp only [Bool.toNat_false, Bool.toNat_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, pow_zero, pow_one, mul_one, pow_two] at hh)
  all_goals exact nontrivial h (by simpa using hh)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem ac_coeff (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (i j k m ic jc kc mc : Bool)
    (Ra : act f.r f.a = f.d * f.w ^ i.toNat * f.u ^ j.toNat * n.v ^ k.toNat * z ^ m.toNat)
    (Rc : act f.r f.c = f.c * f.d * f.a * f.w ^ ic.toNat * f.u ^ jc.toNat * n.v ^ kc.toNat * n.t ^ (ic.xor kc).toNat * z ^ mc.toNat)
    : ic.xor kc = i.xor k := by
  have Rz := act_comm f.comm_zr
  have Rt : act f.r n.t = _ := f.eq20_tr
  have Rv : act f.r n.v = _ := f.eq21_vr
  have Ru : act f.r f.u = _ := f.eq22_ur
  have Rw : act f.r f.w = _ := f.eq22_wr
  have hh := congrArg (act f.r) ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq12_ac)
  simp only [map_mul, map_pow, Ra, Rc, Rz, Rt, Rv, Ru, Rw] at hh
  collect_core f, n, z at hh using
    (cases i <;> cases j <;> cases k <;> cases m <;> cases ic <;> cases jc <;> cases kc <;> cases mc
     all_goals first | rfl | exfalso
     all_goals simp only [Bool.toNat_false, Bool.toNat_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, pow_zero, pow_one, mul_one, pow_two] at hh)
  all_goals exact nontrivial h (by simpa using hh)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem db_coeff (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (i j k m ib jb mb : Bool)
    (Rd : act f.r f.d = f.a * f.u ^ (j.xor k).toNat * n.v ^ (i.xor k).toNat * n.t ^ i.toNat * z ^ (i.xor m).toNat)
    (Rb : act f.r f.b = f.d * f.c * f.b * f.w ^ ib.toNat * f.u ^ jb.toNat * n.v ^ (jb.xor (j.xor k)).toNat * n.t ^ (j.xor k).toNat * z ^ mb.toNat)
    : ib = !j := by
  have Rz := act_comm f.comm_zr
  have Rt : act f.r n.t = _ := f.eq20_tr
  have Rv : act f.r n.v = _ := f.eq21_vr
  have Ru : act f.r f.u = _ := f.eq22_ur
  have Rw : act f.r f.w = _ := f.eq22_wr
  have hh := congrArg (act f.r) ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq03_db)
  simp only [map_mul, map_pow, Rd, Rb, Rz, Rt, Rv, Ru, Rw] at hh
  collect_core f, n, z at hh using
    (cases i <;> cases j <;> cases k <;> cases m <;> cases ib <;> cases jb <;> cases mb
     all_goals first | rfl | exfalso
     all_goals simp only [Bool.toNat_false, Bool.toNat_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, pow_zero, pow_one, mul_one, pow_two] at hh)
  all_goals exact nontrivial h (by simpa using hh)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem cd_coeff (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (i j k m ic jc mc : Bool)
    (Rc : act f.r f.c = f.c * f.d * f.a * f.w ^ ic.toNat * f.u ^ jc.toNat * n.v ^ (ic.xor (i.xor k)).toNat * n.t ^ (i.xor k).toNat * z ^ mc.toNat)
    (Rd : act f.r f.d = f.a * f.u ^ (j.xor k).toNat * n.v ^ (i.xor k).toNat * n.t ^ i.toNat * z ^ (i.xor m).toNat)
    : ic = k := by
  have Rz := act_comm f.comm_zr
  have Rt : act f.r n.t = _ := f.eq20_tr
  have Rv : act f.r n.v = _ := f.eq21_vr
  have Ru : act f.r f.u = _ := f.eq22_ur
  have Rw : act f.r f.w = _ := f.eq22_wr
  have hh := congrArg (act f.r) ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq14_cd)
  simp only [map_mul, map_pow, Rc, Rd, Rz, Rt, Rv, Ru, Rw] at hh
  collect_core f, n, z at hh using
    (cases i <;> cases j <;> cases k <;> cases m <;> cases ic <;> cases jc <;> cases mc
     all_goals first | rfl | exfalso
     all_goals simp only [Bool.toNat_false, Bool.toNat_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, pow_zero, pow_one, mul_one, pow_two] at hh)
  all_goals exact nontrivial h (by simpa using hh)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem bc_coeff (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (i j k jb mb jc mc : Bool)
    (Rb : act f.r f.b = f.d * f.c * f.b * f.w ^ (!j).toNat * f.u ^ jb.toNat * n.v ^ (jb.xor (j.xor k)).toNat * n.t ^ (j.xor k).toNat * z ^ mb.toNat)
    (Rc : act f.r f.c = f.c * f.d * f.a * f.w ^ k.toNat * f.u ^ jc.toNat * n.v ^ i.toNat * n.t ^ (i.xor k).toNat * z ^ mc.toNat)
    : jc = jb.xor (j.xor k) := by
  have Rz := act_comm f.comm_zr
  have Rt : act f.r n.t = _ := f.eq20_tr
  have Rv : act f.r n.v = _ := f.eq21_vr
  have Ru : act f.r f.u = _ := f.eq22_ur
  have Rw : act f.r f.w = _ := f.eq22_wr
  have hh := congrArg (act f.r) ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq15_bc)
  simp only [map_mul, map_pow, Rb, Rc, Rz, Rt, Rv, Ru, Rw] at hh
  collect_core f, n, z at hh using
    (cases i <;> cases j <;> cases k <;> cases jb <;> cases mb <;> cases jc <;> cases mc
     all_goals first | rfl | exfalso
     all_goals simp only [Bool.toNat_false, Bool.toNat_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, pow_zero, pow_one, mul_one, pow_two] at hh)
  all_goals exact nontrivial h (by simpa using hh)

private theorem xor_cancel_left (i j : Bool) : i.xor (i.xor j) = j := by
  cases i <;> cases j <;> rfl

/-- Squares and the six transported core commutators leave seven binary coefficients. -/
public theorem ParrottCentralizerInvolutionData.core_image_seven_coefficients
    [Finite G] (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) :
    ∃ i j k m jb mb mc : Bool,
      f.r⁻¹ * f.a * f.r = f.d * f.w ^ i.toNat * f.u ^ j.toNat * n.v ^ k.toNat * z ^ m.toNat ∧
      f.r⁻¹ * f.d * f.r = f.a * f.u ^ (j.xor k).toNat * n.v ^ (i.xor k).toNat * n.t ^ i.toNat * z ^ (i.xor m).toNat ∧
      f.r⁻¹ * f.b * f.r = f.d * f.c * f.b * f.w ^ (!j).toNat * f.u ^ jb.toNat * n.v ^ (jb.xor (j.xor k)).toNat * n.t ^ (j.xor k).toNat * z ^ mb.toNat ∧
      f.r⁻¹ * f.c * f.r = f.c * f.d * f.a * f.w ^ k.toNat * f.u ^ (jb.xor (j.xor k)).toNat * n.v ^ i.toNat * n.t ^ (i.xor k).toNat * z ^ mc.toNat := by
  obtain ⟨i, j, k, m, ib, jb, kb, lb, mb, ic, jc, kc, lc, mc,
    Ra, Rd, Rb, Rc, _⟩ := f.core_image_binary_coefficients_with_involutivity h
  change act f.r f.a = _ at Ra
  change act f.r f.d = _ at Rd
  change act f.r f.b = _ at Rb
  change act f.r f.c = _ at Rc
  have hlb := b_square_coeff f h ib jb kb lb mb Rb
  have hlc := c_square_coeff f h ic jc kc lc mc Rc
  subst lb
  subst lc
  have hab := ab_coeff f h i j k m ib jb kb mb Ra Rb
  have hkb : kb = jb.xor (j.xor k) := by
    cases jb <;> cases kb <;> cases j <;> cases k
    all_goals first | rfl | exact Bool.noConfusion hab
  subst kb
  simp only [xor_cancel_left] at Rb
  have hac := ac_coeff f h i j k m ic jc kc mc Ra Rc
  have hkc : kc = ic.xor (i.xor k) := by
    cases ic <;> cases kc <;> cases i <;> cases k
    all_goals first | rfl | exact Bool.noConfusion hac
  subst kc
  simp only [xor_cancel_left] at Rc
  have hib := db_coeff f h i j k m ib jb mb Rd Rb
  subst ib
  have hic := cd_coeff f h i j k m ic jc mc Rc Rd
  subst ic
  have hx : k.xor (i.xor k) = i := by cases i <;> cases k <;> rfl
  rw [hx] at Rc
  have hjc := bc_coeff f h i j k jb mb jc mc Rb Rc
  subst jc
  exact ⟨i, j, k, m, jb, mb, mc, Ra, Rd, Rb, Rc⟩

end Stellmacher.Recognition
