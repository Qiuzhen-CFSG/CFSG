module

public import Theory.SpecificGroups.Tits.RecognitionLocalData

/-!
# The local conjugation relations in Parrott's presentation

The local equations imply all thirteen relations in groups VI–VIII other than
the global braid relation. No finite-group or witness-existence hypothesis is
needed. The two longer s₃ calculations collect words in b,c,d,a,w,u,v,t,z:
conjugating bav by r gives bcwt, and the conjugate of bxv by s times bcwt
gives wuvz. The latter identifies s₇x through the previously proved formula
s₇r₇ = wuvz. Inversion of s₇ under s follows directly from s₇ = x⁻¹xˢ.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§§3, 5, 6, especially pp.681–684. See
`refs/original/n-group-global/parrott-tits-presentation.md` for the scan-checked
conventions and generator correspondence.
-/

namespace Tits

private theorem sqinv {G : Type*} [Group G] {a : G} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

private theorem tail {G : Type*} [Group G] {a b c : G} (h : a * b = c) (k : G) :
    a * (b * k) = c * k := by rw [← mul_assoc, h]

private theorem revswap {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) : b * a = a * b * c⁻¹ := by rw [h]; group

private theorem conjmul {G : Type*} [Group G] (g a b : G) :
    g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group

namespace ParrottLocalRelations

variable {G : Type*} [Group G] {z t v u w a b c d x y r s : G}
variable (h : ParrottLocalRelations z t v u w a b c d x y r s)
include h

-- Collect the tail of the conjugate of bxv after using equation (24).
private theorem r_tail : r⁻¹ * (b * a * v) * r = b * c * w * t := by
  simp only [conjmul, h.eq23_br, h.eq23_ar, h.eq21_vr]
  have sq_z : z * z = 1 := by simpa only [pow_two] using h.z_sq
  have sq_v : v * v = 1 := by simpa only [pow_two] using h.v_sq
  have sq_u : u * u = 1 := by simpa only [pow_two] using h.u_sq
  have sq_d : d * d = 1 := by simpa only [pow_two] using h.d_sq
  have swap_zt := h.comm_zt.eq
  have swap_zv := h.comm_zv.eq
  have swap_zu := h.comm_zu.eq
  have swap_tv := h.comm_tv.eq
  have swap_tu := h.comm_tu.eq
  have swap_vu := h.comm_vu.eq
  have swap_vw := h.comm_vw.eq
  have swap_uw := h.comm_uw.eq
  have swap_zd := h.comm_zd.eq
  have swap_bw := (parrottCommutator_eq_iff _ _ _).mp h.eq02_bw
  have swap_bw := revswap swap_bw
  simp only [inv_one, mul_one] at swap_bw
  have swap_bu := (parrottCommutator_eq_iff _ _ _).mp h.eq02_bu
  have swap_bu := revswap swap_bu
  simp only [sqinv h.z_sq] at swap_bu
  have swap_db := (parrottCommutator_eq_iff _ _ _).mp h.eq03_db
  have swap_dt := (parrottCommutator_eq_iff _ _ _).mp h.eq03_dt
  have swap_dt := revswap swap_dt
  simp only [sqinv h.z_sq] at swap_dt
  have swap_dw := (parrottCommutator_eq_iff _ _ _).mp h.eq07_dw
  have swap_dw := revswap swap_dw
  simp only [inv_one, mul_one] at swap_dw
  have swap_du := (parrottCommutator_eq_iff _ _ _).mp h.eq08_du
  have swap_du := revswap swap_du
  simp only [inv_one, mul_one] at swap_du
  have swap_cd := (parrottCommutator_eq_iff _ _ _).mp h.eq14_cd
  have swap_cd := revswap swap_cd
  simp only [mul_inv_rev, sqinv h.u_sq, sqinv h.w_sq] at swap_cd
  have swap_bc := (parrottCommutator_eq_iff _ _ _).mp h.eq15_bc
  have swap_bc := revswap swap_bc
  simp only [mul_inv_rev, sqinv h.v_sq, sqinv h.u_sq] at swap_bc
  simp only [swap_cd, swap_uw, mul_assoc, swap_bu, tail swap_bw, tail swap_db, tail swap_vw, tail swap_vu,
    tail swap_bc, swap_vu, swap_zv, tail sq_v, one_mul, swap_zt, tail swap_zd, swap_zu, tail swap_dt, tail swap_zu,
    sq_z, mul_one, swap_tu, tail swap_du, tail sq_u, tail swap_dw, tail sq_d, tail swap_uw, tail swap_tu, swap_tv]

-- Right multiplication by bcwt avoids expanding the inverse in the word s₇.
private theorem s_tail :
    ((b * a * u * v * z) * (c * a * w * t * z) * (v * t * z)) * (b * c * w * t) = w * u * v * z := by
  have swap_vb : v * b = b * v := by
    rw [← h.eq03_b]
    exact (Commute.self_pow b 2).symm.eq
  have sq_z : z * z = 1 := by simpa only [pow_two] using h.z_sq
  have sq_t : t * t = 1 := by simpa only [pow_two] using h.t_sq
  have sq_v : v * v = 1 := by simpa only [pow_two] using h.v_sq
  have sq_u : u * u = 1 := by simpa only [pow_two] using h.u_sq
  have sq_w : w * w = 1 := by simpa only [pow_two] using h.w_sq
  have sq_a : a * a = 1 := by simpa only [pow_two] using h.a_sq
  have sq_b := h.eq03_b
  simp only [pow_two] at sq_b
  have sq_c := h.eq13
  simp only [pow_two] at sq_c
  have swap_zt := h.comm_zt.eq
  have swap_zv := h.comm_zv.eq
  have swap_zu := h.comm_zu.eq
  have swap_zw := h.comm_zw.eq
  have swap_tv := h.comm_tv.eq
  have swap_tu := h.comm_tu.eq
  have swap_tw := h.comm_tw.eq
  have swap_vu := h.comm_vu.eq
  have swap_vw := h.comm_vw.eq
  have swap_uw := h.comm_uw.eq
  have swap_az := h.comm_az.symm.eq
  have swap_at := h.comm_at.symm.eq
  have swap_av := h.comm_av.symm.eq
  have swap_au := h.comm_au.symm.eq
  have swap_zc := h.comm_zc.eq
  have swap_bt := h.comm_bt.symm.eq
  have swap_bw := (parrottCommutator_eq_iff _ _ _).mp h.eq02_bw
  have swap_bw := revswap swap_bw
  simp only [inv_one, mul_one] at swap_bw
  have swap_bu := (parrottCommutator_eq_iff _ _ _).mp h.eq02_bu
  have swap_bu := revswap swap_bu
  simp only [sqinv h.z_sq] at swap_bu
  have swap_cu := (parrottCommutator_eq_iff _ _ _).mp h.eq09_cu
  have swap_cu := revswap swap_cu
  simp only [inv_one, mul_one] at swap_cu
  have swap_cw := (parrottCommutator_eq_iff _ _ _).mp h.eq09_cw
  have swap_cw := revswap swap_cw
  simp only [inv_one, mul_one] at swap_cw
  have swap_ct := (parrottCommutator_eq_iff _ _ _).mp h.eq10_ct
  have swap_ct := revswap swap_ct
  simp only [inv_one, mul_one] at swap_ct
  have swap_cv := (parrottCommutator_eq_iff _ _ _).mp h.eq10_cv
  have swap_cv := revswap swap_cv
  simp only [sqinv h.z_sq] at swap_cv
  have swap_ac := (parrottCommutator_eq_iff _ _ _).mp h.eq12_ac
  have swap_bc := (parrottCommutator_eq_iff _ _ _).mp h.eq15_bc
  have swap_bc := revswap swap_bc
  simp only [mul_inv_rev, sqinv h.v_sq, sqinv h.u_sq] at swap_bc
  simp only [mul_assoc, tail swap_zc, tail swap_az, tail swap_zw, tail swap_zt, sq_z, mul_one, tail swap_cv,
    swap_zt, tail swap_av, tail swap_vw, tail swap_cu, tail swap_au, tail swap_uw, tail swap_ac, tail swap_at,
    tail swap_tw, tail swap_tu, tail swap_tv, tail sq_t, one_mul, tail swap_vu, tail sq_v, tail sq_a, tail swap_zv,
    tail swap_bt, tail swap_ct, sq_t, tail swap_vb, swap_zw, tail swap_bu, tail swap_bw, tail swap_cw, tail sq_w,
    tail swap_bc, swap_vu, tail swap_zu, swap_zv, tail sq_u, tail sq_c, tail sq_b]

private theorem z_conj_r : r⁻¹ * z * r = z := by
  rw [mul_assoc, h.comm_zr.eq]
  simp

private theorem z_conj_s : s⁻¹ * z * s = t := by
  rw [← h.eq25_ts]
  calc
    _ = (s * s)⁻¹ * t * (s * s) := by group
    _ = t := by simp [← pow_two, h.s_sq]

private theorem r_s2 : r * (a * v * z) * r = d * v * z := by
  have uu : u * u = 1 := by simpa only [pow_two] using h.u_sq
  conv_lhs => lhs; lhs; rw [← sqinv h.eq20_r]
  simp only [conjmul, h.eq23_ar, h.eq21_vr, h.z_conj_r]
  simp only [mul_assoc, tail uu, one_mul]

private theorem r_s4 : r * (v * z) * r = u * v * z := by
  conv_lhs => lhs; lhs; rw [← sqinv h.eq20_r]
  rw [conjmul, h.eq21_vr, h.z_conj_r]

private theorem r_s3 : r * (b * x * v) * r = (y * r) ^ 2 * (x * b * c * w * t) := by
  have bx := (parrottCommutator_eq_iff _ _ _).mp h.eq18_bx
  calc
    r * (b * x * v) * r = r * (x * (b * a * v)) * r := by rw [bx]; group
    _ = (r * x * r) * (r⁻¹ * (b * a * v) * r) := by group
    _ = ((y * r) ^ 2 * x) * (b * c * w * t) := by rw [h.eq24, h.r_tail]
    _ = _ := by group

private theorem s_s2 : s * (a * v * z) * s = u * v * z := by
  have tt : t * t = 1 := by simpa only [pow_two] using h.t_sq
  conv_lhs => lhs; lhs; rw [← sqinv h.s_sq]
  simp only [conjmul, h.eq25_as, h.eq25_vs, h.z_conj_s]
  simp only [mul_assoc, h.comm_zt.eq, tail tt, one_mul]

private theorem s_s4 : s * (v * z) * s = v * z := by
  have tt : t * t = 1 := by simpa only [pow_two] using h.t_sq
  conv_lhs => lhs; lhs; rw [← sqinv h.s_sq]
  rw [conjmul, h.eq25_vs, h.z_conj_s]
  simp only [mul_assoc, h.comm_zt.eq, tail tt, one_mul]

private theorem s_s7 :
    s * (x⁻¹ * c * a * w * t * z) * s = (x⁻¹ * c * a * w * t * z)⁻¹ := by
  have word : x⁻¹ * c * a * w * t * z = x⁻¹ * (s⁻¹ * x * s) := by rw [h.eq25_xs]; group
  rw [word]
  calc
    _ = s * x⁻¹ * s⁻¹ * x * (s * s) := by group
    _ = s * x⁻¹ * s⁻¹ * x := by rw [← pow_two, h.s_sq, mul_one]
    _ = (x⁻¹ * (s⁻¹ * x * s))⁻¹ := by simp only [mul_inv_rev, inv_inv, sqinv h.s_sq, mul_assoc]

private theorem s_s3 : s * (b * x * v) * s = (x⁻¹ * c * a * w * t * z) * x := by
  apply mul_right_cancel (b := b * c * w * t)
  calc
    s * (b * x * v) * s * (b * c * w * t) =
        ((b * a * u * v * z) * (c * a * w * t * z) * (v * t * z)) * (b * c * w * t) := by
      conv_lhs => lhs; lhs; lhs; rw [← sqinv h.s_sq]
      rw [conjmul, conjmul, h.eq25_bs, h.eq25_xs, h.eq25_vs]
    _ = w * u * v * z := h.s_tail
    _ = ((x⁻¹ * c * a * w * t * z) * x) * (b * c * w * t) := by
      simpa only [mul_assoc] using h.s7_r7_word.symm

/-- The thirteen local power and conjugation relators in groups VI–VIII.
The global eighth-power braid relator is deliberately excluded. -/
public theorem relators_VI_VIII_except_braid (i : ParrottRelatorIndex)
    (hi : i ∈ [ParrottRelatorIndex.vi_s1_r1, .vi_r8_s8,
      .vii_s2, .vii_s4, .vii_s5, .vii_s3, .vii_r3,
      .viii_s2, .viii_s4, .viii_s1, .viii_s7, .viii_s3, .viii_r3]) :
    FreeGroup.lift (parrottRecognitionWords z t v u w a b c d x y r s)
      (parrottRelator i) = 1 := by
  have hs := sqinv h.s_sq
  have ry : (y * r) ^ 5 = 1 := by
    calc
      (y * r) ^ 5 = r⁻¹ * (r * y) ^ 5 * r := by
        simp only [pow_succ, pow_zero]
        group
      _ = 1 := by rw [h.eq20_ry]; group
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi <;>
    subst i
  all_goals simp only [parrottRelator, map_mul, map_pow, map_inv,
    FreeGroup.lift_apply_of]
  · exact ry
  · simpa only [parrottRecognitionWords, mul_assoc] using h.eq26
  · simpa only [parrottRecognitionWords, mul_inv_eq_one] using h.r_s2
  · simpa only [parrottRecognitionWords, mul_inv_eq_one] using h.r_s4
  · simpa only [parrottRecognitionWords, mul_inv_eq_one] using h.eq24
  · simpa only [h.r7, parrottRecognitionWords, mul_inv_eq_one] using h.r_s3
  · rw [h.r3, h.s7_mul_r7]
    exact mul_inv_eq_one.mpr h.rtr
  · simpa only [parrottRecognitionWords, mul_inv_eq_one] using h.s_s2
  · simpa only [parrottRecognitionWords, mul_inv_eq_one] using h.s_s4
  · rw [h.s7_mul_r7]
    simpa only [parrottRecognitionWords, mul_inv_eq_one, hs] using h.eq25_ys
  · simpa only [parrottRecognitionWords, mul_inv_eq_one] using h.s_s7
  · simpa only [parrottRecognitionWords, mul_inv_eq_one] using h.s_s3
  · rw [h.r3, h.r5]
    simpa only [parrottRecognitionWords, mul_inv_eq_one, hs] using h.eq25_ts

end ParrottLocalRelations
end Tits
