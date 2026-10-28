module

public import Theory.SpecificGroups.Tits.RecognitionWords
public import Mathlib.Tactic.Group

/-!
# Local equations in Parrott's recognition argument

This module separates the word algebra in §6 from the existence of the local
configuration constructed in §§1–3. The supplied elements satisfy the unprimed
Case 1 equations (1)–(26), printed pp.678–682, together with the elementary
relations for E = ⟨z,t,v,u,w⟩ and F = ⟨z,t,v,u,a⟩. The scalar equations below
express exponent dividing two and pairwise commutation; no independence or
cardinality of these generating sets is needed for the word calculations.

Commutators mean a⁻¹b⁻¹ab, and conjugation x^g means g⁻¹xg. In particular,
(23) uses b^r = dcbvt, not dc b v; (25) uses v^s = vtz and c^s = xyauvt;
and the exponent in (26) is three. These were checked against the printed
scans, not the PDF's erroneous text layer.

The additional centrality relations come from H = C_G(z), with
z,t,v in Z(B), as described on p.674. The squares of y,d,s are from their
choice as involutions. No presentation relator, nor the global relation
(rs)^8 = 1, is an input. Equations (24) and (26) are recorded here because
they are explicitly established local source equations.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§§1–3, especially pp.674–675 and 678–682. The generator correspondence
is on p.684. See refs/original/n-group-global/parrott-tits-presentation.md.
-/

namespace Tits

/-- Precisely the elementary and source relations used for local word algebra.
The fields named eqNN follow the unprimed equations in §3. The structure makes
no assertion that witnesses exist; the recognition argument must construct them.
All orders are expressed as power equations, so the interface also permits
quotients and does not assume any generator is nontrivial. -/
public structure ParrottLocalRelations {G : Type*} [Group G]
    (z t v u w a b c d x y r s : G) : Prop where
  /-- Elementary relations for E and F. -/
  z_sq : z ^ 2 = 1
  /-- Elementary relations for E and F. -/
  t_sq : t ^ 2 = 1
  /-- Elementary relations for E and F. -/
  v_sq : v ^ 2 = 1
  /-- Elementary relations for E and F. -/
  u_sq : u ^ 2 = 1
  /-- Elementary relations for E and F. -/
  w_sq : w ^ 2 = 1
  /-- Elementary relations for E and F. -/
  a_sq : a ^ 2 = 1
  /-- Pairwise commutation in E or F. -/
  comm_zt : Commute z t
  /-- Pairwise commutation in E or F. -/
  comm_zv : Commute z v
  /-- Pairwise commutation in E or F. -/
  comm_zu : Commute z u
  /-- Pairwise commutation in E or F. -/
  comm_zw : Commute z w
  /-- Pairwise commutation in E or F. -/
  comm_tv : Commute t v
  /-- Pairwise commutation in E or F. -/
  comm_tu : Commute t u
  /-- Pairwise commutation in E or F. -/
  comm_tw : Commute t w
  /-- Pairwise commutation in E or F. -/
  comm_vu : Commute v u
  /-- Pairwise commutation in E or F. -/
  comm_vw : Commute v w
  /-- Pairwise commutation in E or F. -/
  comm_uw : Commute u w
  /-- Pairwise commutation in E or F. -/
  comm_az : Commute a z
  /-- Pairwise commutation in E or F. -/
  comm_at : Commute a t
  /-- Pairwise commutation in E or F. -/
  comm_av : Commute a v
  /-- Pairwise commutation in E or F. -/
  comm_au : Commute a u
  /-- The supplied element lies in H = C_G(z). -/
  comm_zb : Commute z b
  /-- The supplied element lies in H = C_G(z). -/
  comm_zc : Commute z c
  /-- The supplied element lies in H = C_G(z). -/
  comm_zd : Commute z d
  /-- The supplied element lies in H = C_G(z). -/
  comm_zx : Commute z x
  /-- The supplied element lies in H = C_G(z). -/
  comm_zy : Commute z y
  /-- The supplied element lies in H = C_G(z). -/
  comm_zr : Commute z r
  /-- The element t belongs to Z(B), p.674. -/
  comm_bt : Commute b t
  /-- The source chooses this element to be an involution. -/
  y_sq : y ^ 2 = 1
  /-- The source chooses this element to be an involution. -/
  d_sq : d ^ 2 = 1
  /-- The source chooses this element to be an involution. -/
  s_sq : s ^ 2 = 1
  /-- Equation (1). -/
  eq01_x : x ^ 4 = 1
  /-- Equation (1); inverse-first commutator. -/
  eq01_xt : parrottCommutator x t = 1
  /-- Equation (1); inverse-first commutator. -/
  eq01_xv : parrottCommutator x v = t
  /-- Equation (1); inverse-first commutator. -/
  eq01_xu : parrottCommutator x u = v
  /-- Equation (1); inverse-first commutator. -/
  eq01_xw : parrottCommutator x w = u
  /-- Equation (2); inverse-first commutator. -/
  eq02_bw : parrottCommutator b w = 1
  /-- Equation (2); inverse-first commutator. -/
  eq02_aw : parrottCommutator a w = z
  /-- Equation (2); inverse-first commutator. -/
  eq02_bu : parrottCommutator b u = z
  /-- Equation (3); inverse-first commutator. -/
  eq03_db : parrottCommutator d b = v
  /-- Equation (3); inverse-first commutator. -/
  eq03_dt : parrottCommutator d t = z
  /-- Equation (5); inverse-first commutator. -/
  eq05_ab : parrottCommutator a b = t
  /-- Equation (6); inverse-first commutator. -/
  eq06_ya : parrottCommutator y a = 1
  /-- Equation (7); inverse-first commutator. -/
  eq07_dw : parrottCommutator d w = 1
  /-- Equation (8); inverse-first commutator. -/
  eq08_du : parrottCommutator d u = 1
  /-- Equation (9); inverse-first commutator. -/
  eq09_cu : parrottCommutator c u = 1
  /-- Equation (9); inverse-first commutator. -/
  eq09_cw : parrottCommutator c w = 1
  /-- Equation (10); inverse-first commutator. -/
  eq10_ct : parrottCommutator c t = 1
  /-- Equation (10); inverse-first commutator. -/
  eq10_cv : parrottCommutator c v = z
  /-- Equation (11); inverse-first commutator. -/
  eq11_ad : parrottCommutator a d = u
  /-- Equation (12); inverse-first commutator. -/
  eq12_ac : parrottCommutator a c = v * t
  /-- Equation (14); inverse-first commutator. -/
  eq14_cd : parrottCommutator c d = w * u
  /-- Equation (15); inverse-first commutator. -/
  eq15_bc : parrottCommutator b c = u * v
  /-- Equation (16); inverse-first commutator. -/
  eq16_ax : parrottCommutator a x = 1
  /-- Equation (17); inverse-first commutator. -/
  eq17_yd : parrottCommutator y d = b * w
  /-- Equation (18); inverse-first commutator. -/
  eq18_bx : parrottCommutator b x = a
  /-- Equation (18); inverse-first commutator. -/
  eq18_by : parrottCommutator b y = 1
  /-- Equation (19); inverse-first commutator. -/
  eq19_yc : parrottCommutator y c = a * t * z
  /-- Equation (19); inverse-first commutator. -/
  eq19_xc : parrottCommutator x c = a * b * u * v
  /-- Equation (19); inverse-first commutator. -/
  eq19_xd : parrottCommutator x d = a * b * c * u * v
  /-- Equation (3). -/
  eq03_b : b ^ 2 = v
  /-- Equation (4). -/
  eq04 : x ^ 2 = y * z
  /-- Equation (13), unprimed Case 1. -/
  eq13 : c ^ 2 = w * u
  /-- Equation (20). -/
  eq20_r : r ^ 2 = 1
  /-- Equation (20), with the printed order ry. -/
  eq20_ry : (r * y) ^ 5 = 1
  /-- Equation (20); conjugation is inverse on the left. -/
  eq20_tr : r⁻¹ * t * r = w * u * v * z
  /-- Equation (21); conjugation is inverse on the left. -/
  eq21_vr : r⁻¹ * v * r = u * v
  /-- Equation (22); conjugation is inverse on the left. -/
  eq22_ur : r⁻¹ * u * r = u
  /-- Equation (22); conjugation is inverse on the left. -/
  eq22_wr : r⁻¹ * w * r = v * t * z
  /-- Equation (23); conjugation is inverse on the left. -/
  eq23_ar : r⁻¹ * a * r = d * u
  /-- Equation (23); conjugation is inverse on the left. -/
  eq23_dr : r⁻¹ * d * r = a * u
  /-- Equation (23); conjugation is inverse on the left. -/
  eq23_cr : r⁻¹ * c * r = c * d * a * u
  /-- Equation (23); conjugation is inverse on the left. -/
  eq23_br : r⁻¹ * b * r = d * c * b * v * t
  /-- Equation (25); conjugation is inverse on the left. -/
  eq25_ts : s⁻¹ * t * s = z
  /-- Equation (25); conjugation is inverse on the left. -/
  eq25_vs : s⁻¹ * v * s = v * t * z
  /-- Equation (25); conjugation is inverse on the left. -/
  eq25_ys : s⁻¹ * y * s = w * u * v * z
  /-- Equation (25); conjugation is inverse on the left. -/
  eq25_ws : s⁻¹ * w * s = y * a * v * z
  /-- Equation (25); conjugation is inverse on the left. -/
  eq25_as : s⁻¹ * a * s = u
  /-- Equation (25); conjugation is inverse on the left. -/
  eq25_bs : s⁻¹ * b * s = b * a * u * v * z
  /-- Equation (25); conjugation is inverse on the left. -/
  eq25_cs : s⁻¹ * c * s = x * y * a * u * v * t
  /-- Equation (25); conjugation is inverse on the left. -/
  eq25_xs : s⁻¹ * x * s = c * a * w * t * z
  /-- Equation (24), as printed. -/
  eq24 : r * x * r = (y * r) ^ 2 * x
  /-- Equation (26), as printed; the exponent is three. -/
  eq26 : (s * d * v * z) ^ 3 = 1

/-- An inverse-first commutator equation expressed as a multiplication rule. -/
public theorem parrottCommutator_eq_iff {G : Type*} [Group G] (a b c : G) :
    parrottCommutator a b = c ↔ a * b = b * a * c := by
  constructor
  · intro h
    calc
      a * b = b * a * parrottCommutator a b := by
        simp only [parrottCommutator]
        group
      _ = b * a * c := by rw [h]
  · intro h
    calc
      parrottCommutator a b = a⁻¹ * b⁻¹ * (a * b) := by
        simp only [parrottCommutator, mul_assoc]
      _ = c := by rw [h]; group

/-- In this convention, a trivial commutator is precisely commutation. -/
public theorem parrottCommutator_eq_one_iff {G : Type*} [Group G] (a b : G) :
    parrottCommutator a b = 1 ↔ Commute a b := by
  simpa only [mul_one, Commute, SemiconjBy] using parrottCommutator_eq_iff a b 1

private theorem parrott_reverse_swap {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) : b * a = a * b * c⁻¹ := by
  rw [h]
  group

private theorem parrott_square_inv {G : Type*} [Group G] {a : G}
    (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

private theorem parrott_tail_rule {G : Type*} [Group G] {a b c : G}
    (h : a * b = c) (k : G) : a * (b * k) = c * k := by rw [← mul_assoc, h]

namespace ParrottLocalRelations

variable {G : Type*} [Group G] {z t v u w a b c d x y r s : G}
variable (h : ParrottLocalRelations z t v u w a b c d x y r s)
include h

/-- The local equations recover the prescribed involution as the named word r₅. -/
public theorem r5 :
    FreeGroup.lift (parrottRecognitionWords z t v u w a b c d x y r s)
      parrottR5 = z :=
  parrottRecognitionWords_r5 z t v u w a b c d x y r s h.y_sq h.eq04

/-- The anchor used by the recognition homomorphism is z. -/
public theorem anchor :
    parrottRecognitionWords z t v u w a b c d x y r s .s1 *
      (parrottRecognitionWords z t v u w a b c d x y r s .s5) ^ 2 = z :=
  parrottRecognitionWords_anchor z t v u w a b c d x y r s h.y_sq h.eq04

/-- The involutory conjugator r converts equation (20) to the printed product. -/
public theorem rtr : r * t * r = w * u * v * z := by
  have hr : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h.eq20_r)
  simpa only [hr] using h.eq20_tr

/-- The square of the third presentation generator, in local coordinates. -/
public theorem s3_sq : (b * x * v) ^ 2 = y * a * v * t * z := by
  have bx := (parrottCommutator_eq_iff b x a).mp h.eq18_bx
  have vx : v * x = x * v * t := by
    simpa only [parrott_square_inv h.t_sq] using
      parrott_reverse_swap ((parrottCommutator_eq_iff x v t).mp h.eq01_xv)
  have bv : Commute b v := by
    rw [← h.eq03_b]
    exact Commute.self_pow b 2
  have za := h.comm_az.symm
  have xx : x * x = y * z := by simpa only [pow_two] using h.eq04
  have vv : v * v = 1 := by simpa only [pow_two] using h.v_sq
  have bb : b * b = v := by simpa only [pow_two] using h.eq03_b
  have byc := (parrottCommutator_eq_one_iff b y).mp h.eq18_by
  simp only [pow_two, mul_assoc]
  simp only [parrott_tail_rule bx, parrott_tail_rule vx, parrott_tail_rule bv.symm.eq,
    parrott_tail_rule h.comm_av.symm.eq, parrott_tail_rule h.comm_tv.eq, parrott_tail_rule xx,
    parrott_tail_rule vv, parrott_tail_rule bb, parrott_tail_rule byc.eq, parrott_tail_rule h.comm_bt.symm.eq,
    parrott_tail_rule h.comm_zb.eq, parrott_tail_rule h.comm_at.symm.eq, parrott_tail_rule za.eq,
    parrott_tail_rule h.comm_zv.eq, parrott_tail_rule h.comm_zt.eq, mul_assoc, one_mul,
    h.comm_zv.eq]

/-- The multiplication identity underlying the named word r₃. -/
public theorem r3_word : y * (a * v * z) * (b * x * v) ^ 2 = t := by
  rw [s3_sq h]
  have ya := (parrottCommutator_eq_one_iff y a).mp h.eq06_ya
  have yv : Commute y v := by
    have hxv := (parrottCommutator_eq_iff x v t).mp h.eq01_xv
    have hxt := (parrottCommutator_eq_one_iff x t).mp h.eq01_xt
    have hxx : Commute (x ^ 2) v := by
      change (x ^ 2) * v = v * (x ^ 2)
      have tt : t * t = 1 := by simpa only [pow_two] using h.t_sq
      simp only [pow_two, mul_assoc, hxv, parrott_tail_rule hxv,
        parrott_tail_rule hxt.symm.eq, tt, mul_one]
    rw [h.eq04] at hxx
    change y * v = v * y
    apply mul_right_cancel (b := z)
    simpa only [mul_assoc, h.comm_zv.eq] using hxx.eq
  have yy : y * y = 1 := by simpa only [pow_two] using h.y_sq
  have aa : a * a = 1 := by simpa only [pow_two] using h.a_sq
  have vv : v * v = 1 := by simpa only [pow_two] using h.v_sq
  have zz : z * z = 1 := by simpa only [pow_two] using h.z_sq
  simp only [mul_assoc, parrott_tail_rule h.comm_zy.eq, parrott_tail_rule yv.symm.eq,
    parrott_tail_rule ya.symm.eq, parrott_tail_rule yy, parrott_tail_rule h.comm_az.symm.eq,
    parrott_tail_rule h.comm_av.symm.eq, parrott_tail_rule aa, parrott_tail_rule h.comm_zv.eq,
    parrott_tail_rule vv, parrott_tail_rule h.comm_zt.eq, zz, one_mul, mul_one]

/-- Evaluating the named free-group word r₃ gives the local involution t. -/
public theorem r3 :
    FreeGroup.lift (parrottRecognitionWords z t v u w a b c d x y r s)
      parrottR3 = t := by
  simpa only [parrottR3, map_mul, map_pow, FreeGroup.lift_apply_of,
    parrottRecognitionWords] using h.r3_word

/-- Every local generator is recovered inside any subgroup containing the ten
presentation words, and conversely. -/
public theorem mem_iff (L : Subgroup G) :
    (∀ i, parrottRecognitionWords z t v u w a b c d x y r s i ∈ L) ↔
      z ∈ L ∧ t ∈ L ∧ v ∈ L ∧ u ∈ L ∧ w ∈ L ∧ a ∈ L ∧ b ∈ L ∧
        c ∈ L ∧ d ∈ L ∧ x ∈ L ∧ y ∈ L ∧ r ∈ L ∧ s ∈ L :=
  parrottRecognitionWords_mem_iff L z t v u w a b c d x y r s
    h.y_sq h.eq04 h.r3_word h.rtr

/-- The multiplication identity underlying the named word r₇, in printed factor order. -/
public theorem r7_word : t * (b * x * v) * x * (x⁻¹ * c * a * w * t * z) = x * b * c * w * t := by
  have bx := (parrottCommutator_eq_iff b x a).mp h.eq18_bx
  have ac := (parrottCommutator_eq_iff a c (v * t)).mp h.eq12_ac
  have vc : v * c = c * v * z := by
    simpa only [parrott_square_inv h.z_sq] using
      parrott_reverse_swap ((parrottCommutator_eq_iff c v z).mp h.eq10_cv)
  have tx := ((parrottCommutator_eq_one_iff x t).mp h.eq01_xt).symm
  have tc := ((parrottCommutator_eq_one_iff c t).mp h.eq10_ct).symm
  have aa : a * a = 1 := by simpa only [pow_two] using h.a_sq
  have vv : v * v = 1 := by simpa only [pow_two] using h.v_sq
  have tt : t * t = 1 := by simpa only [pow_two] using h.t_sq
  have zz : z * z = 1 := by simpa only [pow_two] using h.z_sq
  simp only [mul_assoc, mul_inv_cancel_left]
  simp only [parrott_tail_rule bx, parrott_tail_rule ac, parrott_tail_rule vc, parrott_tail_rule h.comm_bt.symm.eq,
    parrott_tail_rule tx.eq, parrott_tail_rule h.comm_tv.eq, parrott_tail_rule tc.eq,
    parrott_tail_rule h.comm_at.symm.eq, parrott_tail_rule h.comm_av.symm.eq,
    parrott_tail_rule h.comm_az.symm.eq, parrott_tail_rule h.comm_tw.eq, parrott_tail_rule h.comm_zw.eq,
    parrott_tail_rule h.comm_zt.eq, parrott_tail_rule vv, parrott_tail_rule aa, parrott_tail_rule tt, zz,
    mul_assoc, one_mul, mul_one]

/-- Evaluating the named word r₇ gives xbcwt, with exactly the source factor order. -/
public theorem r7 :
    FreeGroup.lift (parrottRecognitionWords z t v u w a b c d x y r s)
      parrottR7 = x * b * c * w * t := by
  simp only [parrottR7, map_mul, h.r3, FreeGroup.lift_apply_of,
    parrottRecognitionWords]
  exact h.r7_word

/-- The product s₇r₇ reduces to wuvz in the printed factor order. -/
public theorem s7_r7_word : (x⁻¹ * c * a * w * t * z) * (x * b * c * w * t) = w * u * v * z := by
  have cx := parrott_reverse_swap ((parrottCommutator_eq_iff x c (a*b*u*v)).mp h.eq19_xc)
  have wx := parrott_reverse_swap ((parrottCommutator_eq_iff x w u).mp h.eq01_xw)
  have ax := (parrottCommutator_eq_one_iff a x).mp h.eq16_ax
  have tx := ((parrottCommutator_eq_one_iff x t).mp h.eq01_xt).symm
  have bw := (parrottCommutator_eq_one_iff b w).mp h.eq02_bw
  have ub := parrott_reverse_swap ((parrottCommutator_eq_iff b u z).mp h.eq02_bu)
  have uc := ((parrottCommutator_eq_one_iff c u).mp h.eq09_cu).symm
  have wc := ((parrottCommutator_eq_one_iff c w).mp h.eq09_cw).symm
  have tc := ((parrottCommutator_eq_one_iff c t).mp h.eq10_ct).symm
  have vc := parrott_reverse_swap ((parrottCommutator_eq_iff c v z).mp h.eq10_cv)
  have aa : a*a = 1 := by simpa [pow_two] using h.a_sq
  have uu : u*u = 1 := by simpa [pow_two] using h.u_sq
  have ww : w*w = 1 := by simpa [pow_two] using h.w_sq
  have tt : t*t = 1 := by simpa [pow_two] using h.t_sq
  have zz : z*z = 1 := by simpa [pow_two] using h.z_sq
  have cc : c*c = w*u := by simpa [pow_two] using h.eq13
  simp only [parrott_square_inv h.u_sq] at wx
  simp only [mul_inv_rev, parrott_square_inv h.v_sq, parrott_square_inv h.u_sq, parrott_square_inv h.a_sq] at cx
  simp only [parrott_square_inv h.z_sq] at ub vc
  simp only [mul_assoc, parrott_tail_rule h.comm_zx.eq, parrott_tail_rule tx.eq, parrott_tail_rule wx,
    parrott_tail_rule ax.eq, parrott_tail_rule cx, parrott_tail_rule aa, one_mul, inv_mul_cancel_left]
  simp only [mul_assoc, parrott_tail_rule h.comm_zb.eq, parrott_tail_rule h.comm_bt.symm.eq,
    parrott_tail_rule ub, parrott_tail_rule bw.symm.eq, inv_mul_cancel_left,
    parrott_tail_rule h.comm_uw.symm.eq, parrott_tail_rule h.comm_vw.symm.eq,
    parrott_tail_rule h.comm_vu.symm.eq, parrott_tail_rule uu, parrott_tail_rule h.comm_zt.eq,
    parrott_tail_rule h.comm_zc.eq, parrott_tail_rule tc.eq, parrott_tail_rule vc, parrott_tail_rule uc.eq,
    parrott_tail_rule wc.eq, parrott_tail_rule cc, one_mul]
  simp only [mul_assoc, parrott_tail_rule h.comm_zw.eq, parrott_tail_rule h.comm_tw.eq,
    h.comm_zw.eq, parrott_tail_rule ww, parrott_tail_rule zz, tt, one_mul, mul_one]
/-- The evaluation of s₇r₇, used in both conjugation blocks of the presentation. -/
public theorem s7_mul_r7 :
    parrottRecognitionWords z t v u w a b c d x y r s .s7 *
      FreeGroup.lift (parrottRecognitionWords z t v u w a b c d x y r s)
        parrottR7 = w * u * v * z := by
  rw [h.r7]
  exact h.s7_r7_word

end ParrottLocalRelations
end Tits
