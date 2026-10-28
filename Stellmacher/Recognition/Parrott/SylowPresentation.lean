module

public import Stellmacher.Recognition.Parrott.LocalGeneratorData
public import Theory.SpecificGroups.Tits.FirstParabolicCoordinates

/-!
# Eight presentation generators from the actual Parrott Sylow frame

The normalized equations (1)--(19) suffice for the twenty-one Sylow
relations. The eight words recover x,a,b,c,d inside any subgroup: in
particular equation (17) recovers w without an outside Weyl actor.
Consequently they generate exactly the original Sylow subgroup.

Source: Parrott (1972), §3 and §6, pp.678--680 and684. The collection
calculation follows `Tits.ParrottLocalRelations.relators_I_V`, restricted
to the equations preceding the choice of either Weyl actor.
-/

public section
open Subgroup Tits Tits.FirstParabolicCoordinates
namespace Stellmacher.Recognition.ParrottSylowGeneratorData
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable (h : ParrottSylowGeneratorData n)

private theorem tail {p q o : G} (hp : p * q = o) (k : G) :
    p * (q * k) = o * k := by rw [← mul_assoc, hp]

private theorem sq_inv {p : G} (hp : p ^ 2 = 1) : p⁻¹ = p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)

private theorem reverse {p q o : G} (hp : p * q = q * p * o) :
    q * p = p * q * o⁻¹ := by rw [hp]; group

include h
set_option linter.unusedSimpArgs false in
private theorem y_actions :
    h.y * n.v = n.v * h.y ∧ h.y * h.u = h.u * h.y * n.t ∧ h.y * h.w = h.w * h.y * n.v := by
  have vx := reverse ((parrottCommutator_eq_iff h.x n.v n.t).mp h.eq01_xv)
  have ux := reverse ((parrottCommutator_eq_iff h.x h.u n.v).mp h.eq01_xu)
  have wx := reverse ((parrottCommutator_eq_iff h.x h.w h.u).mp h.eq01_xw)
  have tx := ((parrottCommutator_eq_one_iff h.x n.t).mp h.eq01_xt).symm.eq
  simp only [sq_inv h.t_sq, sq_inv h.v_sq, sq_inv h.u_sq] at vx ux wx
  have yy : h.y = h.x * h.x * z := by
    apply mul_right_cancel (b := z)
    simp only [mul_assoc, ← pow_two, h.z_sq, mul_one, h.eq04]
  have vv : n.v*n.v=1 := by simpa only [pow_two] using h.v_sq
  have tt : n.t*n.t=1 := by simpa only [pow_two] using h.t_sq
  have uu : h.u*h.u=1 := by simpa only [pow_two] using h.u_sq
  rw [yy]
  constructor
  · simp only [mul_assoc, tail vx, vx, tail tx, tx, tail h.comm_zv.eq,
      h.comm_zv.eq, tail tt, tt, one_mul, mul_one]
  constructor
  · simp only [mul_assoc, tail ux, ux, tail vx, vx, tail h.comm_zu.eq,
      tail h.comm_vu.eq, tail h.comm_zv.eq, tail h.comm_zt.eq,
      tail h.comm_tv.eq, h.comm_zu.eq, h.comm_zv.eq, h.comm_zt.eq,
      h.comm_tv.eq, tail vv, vv, tail tt, tt, one_mul, mul_one]
  · simp only [mul_assoc, tail wx, wx, tail ux, ux, tail h.comm_zw.eq,
      tail h.comm_uw.eq, tail h.comm_zv.eq, tail h.comm_zt.eq,
      tail h.comm_tv.eq, tail h.comm_vu.eq, h.comm_zw.eq, h.comm_zv.eq,
      h.comm_uw.eq, h.comm_vu.eq, tail vv, vv, tail uu, uu, one_mul, mul_one]

private theorem d_v : h.d * n.v = n.v * h.d := by
  have dd : h.d*h.d=1 := by simpa only [pow_two] using h.d_sq
  calc
    h.d * n.v = n.v⁻¹ * h.d := by
      rw [← h.eq03_db]
      simp only [parrottCommutator, mul_inv_rev, inv_inv, sq_inv h.d_sq]
      group
      simp only [mul_assoc, dd, one_mul, mul_one]
    _ = n.v * h.d := by rw [sq_inv h.v_sq]

-- The collection uses only equations (1)--(19); no Weyl actor is present.
set_option linter.unusedSimpArgs false in
private theorem sylow_word_relations :
    h.y ^ 2 = 1 ∧
    (h.a*n.v*z) ^ 2 = 1 ∧ (n.v*z) ^ 2 = 1 ∧ (h.u*n.v*z) ^ 2 = 1 ∧
    (h.d*n.v*z) ^ 2 = 1 ∧ (h.b*h.x*n.v) ^ 4 = 1 ∧ h.x ^ 4 = 1 ∧
    (h.x⁻¹*h.c*h.a*h.w*n.t*z) ^ 4 = 1 ∧
    parrottCommutator h.y (h.a*n.v*z) = 1 ∧
    parrottCommutator h.y (h.b*h.x*n.v) = 1 ∧ parrottCommutator h.y h.x = 1 ∧
    parrottCommutator h.y (h.u*n.v*z) = n.t ∧
    parrottCommutator h.y (h.x⁻¹*h.c*h.a*h.w*n.t*z) = (h.a*n.v*z)*n.t*z ∧
    parrottCommutator h.y (h.d*n.v*z) = (h.x⁻¹*h.c*h.a*h.w*n.t*z)^2*n.t*h.y ∧
    parrottCommutator (h.a*n.v*z) (n.v*z) = 1 ∧
    parrottCommutator (h.a*n.v*z) (h.u*n.v*z) = 1 ∧
    parrottCommutator (h.a*n.v*z) (h.d*n.v*z) = (n.v*z)*(h.u*n.v*z) ∧
    parrottCommutator (h.x⁻¹*h.c*h.a*h.w*n.t*z) (h.a*n.v*z) = (n.v*z)*z ∧
    parrottCommutator (h.x⁻¹*h.c*h.a*h.w*n.t*z) (n.v*z) = n.t*z ∧
    parrottCommutator (h.b*h.x*n.v) h.x = (h.a*n.v*z)*n.t*(n.v*z) ∧
    parrottCommutator h.x (n.v*z) = n.t := by
  have yv := (y_actions h).1
  have yu := (y_actions h).2.1
  have yw := (y_actions h).2.2
  have dv := d_v h
  have y_eq : h.y = h.x ^ 2 * z := by
    apply mul_right_cancel (b := z)
    simp only [mul_assoc, ← pow_two, h.z_sq, mul_one, h.eq04]
  have yx : h.y*h.x=h.x*h.y := by
    rw [y_eq]
    exact (((Commute.refl h.x).pow_left 2).mul_left h.comm_zx).eq
  have yt : h.y*n.t=n.t*h.y := by
    rw [y_eq]
    exact ((((parrottCommutator_eq_one_iff h.x n.t).mp h.eq01_xt).pow_left 2).mul_left h.comm_zt).eq
  have ya := (parrottCommutator_eq_one_iff h.y h.a).mp h.eq06_ya
  have byc := (parrottCommutator_eq_one_iff h.b h.y).mp h.eq18_by
  have ax := (parrottCommutator_eq_one_iff h.a h.x).mp h.eq16_ax
  have tx := ((parrottCommutator_eq_one_iff h.x n.t).mp h.eq01_xt).symm
  have bw := (parrottCommutator_eq_one_iff h.b h.w).mp h.eq02_bw
  have dw := (parrottCommutator_eq_one_iff h.d h.w).mp h.eq07_dw
  have du := (parrottCommutator_eq_one_iff h.d h.u).mp h.eq08_du
  have cu := (parrottCommutator_eq_one_iff h.c h.u).mp h.eq09_cu
  have cw := (parrottCommutator_eq_one_iff h.c h.w).mp h.eq09_cw
  have ct := (parrottCommutator_eq_one_iff h.c n.t).mp h.eq10_ct
  have bv : Commute h.b n.v := by
    rw [← h.eq03_b]
    exact Commute.self_pow h.b 2
  have vx := reverse ((parrottCommutator_eq_iff h.x n.v n.t).mp h.eq01_xv)
  have ux := reverse ((parrottCommutator_eq_iff h.x h.u n.v).mp h.eq01_xu)
  have wx := reverse ((parrottCommutator_eq_iff h.x h.w h.u).mp h.eq01_xw)
  have cx := reverse ((parrottCommutator_eq_iff h.x h.c (h.a*h.b*h.u*n.v)).mp h.eq19_xc)
  have bx := (parrottCommutator_eq_iff h.b h.x h.a).mp h.eq18_bx
  have aw := (parrottCommutator_eq_iff h.a h.w z).mp h.eq02_aw
  have wa := reverse aw
  simp only [sq_inv h.z_sq] at wa
  have ub := reverse ((parrottCommutator_eq_iff h.b h.u z).mp h.eq02_bu)
  have bd := reverse ((parrottCommutator_eq_iff h.d h.b n.v).mp h.eq03_db)
  have td := reverse ((parrottCommutator_eq_iff h.d n.t z).mp h.eq03_dt)
  have ab := (parrottCommutator_eq_iff h.a h.b n.t).mp h.eq05_ab
  have vc := reverse ((parrottCommutator_eq_iff h.c n.v z).mp h.eq10_cv)
  have ad := (parrottCommutator_eq_iff h.a h.d h.u).mp h.eq11_ad
  have ac := (parrottCommutator_eq_iff h.a h.c (n.v*n.t)).mp h.eq12_ac
  have cd := (parrottCommutator_eq_iff h.c h.d (h.w*h.u)).mp h.eq14_cd
  have bc := (parrottCommutator_eq_iff h.b h.c (h.u*n.v)).mp h.eq15_bc
  have cy := reverse ((parrottCommutator_eq_iff h.y h.c (h.a*n.t*z)).mp h.eq19_yc)
  have dy := reverse ((parrottCommutator_eq_iff h.y h.d (h.b*h.w)).mp h.eq17_yd)
  have uy := reverse yu
  have wy := reverse yw
  have zz : z*z=1 := by simpa only [pow_two] using h.z_sq
  have tt : n.t*n.t=1 := by simpa only [pow_two] using h.t_sq
  have vv : n.v*n.v=1 := by simpa only [pow_two] using h.v_sq
  have uu : h.u*h.u=1 := by simpa only [pow_two] using h.u_sq
  have ww : h.w*h.w=1 := by simpa only [pow_two] using h.w_sq
  have aa : h.a*h.a=1 := by simpa only [pow_two] using h.a_sq
  have dd : h.d*h.d=1 := by simpa only [pow_two] using h.d_sq
  have yy : h.y*h.y=1 := by simpa only [pow_two] using h.y_sq
  have bb : h.b*h.b=n.v := by simpa only [pow_two] using h.eq03_b
  have cc : h.c*h.c=h.w*h.u := by simpa only [pow_two] using h.eq13
  have xx : h.x*h.x=h.y*z := by simpa only [pow_two] using h.eq04
  have binv : h.b⁻¹ = h.b*n.v := by
    apply inv_eq_of_mul_eq_one_right
    simp only [← mul_assoc, bb, vv]
  have xinv : h.x⁻¹ = h.x*h.y*z := by
    apply inv_eq_of_mul_eq_one_right
    simp only [mul_assoc, tail xx, tail h.comm_zy.eq, tail yy, zz, one_mul]
  simp only [mul_inv_rev, sq_inv h.z_sq, sq_inv h.t_sq, sq_inv h.v_sq,
    sq_inv h.u_sq, sq_inv h.w_sq, sq_inv h.a_sq, binv] at vx ux wx cx ub bd td vc cy dy uy wy
  simp only [parrottCommutator_eq_iff, h.y_sq, h.eq01_x]
  simp only [pow_succ, pow_zero, mul_one, xinv, mul_assoc]
  simp only [mul_assoc, one_mul, mul_one, and_true, true_and,
    tail (vx), vx,
    tail (ux), ux,
    tail (wx), wx,
    tail (cx), cx,
    tail (bx), bx,
    tail (ax.eq), ax.eq,
    tail (tx.eq), tx.eq,
    tail (h.comm_zx.eq), h.comm_zx.eq,
    tail (yx), yx,
    tail (byc.eq), byc.eq,
    tail (cy), cy,
    tail (dy), dy,
    tail (ya.symm.eq), ya.symm.eq,
    tail (uy), uy,
    tail (wy), wy,
    tail (yv.symm), yv.symm,
    tail (yt.symm), yt.symm,
    tail (h.comm_zy.eq), h.comm_zy.eq,
    tail (cd), cd,
    tail (bd), bd,
    tail (ad), ad,
    tail (dw.symm.eq), dw.symm.eq,
    tail (du.symm.eq), du.symm.eq,
    tail (dv.symm), dv.symm,
    tail (td), td,
    tail (h.comm_zd.eq), h.comm_zd.eq,
    tail (bc), bc,
    tail (ac), ac,
    tail (cw.symm.eq), cw.symm.eq,
    tail (cu.symm.eq), cu.symm.eq,
    tail (vc), vc,
    tail (ct.symm.eq), ct.symm.eq,
    tail (h.comm_zc.eq), h.comm_zc.eq,
    tail (ab), ab,
    tail (bw.symm.eq), bw.symm.eq,
    tail (ub), ub,
    tail (bv.symm.eq), bv.symm.eq,
    tail (h.comm_bt.symm.eq), h.comm_bt.symm.eq,
    tail (h.comm_zb.eq), h.comm_zb.eq,
    tail wa, wa,
    tail (h.comm_au.symm.eq), h.comm_au.symm.eq,
    tail (h.comm_av.symm.eq), h.comm_av.symm.eq,
    tail (h.comm_at.symm.eq), h.comm_at.symm.eq,
    tail (h.comm_az.symm.eq), h.comm_az.symm.eq,
    tail (h.comm_uw.eq), h.comm_uw.eq,
    tail (h.comm_vw.eq), h.comm_vw.eq,
    tail (h.comm_tw.eq), h.comm_tw.eq,
    tail (h.comm_zw.eq), h.comm_zw.eq,
    tail (h.comm_vu.eq), h.comm_vu.eq,
    tail (h.comm_tu.eq), h.comm_tu.eq,
    tail (h.comm_zu.eq), h.comm_zu.eq,
    tail (h.comm_tv.eq), h.comm_tv.eq,
    tail (h.comm_zv.eq), h.comm_zv.eq,
    tail (h.comm_zt.eq), h.comm_zt.eq,
    tail (zz), zz,
    tail (tt), tt,
    tail (vv), vv,
    tail (uu), uu,
    tail (ww), ww,
    tail (aa), aa,
    tail (dd), dd,
    tail (yy), yy,
    tail (bb), bb,
    tail (cc), cc,
    tail (xx), xx]


/-- The square of the third presentation generator, in local coordinates. -/
private theorem s3_square : (h.b * h.x * n.v) ^ 2 = h.y * h.a * n.v * n.t * z := by
  have bx := (parrottCommutator_eq_iff h.b h.x h.a).mp h.eq18_bx
  have vx : n.v * h.x = h.x * n.v * n.t := by
    simpa only [sq_inv h.t_sq] using
      reverse ((parrottCommutator_eq_iff h.x n.v n.t).mp h.eq01_xv)
  have bv : Commute h.b n.v := by
    rw [← h.eq03_b]
    exact Commute.self_pow h.b 2
  have za := h.comm_az.symm
  have xx : h.x * h.x = h.y * z := by simpa only [pow_two] using h.eq04
  have vv : n.v * n.v = 1 := by simpa only [pow_two] using h.v_sq
  have bb : h.b * h.b = n.v := by simpa only [pow_two] using h.eq03_b
  have byc := (parrottCommutator_eq_one_iff h.b h.y).mp h.eq18_by
  simp only [pow_two, mul_assoc]
  simp only [tail bx, tail vx, tail bv.symm.eq,
    tail h.comm_av.symm.eq, tail h.comm_tv.eq, tail xx,
    tail vv, tail bb, tail byc.eq, tail h.comm_bt.symm.eq,
    tail h.comm_zb.eq, tail h.comm_at.symm.eq, tail za.eq,
    tail h.comm_zv.eq, tail h.comm_zt.eq, mul_assoc, one_mul,
    h.comm_zv.eq]

/-- The multiplication identity underlying the named word r₃. -/
private theorem r3_identity : h.y * (h.a * n.v * z) * (h.b * h.x * n.v) ^ 2 = n.t := by
  rw [s3_square h]
  have ya := (parrottCommutator_eq_one_iff h.y h.a).mp h.eq06_ya
  have yv : Commute h.y n.v := by
    have hxv := (parrottCommutator_eq_iff h.x n.v n.t).mp h.eq01_xv
    have hxt := (parrottCommutator_eq_one_iff h.x n.t).mp h.eq01_xt
    have hxx : Commute (h.x ^ 2) n.v := by
      change (h.x ^ 2) * n.v = n.v * (h.x ^ 2)
      have tt : n.t * n.t = 1 := by simpa only [pow_two] using h.t_sq
      simp only [pow_two, mul_assoc, hxv, tail hxv,
        tail hxt.symm.eq, tt, mul_one]
    rw [h.eq04] at hxx
    change h.y * n.v = n.v * h.y
    apply mul_right_cancel (b := z)
    simpa only [mul_assoc, h.comm_zv.eq] using hxx.eq
  have yy : h.y * h.y = 1 := by simpa only [pow_two] using h.y_sq
  have aa : h.a * h.a = 1 := by simpa only [pow_two] using h.a_sq
  have vv : n.v * n.v = 1 := by simpa only [pow_two] using h.v_sq
  have zz : z * z = 1 := by simpa only [pow_two] using h.z_sq
  simp only [mul_assoc, tail h.comm_zy.eq, tail yv.symm.eq,
    tail ya.symm.eq, tail yy, tail h.comm_az.symm.eq,
    tail h.comm_av.symm.eq, tail aa, tail h.comm_zv.eq,
    tail vv, tail h.comm_zt.eq, zz, one_mul, mul_one]

/-- The eight actual words in the original group, with the printed factor order. -/
@[expose] def sylowWords : Fin 8 → G :=
  ![h.y, h.a * n.v * z, h.b * h.x * n.v, n.v * z, h.x,
    h.u * n.v * z, h.x⁻¹ * h.c * h.a * h.w * n.t * z, h.d * n.v * z]

/-- The third named word is the supplied local involution t. -/
theorem sylowWords_r3 : r3 h.sylowWords = n.t := h.r3_identity

/-- The fifth named word is the prescribed central involution z. -/
theorem sylowWords_r5 : r5 h.sylowWords = z := by
  change h.y * h.x ^ 2 = z
  rw [h.eq04, ← mul_assoc, ← pow_two, h.y_sq, one_mul]

/-- Equations (1)--(19) imply precisely the twenty-one Sylow equations. -/
theorem sylowWords_relations : SylowRelations h.sylowWords := by
  rcases sylow_word_relations h with
    ⟨hy, h2, h4, h6, h8, h3, h5, h7,
      h12, h13, h15, h16, h17, h18, h24, h26, h28, h72, h74, h35, h54⟩
  constructor <;> (try rw [h.sylowWords_r3]) <;> (try rw [h.sylowWords_r5])
  all_goals dsimp only [sylowWords, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals assumption

/-- Recovering w from [y,d]=bw proves generation without either Weyl actor. -/
theorem sylowWords_mem_iff (L : Subgroup G) :
    (∀ i, h.sylowWords i ∈ L) ↔
      z ∈ L ∧ n.t ∈ L ∧ n.v ∈ L ∧ h.u ∈ L ∧ h.w ∈ L ∧
        h.a ∈ L ∧ h.b ∈ L ∧ h.c ∈ L ∧ h.d ∈ L ∧ h.x ∈ L ∧ h.y ∈ L := by
  constructor
  · intro hg
    have hy : h.y ∈ L := hg 0
    have hx : h.x ∈ L := hg 4
    have hz : z ∈ L := by
      rw [← h.sylowWords_r5]
      exact L.mul_mem (hg 0) (L.pow_mem (hg 4) 2)
    have hv : n.v ∈ L := (L.mul_mem_cancel_right hz).mp (hg 3)
    have ha : h.a ∈ L := (L.mul_mem_cancel_right hv).mp
      ((L.mul_mem_cancel_right hz).mp (hg 1))
    have hu : h.u ∈ L := (L.mul_mem_cancel_right hv).mp
      ((L.mul_mem_cancel_right hz).mp (hg 5))
    have hd : h.d ∈ L := (L.mul_mem_cancel_right hv).mp
      ((L.mul_mem_cancel_right hz).mp (hg 7))
    have hb : h.b ∈ L := (L.mul_mem_cancel_right hx).mp
      ((L.mul_mem_cancel_right hv).mp (hg 2))
    have ht : n.t ∈ L := by
      rw [← h.sylowWords_r3]
      exact L.mul_mem (L.mul_mem (hg 0) (hg 1)) (L.pow_mem (hg 2) 2)
    have hw : h.w ∈ L := by
      apply (L.mul_mem_cancel_left hb).mp
      rw [← h.eq17_yd]
      exact L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hy) (L.inv_mem hd)) hy) hd
    have hc : h.c ∈ L := (L.mul_mem_cancel_left (L.inv_mem hx)).mp
      ((L.mul_mem_cancel_right ha).mp ((L.mul_mem_cancel_right hw).mp
        ((L.mul_mem_cancel_right ht).mp ((L.mul_mem_cancel_right hz).mp (hg 6)))))
    exact ⟨hz, ht, hv, hu, hw, ha, hb, hc, hd, hx, hy⟩
  · rintro ⟨hz, ht, hv, hu, hw, ha, hb, hc, hd, hx, hy⟩ i
    fin_cases i <;> dsimp only [sylowWords, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    all_goals repeat first | assumption | apply L.mul_mem | apply L.inv_mem

/-- The eight words generate the supplied Sylow subgroup in the ambient group. -/
theorem sylowWords_closure : closure (Set.range h.sylowWords) = e.sylow := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact (h.sylowWords_mem_iff e.sylow).mpr h.local_mem_sylow i
  · rw [← h.sylow_generators]
    apply (closure_le _).mpr
    have hh := (h.sylowWords_mem_iff (closure (Set.range h.sylowWords))).mp
      (fun i => subset_closure ⟨i, rfl⟩)
    rintro g (rfl | rfl | rfl | rfl | rfl) <;> tauto

/-- The same eight words as elements of the actual Sylow subgroup. -/
@[expose] def sylowTuple : Fin 8 → (e.sylow : Subgroup G) := fun i =>
  ⟨h.sylowWords i, (h.sylowWords_mem_iff e.sylow).mpr h.local_mem_sylow i⟩

/-- The equations hold inside that Sylow subgroup. -/
theorem sylowTuple_relations : SylowRelations h.sylowTuple := by
  constructor
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s1_sq
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s2_sq
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s4_sq
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s6_sq
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s8_sq
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s3_four
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s5_four
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s7_four
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s1_s2
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s1_s3
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s1_s5
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s1_s6
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s1_s7
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s1_s8
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s2_s4
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s2_s6
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s2_s8
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s7_s2
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s7_s4
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s3_s5
  · apply (e.sylow : Subgroup G).subtype_injective
    simpa only [sylowTuple, parrottCommutator, r3, r5, map_mul, map_inv, map_pow, map_one, Subgroup.subtype_apply]
      using h.sylowWords_relations.s5_s4

/-- Generation is proved inside the original Sylow, not only in the ambient group. -/
theorem sylowTuple_generates : closure (Set.range h.sylowTuple) = ⊤ := by
  apply map_injective (e.sylow : Subgroup G).subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype]
  have himage : (e.sylow : Subgroup G).subtype '' Set.range h.sylowTuple =
      Set.range h.sylowWords := by
    ext g
    constructor
    · rintro ⟨s, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨h.sylowTuple i, ⟨i, rfl⟩, rfl⟩
  rw [himage, h.sylowWords_closure]

/-- Construct the requested Sylow coordinates from the normalized source frame. -/
@[expose] def sylowCoordinates : SylowCoordinates (e.sylow : Subgroup G) where
  s := h.sylowTuple
  relations := h.sylowTuple_relations
  generates := h.sylowTuple_generates

end Stellmacher.Recognition.ParrottSylowGeneratorData
