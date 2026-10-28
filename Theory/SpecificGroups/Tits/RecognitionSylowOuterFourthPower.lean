module

public import Theory.SpecificGroups.Tits.RecognitionSylowSeed

/-!
# The fourth-power obstruction in Parrott's outer action

In the unprimed coordinates, assume that a commutes with x and that the three
outer conjugates have the prescribed elementary tails. If the v-coordinate
of the tail of b is zero, conjugating twice fixes b. Otherwise, collecting
four successive conjugates of d gives either dt or dz. Since x⁴ = 1, this
forces t = 1 or z = 1; the former also forces z = 1 by [d,t] = z.

The collection keeps the central z-parameters and fixed t-parameters symbolic
and checks the remaining three Boolean parameters. Each iterate is collected
before applying the next conjugation. No construction of the parameters or
additional outer commutator equation is needed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–680, especially the assertion immediately after (16).
-/

namespace Tits.ParrottSylowSeedRelations
variable {G : Type*} [Group G] {z t v u w a b c d x : G}
private theorem sqinv {p : G} (hp : p^2=1) : p⁻¹=p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem reverse {p q r : G} (h : p*q=q*p*r) : q*p=p*q*r⁻¹ := by rw [h]; group
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
private theorem fourth_power_obstruction (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (F : G →* G) (fz : F z = z) (ft : F t = t) (fv : F v = v*t)
    (fu : F u = u*v) (fw : F w = w*u) (fa : F a = a)
    (bi bj ci cj ck di dj dk : Bool)
    (fb : F b = b*a*z^bi.toNat*t^bj.toNat*v)
    (fc : F c = c*(a*b*u*v)⁻¹*z^ci.toNat*t^cj.toNat*(u*v)^ck.toNat)
    (fd : F d = d*(a*b*c*u*v)⁻¹*z^di.toNat*(t*u)^dj.toNat*(v*u)^dk.toNat)
    (fd4 : F (F (F (F d))) = d) : z = 1 ∨ t = 1 := by
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
  have tb := h.comm_bt.symm.eq
  have wb := ((parrottCommutator_eq_one_iff _ _).mp h.eq02_bw).symm.eq
  have wd := ((parrottCommutator_eq_one_iff _ _).mp h.eq07_dw).symm.eq
  have ud := ((parrottCommutator_eq_one_iff _ _).mp h.eq08_du).symm.eq
  have uc := ((parrottCommutator_eq_one_iff _ _).mp h.eq09_cu).symm.eq
  have wc := ((parrottCommutator_eq_one_iff _ _).mp h.eq09_cw).symm.eq
  have tc := ((parrottCommutator_eq_one_iff _ _).mp h.eq10_ct).symm.eq
  have wa := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_aw)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq,
    sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at wa
  have ub := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_bu)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq,
    sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ub
  have bd := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_db)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq,
    sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bd
  have td := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_dt)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq,
    sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at td
  have ab := ((parrottCommutator_eq_iff _ _ _).mp h.eq05_ab)
  have vc := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq10_cv)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq,
    sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at vc
  have ad := ((parrottCommutator_eq_iff _ _ _).mp h.eq11_ad)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq,
    sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ad
  have ac := ((parrottCommutator_eq_iff _ _ _).mp h.eq12_ac)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq,
    sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at ac
  have cd := ((parrottCommutator_eq_iff _ _ _).mp h.eq14_cd)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq,
    sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at cd
  have bc := ((parrottCommutator_eq_iff _ _ _).mp h.eq15_bc)
  simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, sqinv h.z_sq,
    sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq] at bc
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
  have biz := ((Commute.refl z).pow_left bi.toNat).eq
  have bit := ((h.comm_zt).pow_left bi.toNat).eq
  have biv := ((h.comm_zv).pow_left bi.toNat).eq
  have biu := ((h.comm_zu).pow_left bi.toNat).eq
  have biw := ((h.comm_zw).pow_left bi.toNat).eq
  have bib := ((h.comm_zb).pow_left bi.toNat).eq
  have bic := ((h.comm_zc).pow_left bi.toNat).eq
  have bid := ((h.comm_zd).pow_left bi.toNat).eq
  have bia := ((h.comm_az.symm).pow_left bi.toNat).eq
  have bisq : z^bi.toNat * z^bi.toNat = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm bi.toNat 2, pow_mul, h.z_sq, one_pow]
  have biinv : (z^bi.toNat)⁻¹ = z^bi.toNat := inv_eq_of_mul_eq_one_right bisq
  have ciz := ((Commute.refl z).pow_left ci.toNat).eq
  have cit := ((h.comm_zt).pow_left ci.toNat).eq
  have civ := ((h.comm_zv).pow_left ci.toNat).eq
  have ciu := ((h.comm_zu).pow_left ci.toNat).eq
  have ciw := ((h.comm_zw).pow_left ci.toNat).eq
  have cib := ((h.comm_zb).pow_left ci.toNat).eq
  have cic := ((h.comm_zc).pow_left ci.toNat).eq
  have cid := ((h.comm_zd).pow_left ci.toNat).eq
  have cia := ((h.comm_az.symm).pow_left ci.toNat).eq
  have cisq : z^ci.toNat * z^ci.toNat = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm ci.toNat 2, pow_mul, h.z_sq, one_pow]
  have ciinv : (z^ci.toNat)⁻¹ = z^ci.toNat := inv_eq_of_mul_eq_one_right cisq
  have diz := ((Commute.refl z).pow_left di.toNat).eq
  have dit := ((h.comm_zt).pow_left di.toNat).eq
  have div := ((h.comm_zv).pow_left di.toNat).eq
  have diu := ((h.comm_zu).pow_left di.toNat).eq
  have diw := ((h.comm_zw).pow_left di.toNat).eq
  have dib := ((h.comm_zb).pow_left di.toNat).eq
  have dic := ((h.comm_zc).pow_left di.toNat).eq
  have did := ((h.comm_zd).pow_left di.toNat).eq
  have dia := ((h.comm_az.symm).pow_left di.toNat).eq
  have disq : z^di.toNat * z^di.toNat = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm di.toNat 2, pow_mul, h.z_sq, one_pow]
  have diinv : (z^di.toNat)⁻¹ = z^di.toNat := inv_eq_of_mul_eq_one_right disq
  have bici := (((Commute.refl z).pow_left bi.toNat).pow_right ci.toNat).eq
  have bidi := (((Commute.refl z).pow_left bi.toNat).pow_right di.toNat).eq
  have cidi := (((Commute.refl z).pow_left ci.toNat).pow_right di.toNat).eq
  have bjz := ((h.comm_zt.symm).pow_left bj.toNat).eq
  have bjt := ((Commute.refl t).pow_left bj.toNat).eq
  have bjv := ((h.comm_tv).pow_left bj.toNat).eq
  have bju := ((h.comm_tu).pow_left bj.toNat).eq
  have bjw := ((h.comm_tw).pow_left bj.toNat).eq
  have bja := ((h.comm_at.symm).pow_left bj.toNat).eq
  have bjb := ((h.comm_bt.symm).pow_left bj.toNat).eq
  have bjc := ((((parrottCommutator_eq_one_iff _ _).mp h.eq10_ct).symm).pow_left bj.toNat).eq
  have bjbi := ((h.comm_zt.symm.pow_left bj.toNat).pow_right bi.toNat).eq
  have bjci := ((h.comm_zt.symm.pow_left bj.toNat).pow_right ci.toNat).eq
  have bjdi := ((h.comm_zt.symm.pow_left bj.toNat).pow_right di.toNat).eq
  have bjsq : t^bj.toNat * t^bj.toNat = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm bj.toNat 2, pow_mul, h.t_sq, one_pow]
  have bjinv : (t^bj.toNat)⁻¹ = t^bj.toNat := inv_eq_of_mul_eq_one_right bjsq
  have cjz := ((h.comm_zt.symm).pow_left cj.toNat).eq
  have cjt := ((Commute.refl t).pow_left cj.toNat).eq
  have cjv := ((h.comm_tv).pow_left cj.toNat).eq
  have cju := ((h.comm_tu).pow_left cj.toNat).eq
  have cjw := ((h.comm_tw).pow_left cj.toNat).eq
  have cja := ((h.comm_at.symm).pow_left cj.toNat).eq
  have cjb := ((h.comm_bt.symm).pow_left cj.toNat).eq
  have cjc := ((((parrottCommutator_eq_one_iff _ _).mp h.eq10_ct).symm).pow_left cj.toNat).eq
  have cjbi := ((h.comm_zt.symm.pow_left cj.toNat).pow_right bi.toNat).eq
  have cjci := ((h.comm_zt.symm.pow_left cj.toNat).pow_right ci.toNat).eq
  have cjdi := ((h.comm_zt.symm.pow_left cj.toNat).pow_right di.toNat).eq
  have cjsq : t^cj.toNat * t^cj.toNat = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm cj.toNat 2, pow_mul, h.t_sq, one_pow]
  have cjinv : (t^cj.toNat)⁻¹ = t^cj.toNat := inv_eq_of_mul_eq_one_right cjsq
  have bjcj := (((Commute.refl t).pow_left bj.toNat).pow_right cj.toNat).eq
  cases ck <;> cases dj <;> cases dk
  all_goals
    simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, mul_one] at fb fc fd
    have fd2 := congrArg F fd
    conv at fd2 =>
      rhs
      simp only [map_mul, map_inv, map_pow, fb, fc, fd, fa, fz, ft, fv, fu, fw]
      simp only [mul_inv_rev, inv_inv, inv_pow, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
        sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, biinv, ciinv, diinv, bjinv, cjinv, mul_assoc]
      simp -failIfUnchanged only [mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu,
        zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw,
        uw, tail za, za, tail ta, ta, tail va, va, tail ua, ua, tail zb, zb, tail zc, zc, tail zd,
        zd, tail tb, tb, tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc,
        tc, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc, tail ad,
        ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz, tail tt,
        tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb, tail cc,
        cc, tail biz, biz, tail bit, bit, tail biv, biv, tail biu, biu, tail biw, biw, tail bib,
        bib, tail bic, bic, tail bid, bid, tail bia, bia, tail bisq, bisq, tail ciz, ciz, tail cit,
        cit, tail civ, civ, tail ciu, ciu, tail ciw, ciw, tail cib, cib, tail cic, cic, tail cid,
        cid, tail cia, cia, tail cisq, cisq, tail diz, diz, tail dit, dit, tail div, div, tail diu,
        diu, tail diw, diw, tail dib, dib, tail dic, dic, tail did, did, tail dia, dia, tail disq,
        disq, tail bici, bici, tail bidi, bidi, tail cidi, cidi, tail bjz, bjz, tail bjt, bjt,
        tail bjv, bjv, tail bju, bju, tail bjw, bjw, tail bja, bja, tail bjb, bjb, tail bjc, bjc,
        tail bjbi, bjbi, tail bjci, bjci, tail bjdi, bjdi, tail bjsq, bjsq, tail cjz, cjz,
        tail cjt, cjt, tail cjv, cjv, tail cju, cju, tail cjw, cjw, tail cja, cja, tail cjb, cjb,
        tail cjc, cjc, tail cjbi, cjbi, tail cjci, cjci, tail cjdi, cjdi, tail cjsq, cjsq,
        tail bjcj, bjcj]
    have fd3 := congrArg F fd2
    conv at fd3 =>
      rhs
      simp only [map_mul, map_inv, map_pow, fb, fc, fd, fa, fz, ft, fv, fu, fw]
      simp only [mul_inv_rev, inv_inv, inv_pow, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
        sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, biinv, ciinv, diinv, bjinv, cjinv, mul_assoc]
      simp -failIfUnchanged only [mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu,
        zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw,
        uw, tail za, za, tail ta, ta, tail va, va, tail ua, ua, tail zb, zb, tail zc, zc, tail zd,
        zd, tail tb, tb, tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc,
        tc, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc, tail ad,
        ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz, tail tt,
        tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb, tail cc,
        cc, tail biz, biz, tail bit, bit, tail biv, biv, tail biu, biu, tail biw, biw, tail bib,
        bib, tail bic, bic, tail bid, bid, tail bia, bia, tail bisq, bisq, tail ciz, ciz, tail cit,
        cit, tail civ, civ, tail ciu, ciu, tail ciw, ciw, tail cib, cib, tail cic, cic, tail cid,
        cid, tail cia, cia, tail cisq, cisq, tail diz, diz, tail dit, dit, tail div, div, tail diu,
        diu, tail diw, diw, tail dib, dib, tail dic, dic, tail did, did, tail dia, dia, tail disq,
        disq, tail bici, bici, tail bidi, bidi, tail cidi, cidi, tail bjz, bjz, tail bjt, bjt,
        tail bjv, bjv, tail bju, bju, tail bjw, bjw, tail bja, bja, tail bjb, bjb, tail bjc, bjc,
        tail bjbi, bjbi, tail bjci, bjci, tail bjdi, bjdi, tail bjsq, bjsq, tail cjz, cjz,
        tail cjt, cjt, tail cjv, cjv, tail cju, cju, tail cjw, cjw, tail cja, cja, tail cjb, cjb,
        tail cjc, cjc, tail cjbi, cjbi, tail cjci, cjci, tail cjdi, cjdi, tail cjsq, cjsq,
        tail bjcj, bjcj]
    have fd4eq := congrArg F fd3
    conv at fd4eq =>
      rhs
      simp only [map_mul, map_inv, map_pow, fb, fc, fd, fa, fz, ft, fv, fu, fw]
      simp only [mul_inv_rev, inv_inv, inv_pow, sqinv h.z_sq, sqinv h.t_sq, sqinv h.v_sq,
        sqinv h.u_sq, sqinv h.w_sq, sqinv h.a_sq, sqinv h.d_sq, binv, cinv, biinv, ciinv, diinv, bjinv, cjinv, mul_assoc]
      simp -failIfUnchanged only [mul_assoc, one_mul, mul_one, tail zt, zt, tail zv, zv, tail zu,
        zu, tail zw, zw, tail tv, tv, tail tu, tu, tail tw, tw, tail vu, vu, tail vw, vw, tail uw,
        uw, tail za, za, tail ta, ta, tail va, va, tail ua, ua, tail zb, zb, tail zc, zc, tail zd,
        zd, tail tb, tb, tail wb, wb, tail wd, wd, tail ud, ud, tail uc, uc, tail wc, wc, tail tc,
        tc, tail wa, wa, tail ub, ub, tail bd, bd, tail td, td, tail ab, ab, tail vc, vc, tail ad,
        ad, tail ac, ac, tail cd, cd, tail bc, bc, tail vd, vd, tail vb, vb, tail zz, zz, tail tt,
        tt, tail vv, vv, tail uu, uu, tail ww, ww, tail aa, aa, tail dd, dd, tail bb, bb, tail cc,
        cc, tail biz, biz, tail bit, bit, tail biv, biv, tail biu, biu, tail biw, biw, tail bib,
        bib, tail bic, bic, tail bid, bid, tail bia, bia, tail bisq, bisq, tail ciz, ciz, tail cit,
        cit, tail civ, civ, tail ciu, ciu, tail ciw, ciw, tail cib, cib, tail cic, cic, tail cid,
        cid, tail cia, cia, tail cisq, cisq, tail diz, diz, tail dit, dit, tail div, div, tail diu,
        diu, tail diw, diw, tail dib, dib, tail dic, dic, tail did, did, tail dia, dia, tail disq,
        disq, tail bici, bici, tail bidi, bidi, tail cidi, cidi, tail bjz, bjz, tail bjt, bjt,
        tail bjv, bjv, tail bju, bju, tail bjw, bjw, tail bja, bja, tail bjb, bjb, tail bjc, bjc,
        tail bjbi, bjbi, tail bjci, bjci, tail bjdi, bjdi, tail bjsq, bjsq, tail cjz, cjz,
        tail cjt, cjt, tail cjv, cjv, tail cju, cju, tail cjw, cjw, tail cja, cja, tail cjb, cjb,
        tail cjc, cjc, tail cjbi, cjbi, tail cjci, cjci, tail cjdi, cjdi, tail cjsq, cjsq,
        tail bjcj, bjcj]
    have fd4norm := fd4eq.symm.trans fd4
    first | exact Or.inl (mul_left_cancel (fd4norm.trans (mul_one d).symm))
          | exact Or.inr (mul_left_cancel (fd4norm.trans (mul_one d).symm))

private theorem right_conj {g k r : G}
    (hr : parrottCommutator g k = r) (hr2 : r^2=1) : g⁻¹*k*g=k*r := by
  have hswap := (parrottCommutator_eq_iff _ _ _).mp hr
  have hrr : r*r=1 := by simpa only [pow_two] using hr2
  have heq := congrArg (fun p : G => g⁻¹*p*r) hswap
  simpa only [mul_assoc, inv_mul_cancel_left, hrr, mul_one] using heq.symm

private theorem conj_of_commute {g k : G} (h : Commute g k) : g⁻¹*k*g=k := by
  rw [mul_assoc, h.symm.eq, inv_mul_cancel_left]

/-- The fourth power of the outer generator forces its square to centralize b.
The parameters need only satisfy the three displayed conjugation equations. -/
public theorem b_comm_square_mul_z_of_parameters
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hz : z ≠ 1) (hax : parrottCommutator a x = 1)
    (bi bj bk ci cj ck di dj dk : Bool)
    (hb : x⁻¹*b*x = (b*a)*z^bi.toNat*t^bj.toNat*v^bk.toNat)
    (hc : x⁻¹*c*x = (c*(a*b*u*v)⁻¹)*z^ci.toNat*t^cj.toNat*(u*v)^ck.toNat)
    (hd : x⁻¹*d*x = (d*(a*b*c*u*v)⁻¹)*z^di.toNat*(t*u)^dj.toNat*(v*u)^dk.toNat) :
    Commute b (x^2*z) := by
  let F : G →* G := (MulAut.conj x⁻¹).toMonoidHom
  have fapply (g : G) : F g = x⁻¹*g*x := by simp [F]
  have fz : F z = z := by rw [fapply]; exact conj_of_commute h.comm_zx.symm
  have ft : F t = t := by
    rw [fapply]
    exact conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt)
  have fv : F v = v*t := by rw [fapply]; exact right_conj h.eq01_xv h.t_sq
  have fu : F u = u*v := by rw [fapply]; exact right_conj h.eq01_xu h.v_sq
  have fw : F w = w*u := by rw [fapply]; exact right_conj h.eq01_xw h.u_sq
  have fa : F a = a := by
    rw [fapply]
    exact conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp hax).symm
  have fb : F b = (b*a)*z^bi.toNat*t^bj.toNat*v^bk.toNat := by rwa [fapply]
  have fc : F c = (c*(a*b*u*v)⁻¹)*z^ci.toNat*t^cj.toNat*(u*v)^ck.toNat := by
    rwa [fapply]
  have fd : F d = (d*(a*b*c*u*v)⁻¹)*z^di.toNat*(t*u)^dj.toNat*(v*u)^dk.toNat := by
    rwa [fapply]
  have fd4 : F (F (F (F d))) = d := by
    calc
      _ = (x^4)⁻¹*d*x^4 := by simp only [fapply, pow_succ, pow_zero]; group
      _ = d := by rw [h.eq01_x]; simp
  have hbfix : F (F b) = b := by
    cases bk with
    | false =>
      simp only [Bool.toNat_false, pow_zero, mul_one] at fb
      have aa : a*a=1 := by simpa only [pow_two] using h.a_sq
      have zz : z*z=1 := by simpa only [pow_two] using h.z_sq
      have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
      have za := h.comm_az.symm.eq
      have ta := h.comm_at.symm.eq
      have zt := h.comm_zt.eq
      cases bi <;> cases bj
      all_goals
        simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, mul_one] at fb
        simp only [map_mul, fb, fa, fz, ft]
        simp only [mul_assoc, za, tail ta, ta, zt,
          tail aa, aa, zz, tt, one_mul, mul_one]
    | true =>
      simp only [Bool.toNat_true, pow_one] at fb
      obtain hh | hh := fourth_power_obstruction h F fz ft fv fu fw fa
        bi bj ci cj ck di dj dk fb fc fd fd4
      · exact (hz hh).elim
      · apply False.elim
        apply hz
        have hh' := h.eq03_dt
        simpa [parrottCommutator, hh] using hh'.symm
  have hbx : Commute b (x^2) := by
    change b*x^2=x^2*b
    calc
      b*x^2 = x^2*(F (F b)) := by simp only [fapply, pow_succ, pow_zero]; group
      _ = x^2*b := by rw [hbfix]
  exact hbx.mul_right h.comm_zb.symm

end Tits.ParrottSylowSeedRelations
