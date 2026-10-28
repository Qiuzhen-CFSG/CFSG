module

public import Theory.SpecificGroups.Tits.RecognitionSylowOuterAdjustment

/-!
# A residual symmetry of Parrott's intermediate Sylow coordinates

The simultaneous substitution a↦at, b↦bv, c↦cu, d↦dw preserves
(1)–(18). It also preserves the prescribed central factor in [y,c],
where y=x²z. Its effect on [x,c] records a remaining coordinate ambiguity.
All statements are word identities in the supplied group.

Source: Parrott (1972), §3, printed pp.678–680, equations (1)–(19).
-/

open Subgroup
namespace Tits.ParrottSylowSeedRelations
variable {G : Type*} [Group G] {z t v u w a b c d x : G}
private theorem sqinv {p : G} (hp : p^2=1) : p⁻¹=p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem reverse {p q r : G} (h : p*q=q*p*r) : q*p=p*q*r⁻¹ := by rw [h]; group
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

/-- A residual simultaneous change of the four core generators. -/
public theorem residual_relations
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    ParrottSylowSeedRelations false z t v u w (a*t) (b*v) (c*u) (d*w) x := by
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
  have xxxx : x*(x*(x*x))=1 := by
    simpa only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h.eq01_x
  rcases h.ax_alternative with ha | ha
  all_goals
    have ax := (parrottCommutator_eq_iff _ _ _).mp ha
    constructor
    all_goals
      simp -failIfUnchanged only [parrottCommutator_eq_iff, Commute, SemiconjBy, Bool.false_eq_true, ↓reduceIte]
      simp -failIfUnchanged only [pow_succ, pow_zero, mul_one, mul_inv_rev, inv_inv, sqinv h.z_sq,
        sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq,
        sqinv h.a_sq, sqinv h.d_sq, binv, cinv, mul_assoc]
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
        tail cc, cc, tail ax, ax, xxxx, true_or, or_true]


private theorem comm_mem (L : Subgroup G) {g k : G} (hg : g ∈ L) (hk : k ∈ L) :
    parrottCommutator g k ∈ L :=
  L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hg) (L.inv_mem hk)) hg) hk

private theorem core_mem
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (L : Subgroup G) (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hd : d ∈ L) :
    t ∈ L ∧ v ∈ L ∧ u ∈ L ∧ w ∈ L := by
  have ht : t ∈ L := h.eq05_ab ▸ comm_mem L ha hb
  have hv : v ∈ L := h.eq03_b ▸ L.pow_mem hb 2
  have hu : u ∈ L := by simpa only [h.eq11_ad, Bool.false_eq_true, ↓reduceIte] using comm_mem L ha hd
  have hwu : w*u ∈ L := by simpa only [h.eq13, Bool.false_eq_true, ↓reduceIte] using L.pow_mem hc 2
  exact ⟨ht, hv, hu, (L.mul_mem_cancel_right hu).mp hwu⟩

/-- The residual substitution fixes the subgroup generated by the core coordinates. -/
public theorem residual_core_closure
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    closure ({a*t,b*v,c*u,d*w} : Set G) = closure ({a,b,c,d} : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    have ha : a ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    have hb : b ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    have hc : c ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    have hd : d ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    obtain ⟨ht,hv,hu,hw⟩ := core_mem h _ ha hb hc hd
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mul_mem ha ht
    · exact mul_mem hb hv
    · exact mul_mem hc hu
    · exact mul_mem hd hw
  · apply (closure_le _).mpr
    let L := closure ({a*t,b*v,c*u,d*w} : Set G)
    have ha : a*t ∈ L := subset_closure (by simp)
    have hb : b*v ∈ L := subset_closure (by simp)
    have hc : c*u ∈ L := subset_closure (by simp)
    have hd : d*w ∈ L := subset_closure (by simp)
    obtain ⟨ht,hv,hu,hw⟩ := core_mem h.residual_relations _ ha hb hc hd
    have ha' : a ∈ L := (L.mul_mem_cancel_right ht).mp ha
    have hb' : b ∈ L := (L.mul_mem_cancel_right hv).mp hb
    have hc' : c ∈ L := (L.mul_mem_cancel_right hu).mp hc
    have hd' : d ∈ L := (L.mul_mem_cancel_right hw).mp hd
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption

/-- The residual substitution fixes the Sylow generating closure. -/
public theorem residual_sylow_closure
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    closure ({x,a*t,b*v,c*u,d*w} : Set G) = closure ({x,a,b,c,d} : Set G) := by
  have split (g k l m r : G) : closure ({g,k,l,m,r} : Set G) =
      closure ({g} : Set G) ⊔ closure ({k,l,m,r} : Set G) := by
    rw [← closure_union]
    congr 1
  rw [split, split, h.residual_core_closure]

/-- The residual substitution fixes the second elementary subgroup. -/
public theorem residual_elementary_closure :
    closure ({z,t,v,u,a*t} : Set G) = closure ({z,t,v,u,a} : Set G) := by
  simpa only [Set.pair_comm t v, Set.insert_comm t v] using
    (adjust_ax_elementary_closure (z := z) (t := v) (v := t) (u := u) (a := a))

private theorem pc_right_mul (p q r : G) :
    parrottCommutator p (q*r) = parrottCommutator p r * (r⁻¹*parrottCommutator p q*r) := by
  unfold parrottCommutator
  group

private theorem pc_left_mul (p q r : G) :
    parrottCommutator (p*q) r = (q⁻¹*parrottCommutator p r*q)*parrottCommutator q r := by
  unfold parrottCommutator
  group

private theorem pc_reverse (p q : G) : parrottCommutator q p = (parrottCommutator p q)⁻¹ := by
  unfold parrottCommutator
  group

/-- The first middle relation is preserved by the residual substitution. -/
public theorem residual_ax (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (ha : parrottCommutator a x = 1) : parrottCommutator (a*t) x = 1 := by
  rw [pc_left_mul, ha, pc_reverse x t, h.eq01_xt]
  simp

/-- The last middle relation is preserved by the residual substitution. -/
public theorem residual_bx (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hb : parrottCommutator b x = a) : parrottCommutator (b*v) x = a*t := by
  rw [pc_left_mul, hb, pc_reverse x v, h.eq01_xv, sqinv h.t_sq]
  rw [mul_assoc v⁻¹, h.comm_av.eq, inv_mul_cancel_left]

private theorem square_commutators
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    parrottCommutator (x^2*z) u = t ∧ parrottCommutator (x^2*z) w = v := by
  have hu : parrottCommutator u (x^2*z) = t := by
    change u⁻¹*(x^2*z)⁻¹*u*(x^2*z)=t
    rw [mul_assoc u⁻¹, mul_assoc u⁻¹, h.square_mul_z_action.2.1, inv_mul_cancel_left]
  have hw : parrottCommutator w (x^2*z) = v := by
    change w⁻¹*(x^2*z)⁻¹*w*(x^2*z)=v
    rw [mul_assoc w⁻¹, mul_assoc w⁻¹, h.square_mul_z_action.2.2, inv_mul_cancel_left]
  exact ⟨by rw [pc_reverse, hu, sqinv h.t_sq], by rw [pc_reverse, hw, sqinv h.v_sq]⟩

/-- Commutation of b with y is preserved. -/
public theorem residual_by (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hb : Commute b (x^2*z)) : Commute (b*v) (x^2*z) := by
  apply hb.mul_left
  change v*(x^2*z)=(x^2*z)*v
  have he := congrArg (fun g => (x^2*z)*g) h.square_mul_z_action.1
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he

/-- Equation (17) is preserved by the residual substitution. -/
public theorem residual_yd (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hd : parrottCommutator (x^2*z) d = b*w) :
    parrottCommutator (x^2*z) (d*w) = (b*v)*w := by
  rw [pc_right_mul, h.square_commutators.2, hd]
  have bw := (parrottCommutator_eq_one_iff _ _).mp h.eq02_bw
  have bv : Commute b v := by rw [← h.eq03_b]; exact Commute.self_pow b 2
  rw [bw.eq, inv_mul_cancel_left, ← mul_assoc, bv.symm.eq]

/-- The selected equation for [y,c] is preserved by the residual substitution. -/
public theorem residual_yc (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hc : parrottCommutator (x^2*z) c = a*t*z) :
    parrottCommutator (x^2*z) (c*u) = (a*t)*t*z := by
  rw [pc_right_mul, h.square_commutators.1, hc]
  have hu : Commute (a*t*z) u := (h.comm_au.mul_left h.comm_tu).mul_left h.comm_zu
  rw [mul_assoc u⁻¹, hu.eq, inv_mul_cancel_left]
  simp only [mul_assoc, h.comm_at.symm.left_comm]

/-- In contrast, the proposed exact equation for [x,c] changes by tz. -/
public theorem residual_xc (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hc : parrottCommutator x c = a*b*u*v) :
    parrottCommutator x (c*u) = ((a*t)*(b*v)*u*v)*(t*z) := by
  rw [pc_right_mul, h.eq01_xu, hc]
  have ub := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq02_bu)
  rw [sqinv h.z_sq] at ub
  have bv : Commute b v := by rw [← h.eq03_b]; exact Commute.self_pow b 2
  have uu : u*u=1 := by simpa only [pow_two] using h.u_sq
  have vv : v*v=1 := by simpa only [pow_two] using h.v_sq
  have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
  simp only [sqinv h.u_sq, mul_assoc, tail h.comm_vu.eq, tail h.comm_av.symm.eq,
    tail h.comm_au.symm.eq, tail bv.symm.eq, tail ub, tail h.comm_zu.eq,
    tail h.comm_zv.eq, tail h.comm_zt.eq, tail h.comm_tu.eq,
    tail h.comm_tv.eq, tail h.comm_bt.symm.eq, tail uu, tail vv, tail tt,
    uu, vv, tt, h.comm_zu.eq, mul_one, one_mul]

end Tits.ParrottSylowSeedRelations
