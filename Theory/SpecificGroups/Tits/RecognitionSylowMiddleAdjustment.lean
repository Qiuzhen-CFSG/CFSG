module

public import Theory.SpecificGroups.Tits.RecognitionSylowOuterAdjustment

/-!
# Coordinate corrections for the middle Sylow relations

The substitutions x↦xv and x↦xu preserve the unprimed seed relations and
its generating closures, and change the prescribed y=x²z to yt and yv,
respectively. The simultaneous substitution a↦at, d↦dw preserves the
seed and its closures. On the commutator [y,d], these substitutions remove
the central z-error and the v-error by explicit word identities.

The proofs use only group relations. In particular, they do not identify
b with any generator selected through an odd-order fixed subgroup.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed p.680, the substitutions preceding equations (17) and (18).
The printed assertion [y,d′]=1 must read [y,d′]=bw.
-/

open Subgroup
namespace Tits.ParrottSylowSeedRelations
variable {G : Type*} [Group G] {z t v u w a b c d x : G}
private theorem pc_mul {p q r s : G} (hpq : parrottCommutator p q = r)
    (hsq : Commute s q) (hsr : Commute s r) : parrottCommutator (p*s) q = r := by
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have he := (parrottCommutator_eq_iff _ _ _).mp hpq
  calc
    (p*s)*q = (p*q)*s := by rw [mul_assoc, hsq.eq, ← mul_assoc]
    _ = (q*p*r)*s := by rw [he]
    _ = q*(p*s)*r := by rw [mul_assoc (q*p), ← hsr.eq]; group
private theorem twist_square {p s r : G} (hps : parrottCommutator p s = r)
    (hs : s^2=1) (hr : r^2=1) (hsr : Commute s r) : (p*s)^2 = p^2*r := by
  have he := (parrottCommutator_eq_iff _ _ _).mp hps
  have hrr : r*r=1 := by simpa only [pow_two] using hr
  have hss : s*s=1 := by simpa only [pow_two] using hs
  have hsx : s*p=p*s*r := by
    calc
      s*p = (s*p)*(r*r) := by rw [hrr, mul_one]
      _ = (p*s)*r := by rw [← mul_assoc, ← he]
  calc
    (p*s)^2 = p*(s*p)*s := by rw [pow_two]; group
    _ = p*(p*s*r)*s := by rw [hsx]
    _ = p*p*(s*r)*s := by group
    _ = p*p*(r*s)*s := by rw [hsr.eq]
    _ = p^2*r := by simp only [pow_two, mul_assoc, hss, mul_one]
public theorem adjust_xv_square (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    (x*v)^2*z = (x^2*z)*t := by
  rw [twist_square h.eq01_xv h.v_sq h.t_sq h.comm_tv.symm]
  rw [mul_assoc, h.comm_zt.symm.eq, ← mul_assoc]
public theorem adjust_xu_square (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    (x*u)^2*z = (x^2*z)*v := by
  rw [twist_square h.eq01_xu h.u_sq h.v_sq h.comm_vu.symm]
  rw [mul_assoc, h.comm_zv.symm.eq, ← mul_assoc]

public theorem adjust_xv_relations (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    ParrottSylowSeedRelations false z t v u w a b c d (x*v) := by
  have ht := (parrottCommutator_eq_one_iff _ _).mp h.eq01_xt
  refine { h with
    comm_zx := h.comm_zx.mul_right h.comm_zv
    eq01_x := ?_
    eq01_xt := (parrottCommutator_eq_one_iff _ _).mpr (ht.mul_left h.comm_tv.symm)
    eq01_xv := pc_mul h.eq01_xv (Commute.refl v) h.comm_tv.symm
    eq01_xu := pc_mul h.eq01_xu h.comm_vu (Commute.refl v)
    eq01_xw := pc_mul h.eq01_xw h.comm_vw h.comm_vu
    ax_alternative := ?_ }
  · rw [show (x*v)^4=((x*v)^2)^2 by rw [← pow_mul],
      twist_square h.eq01_xv h.v_sq h.t_sq h.comm_tv.symm,
      (ht.pow_left 2).mul_pow, ← pow_mul, show 2*2=4 from rfl, h.eq01_x, h.t_sq,
      one_mul]
  · rcases h.ax_alternative with ha | ha
    · exact Or.inl ((parrottCommutator_eq_one_iff _ _).mpr
        (((parrottCommutator_eq_one_iff _ _).mp ha).mul_right h.comm_av))
    · right
      apply (parrottCommutator_eq_iff _ _ _).mpr
      have he := (parrottCommutator_eq_iff _ _ _).mp ha
      calc
        a*(x*v) = (x*a*t)*v := by rw [← mul_assoc, he]
        _ = (x*v)*a*t := by
          rw [mul_assoc (x*a), h.comm_tv.eq, ← mul_assoc, mul_assoc x a v, h.comm_av.eq]
          group

public theorem adjust_xu_relations (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    ParrottSylowSeedRelations false z t v u w a b c d (x*u) := by
  have ht := (parrottCommutator_eq_one_iff _ _).mp h.eq01_xt
  have hv : Commute (x^2) v := by
    have hv := h.square_mul_z_action.1
    have hyv : Commute (x^2*z) v := by
      have he := congrArg (fun q => (x^2*z)*q) hv
      change (x^2*z)*v = v*(x^2*z)
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he.symm
    have hv' := hyv.mul_left h.comm_zv
    rwa [← h.square_mul_z.2.1] at hv'
  refine { h with
    comm_zx := h.comm_zx.mul_right h.comm_zu
    eq01_x := ?_
    eq01_xt := (parrottCommutator_eq_one_iff _ _).mpr (ht.mul_left h.comm_tu.symm)
    eq01_xv := pc_mul h.eq01_xv h.comm_vu.symm h.comm_tu.symm
    eq01_xu := pc_mul h.eq01_xu (Commute.refl u) h.comm_vu.symm
    eq01_xw := pc_mul h.eq01_xw h.comm_uw (Commute.refl u)
    ax_alternative := ?_ }
  · rw [show (x*u)^4=((x*u)^2)^2 by rw [← pow_mul],
      twist_square h.eq01_xu h.u_sq h.v_sq h.comm_vu.symm,
      hv.mul_pow, ← pow_mul, show 2*2=4 from rfl, h.eq01_x, h.v_sq, one_mul]
  · rcases h.ax_alternative with ha | ha
    · exact Or.inl ((parrottCommutator_eq_one_iff _ _).mpr
        (((parrottCommutator_eq_one_iff _ _).mp ha).mul_right h.comm_au))
    · right
      apply (parrottCommutator_eq_iff _ _ _).mpr
      have he := (parrottCommutator_eq_iff _ _ _).mp ha
      calc
        a*(x*u) = (x*a*t)*u := by rw [← mul_assoc, he]
        _ = (x*u)*a*t := by
          rw [mul_assoc (x*a), h.comm_tu.eq, ← mul_assoc, mul_assoc x a u, h.comm_au.eq]
          group
private theorem closure_shift (S : Set G) {r : G} (hr : r ∈ closure S) (x : G) :
    closure (insert (x*r) S) = closure (insert x S) := by
  have hS (q : G) : closure S ≤ closure (insert q S) :=
    closure_mono (Set.subset_insert _ _)
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact mul_mem (subset_closure (Set.mem_insert _ _)) (hS x hr)
    · exact subset_closure (Set.mem_insert_of_mem _ hg)
  · apply (closure_le _).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact (mul_mem_cancel_right (hS _ hr)).mp
        (subset_closure (Set.mem_insert _ _))
    · exact subset_closure (Set.mem_insert_of_mem _ hg)

public theorem adjust_xv_sylow_closure
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    closure ({x*v,a,b,c,d} : Set G) = closure ({x,a,b,c,d} : Set G) := by
  apply closure_shift
  rw [← h.eq03_b]
  exact pow_mem (subset_closure (by simp)) 2

public theorem adjust_xu_sylow_closure
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    closure ({x*u,a,b,c,d} : Set G) = closure ({x,a,b,c,d} : Set G) := by
  apply closure_shift
  rw [show u=parrottCommutator a d from h.eq11_ad.symm]
  have ha : a ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
  have hd : d ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
  exact mul_mem (mul_mem (mul_mem (inv_mem ha) (inv_mem hd)) ha) hd

public theorem adjust_xv_ax
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (ha : parrottCommutator a x = 1) : parrottCommutator a (x*v) = 1 :=
  (parrottCommutator_eq_one_iff _ _).mpr
    (((parrottCommutator_eq_one_iff _ _).mp ha).mul_right h.comm_av)

public theorem adjust_xu_ax
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (ha : parrottCommutator a x = 1) : parrottCommutator a (x*u) = 1 :=
  (parrottCommutator_eq_one_iff _ _).mpr
    (((parrottCommutator_eq_one_iff _ _).mp ha).mul_right h.comm_au)

public theorem adjust_xv_by
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hb : Commute b (x^2*z)) : Commute b ((x*v)^2*z) := by
  rw [h.adjust_xv_square]
  exact hb.mul_right h.comm_bt

public theorem adjust_xu_by
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hb : Commute b (x^2*z)) : Commute b ((x*u)^2*z) := by
  rw [h.adjust_xu_square]
  exact hb.mul_right (h.eq03_b ▸ Commute.self_pow b 2)

private theorem sqinv {p : G} (hp : p ^ 2 = 1) : p⁻¹ = p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem reverse {p q r : G} (h : p*q=q*p*r) : q*p=p*q*r⁻¹ := by rw [h]; group
set_option maxHeartbeats 1200000 in
set_option linter.unusedSimpArgs false in
/-- Replacing a by at and d by dw preserves all unprimed seed relations. -/
public theorem adjust_dw_relations (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hax : parrottCommutator a x = 1) :
    ParrottSylowSeedRelations false z t v u w (a*t) b c (d*w) x := by
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
    simp -failIfUnchanged only [← mul_assoc, bb, vv]
  have cinv : c⁻¹=c*u*w := by
    apply inv_eq_of_mul_eq_one_right
    simp -failIfUnchanged only [mul_assoc, tail uc, uc, tail wc, wc, tail uw, uw, tail cc, cc, tail ww, ww, tail uu, uu, one_mul, mul_one]
  have xinv : x⁻¹=x*x*x := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h.eq01_x
  have xxxx : x*(x*(x*x))=1 := by
    simpa only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h.eq01_x
  have xxxx_tail (k : G) : x*(x*(x*(x*k)))=k := by
    calc
      x*(x*(x*(x*k))) = (x*(x*(x*x)))*k := by simp -failIfUnchanged only [mul_assoc]
      _ = k := by rw [xxxx, one_mul]
  have ax := (parrottCommutator_eq_iff _ _ _).mp hax
  constructor
  all_goals
    simp -failIfUnchanged only [parrottCommutator_eq_iff, Commute, SemiconjBy, Bool.false_eq_true, ↓reduceIte]
    simp -failIfUnchanged only [pow_succ, pow_zero, mul_one, mul_inv_rev, inv_inv, sqinv h.z_sq,
      sqinv h.t_sq, sqinv h.v_sq, sqinv h.u_sq, sqinv h.w_sq,
      sqinv h.a_sq, sqinv h.d_sq, binv, cinv, xinv, mul_assoc]
    simp -failIfUnchanged only [mul_assoc, one_mul, mul_one, true_or, or_true, xxxx, xxxx_tail,
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
      tail cc, cc,
      tail ax, ax]

private theorem core_mem_tw
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (L : Subgroup G) (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hd : d ∈ L) :
    t ∈ L ∧ w ∈ L := by
  have comm_mem {g k : G} (hg : g ∈ L) (hk : k ∈ L) :
      parrottCommutator g k ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hg) (L.inv_mem hk)) hg) hk
  have ht : t ∈ L := h.eq05_ab ▸ comm_mem ha hb
  have hu : u ∈ L := by simpa only [h.eq11_ad, Bool.false_eq_true, ↓reduceIte] using comm_mem ha hd
  have hwu : w*u ∈ L := by simpa only [h.eq13, Bool.false_eq_true, ↓reduceIte] using L.pow_mem hc 2
  exact ⟨ht, (L.mul_mem_cancel_right hu).mp hwu⟩

public theorem adjust_dw_core_closure
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hax : parrottCommutator a x = 1) :
    closure ({a*t,b,c,d*w} : Set G) = closure ({a,b,c,d} : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    let L := closure ({a,b,c,d} : Set G)
    have ha : a ∈ L := subset_closure (by simp)
    have hb : b ∈ L := subset_closure (by simp)
    have hc : c ∈ L := subset_closure (by simp)
    have hd : d ∈ L := subset_closure (by simp)
    obtain ⟨ht, hw⟩ := core_mem_tw h L ha hb hc hd
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mul_mem ha ht
    · exact hb
    · exact hc
    · exact mul_mem hd hw
  · apply (closure_le _).mpr
    let L := closure ({a*t,b,c,d*w} : Set G)
    have ha : a*t ∈ L := subset_closure (by simp)
    have hb : b ∈ L := subset_closure (by simp)
    have hc : c ∈ L := subset_closure (by simp)
    have hd : d*w ∈ L := subset_closure (by simp)
    obtain ⟨ht, hw⟩ := core_mem_tw (h.adjust_dw_relations hax) L ha hb hc hd
    have ha' : a ∈ L := (L.mul_mem_cancel_right ht).mp ha
    have hd' : d ∈ L := (L.mul_mem_cancel_right hw).mp hd
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption

public theorem adjust_dw_sylow_closure
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hax : parrottCommutator a x = 1) :
    closure ({x,a*t,b,c,d*w} : Set G) = closure ({x,a,b,c,d} : Set G) := by
  have split (g k l m r : G) : closure ({g,k,l,m,r} : Set G) =
      closure ({g} : Set G) ⊔ closure ({k,l,m,r} : Set G) := by
    rw [← closure_union]
    congr 1
  rw [split, split, h.adjust_dw_core_closure hax]

public theorem adjust_dw_elementary_closure :
    closure ({z,t,v,u,a*t} : Set G) = closure ({z,t,v,u,a} : Set G) := by
  simpa only [Set.insert_comm v t] using
    (adjust_ax_elementary_closure (z := z) (t := v) (v := t) (u := u) (a := a))

public theorem adjust_dw_ax
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (ha : parrottCommutator a x = 1) : parrottCommutator (a*t) x = 1 :=
  (parrottCommutator_eq_one_iff _ _).mpr
    (((parrottCommutator_eq_one_iff _ _).mp ha).mul_left
      ((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt).symm)

private theorem pc_mul_value {p q r s k : G} (hpq : parrottCommutator p q = r)
    (hsq : parrottCommutator s q = k) (hsr : Commute s r) :
    parrottCommutator (p*s) q = r*k := by
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have hpq := (parrottCommutator_eq_iff _ _ _).mp hpq
  have hsq := (parrottCommutator_eq_iff _ _ _).mp hsq
  calc
    (p*s)*q = p*(q*s*k) := by rw [mul_assoc, hsq]
    _ = (q*p*r)*s*k := by simp only [← mul_assoc, hpq]
    _ = q*(p*s)*(r*k) := by rw [mul_assoc (q*p), ← hsr.eq]; group

private theorem pc_right_mul_value {p q r s k : G}
    (hpq : parrottCommutator p q = r) (hps : parrottCommutator p s = k)
    (hsr : Commute s r) (hkr : Commute k r) :
    parrottCommutator p (q*s) = r*k := by
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have hpq := (parrottCommutator_eq_iff _ _ _).mp hpq
  have hps := (parrottCommutator_eq_iff _ _ _).mp hps
  calc
    p*(q*s) = (q*p*r)*s := by rw [← mul_assoc, hpq]
    _ = q*(p*s)*r := by rw [mul_assoc (q*p), ← hsr.eq]; group
    _ = q*(s*p*k)*r := by rw [hps]
    _ = (q*s)*p*(r*k) := by simp only [mul_assoc, hkr.eq]

public theorem adjust_xv_yd
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    {r : G} (hd : parrottCommutator (x^2*z) d = r) (htr : Commute t r) :
    parrottCommutator ((x*v)^2*z) d = r*z := by
  rw [h.adjust_xv_square]
  apply pc_mul_value hd _ htr
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have he := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq03_dt)
  rwa [sqinv h.z_sq] at he

public theorem adjust_dw_yd
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    {r : G} (hd : parrottCommutator (x^2*z) d = r)
    (hwr : Commute w r) (hvr : Commute v r) :
    parrottCommutator (x^2*z) (d*w) = r*v := by
  apply pc_right_mul_value hd _ hwr hvr
  have he := h.square_mul_z_action.2.2
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have he' := congrArg (fun q => (x^2*z)*q) he
  have hh : w*(x^2*z) = (x^2*z)*w*v := by
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he'
  have hh' := reverse hh
  simpa only [sqinv h.v_sq] using hh'

/-- Multiplying x by v preserves its b-commutator whenever v centralizes that value. -/
public theorem adjust_xv_bx
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    {r : G} (hb : parrottCommutator b x = r) (hvr : Commute v r) :
    parrottCommutator b (x*v) = r := by
  have hbv : Commute b v := h.eq03_b ▸ Commute.self_pow b 2
  simpa only [mul_one] using pc_right_mul_value hb
    ((parrottCommutator_eq_one_iff _ _).mpr hbv) hvr (Commute.one_left r)

/-- Multiplying x by u toggles the central z-factor in its b-commutator. -/
public theorem adjust_xu_bx
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    {r : G} (hb : parrottCommutator b x = r)
    (hur : Commute u r) (hzr : Commute z r) :
    parrottCommutator b (x*u) = r*z :=
  pc_right_mul_value hb h.eq02_bu hur hzr

end Tits.ParrottSylowSeedRelations
