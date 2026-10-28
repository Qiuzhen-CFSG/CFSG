module
public import Theory.SpecificGroups.Tits.RecognitionSylowSeed

/-!
# The first outer-generator adjustment in Parrott's calculation

For an unprimed seed with [a,x]=t, the simultaneous substitutions a↦av and
c↦cw preserve equations (1)–(15) and make [a,x]=1. Collecting words proves
the relations; recovering v from b² and w from c² and [a,d] proves equality
of the original and replacement generating closures.

Independently, the seed determines y=x²z. It has square one, commutes with
z and a, and its action on v,u,w is the square of the prescribed x-action.
These facts require neither presentation recognition nor a choice of an
odd-order subgroup.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed pp.678–680, especially equation (16) on p.680.
-/

open Subgroup
namespace Tits.ParrottSylowSeedRelations
variable {G : Type*} [Group G] {z t v u w a b c d x : G}
private theorem sqinv {p : G} (hp : p ^ 2 = 1) : p⁻¹ = p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem reverse {p q r : G} (h : p*q=q*p*r) : q*p=p*q*r⁻¹ := by rw [h]; group
set_option maxHeartbeats 1200000 in
set_option linter.unusedSimpArgs false in
/-- Replacing a by av and c by cw preserves all unprimed seed relations. -/
public theorem adjust_ax_relations (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hax : parrottCommutator a x = t) :
    ParrottSylowSeedRelations false z t v u w (a*v) b (c*w) d x := by
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

/-- The first p.680 replacement centralizes the outer generator. -/
public theorem adjust_ax_eq (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hax : parrottCommutator a x = t) : parrottCommutator (a*v) x = 1 := by
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have ax := (parrottCommutator_eq_iff _ _ _).mp hax
  have vx := reverse ((parrottCommutator_eq_iff _ _ _).mp h.eq01_xv)
  rw [sqinv h.t_sq] at vx
  have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
  simp only [mul_assoc, vx, tail ax, tail h.comm_tv.eq, tt, mul_one]

private theorem comm_mem (L : Subgroup G) {g k : G} (hg : g ∈ L) (hk : k ∈ L) :
    parrottCommutator g k ∈ L :=
  L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hg) (L.inv_mem hk)) hg) hk

private theorem core_mem_vw
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (L : Subgroup G) (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hd : d ∈ L) :
    v ∈ L ∧ w ∈ L := by
  have hv : v ∈ L := h.eq03_b ▸ L.pow_mem hb 2
  have hu : u ∈ L := by
    simpa only [h.eq11_ad, Bool.false_eq_true, ↓reduceIte] using comm_mem L ha hd
  have hwu : w*u ∈ L := by
    simpa only [h.eq13, Bool.false_eq_true, ↓reduceIte] using L.pow_mem hc 2
  exact ⟨hv, (L.mul_mem_cancel_right hu).mp hwu⟩

/-- The replacements a↦av and c↦cw generate the same core. -/
public theorem adjust_ax_core_closure
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hax : parrottCommutator a x = t) :
    closure ({a*v,b,c*w,d} : Set G) = closure ({a,b,c,d} : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    have ha : a ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    have hb : b ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    have hc : c ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    have hd : d ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    obtain ⟨hv, hw⟩ := core_mem_vw h _ ha hb hc hd
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mul_mem ha hv
    · exact hb
    · exact mul_mem hc hw
    · exact hd
  · apply (closure_le _).mpr
    let L := closure ({a*v,b,c*w,d} : Set G)
    have ha : a*v ∈ L := subset_closure (by simp)
    have hb : b ∈ L := subset_closure (by simp)
    have hc : c*w ∈ L := subset_closure (by simp)
    have hd : d ∈ L := subset_closure (by simp)
    obtain ⟨hv, hw⟩ := core_mem_vw (h.adjust_ax_relations hax) _ ha hb hc hd
    have ha' : a ∈ L := (L.mul_mem_cancel_right hv).mp ha
    have hc' : c ∈ L := (L.mul_mem_cancel_right hw).mp hc
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption

/-- The first p.680 replacement preserves the actual Sylow generating closure. -/
public theorem adjust_ax_sylow_closure
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hax : parrottCommutator a x = t) :
    closure ({x,a*v,b,c*w,d} : Set G) = closure ({x,a,b,c,d} : Set G) := by
  have split (g k l m r : G) : closure ({g,k,l,m,r} : Set G) =
      closure ({g} : Set G) ⊔ closure ({k,l,m,r} : Set G) := by
    rw [← closure_union]
    congr 1
  rw [split, split, h.adjust_ax_core_closure hax]

/-- Multiplying the last basis vector by v preserves the elementary closure. -/
public theorem adjust_ax_elementary_closure :
    closure ({z,t,v,u,a*v} : Set G) = closure ({z,t,v,u,a} : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    have hz : z ∈ closure ({z,t,v,u,a} : Set G) := subset_closure (by simp)
    have ht : t ∈ closure ({z,t,v,u,a} : Set G) := subset_closure (by simp)
    have hv : v ∈ closure ({z,t,v,u,a} : Set G) := subset_closure (by simp)
    have hu : u ∈ closure ({z,t,v,u,a} : Set G) := subset_closure (by simp)
    have ha : a ∈ closure ({z,t,v,u,a} : Set G) := subset_closure (by simp)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hz
    · exact ht
    · exact hv
    · exact hu
    · exact mul_mem ha hv
  · apply (closure_le _).mpr
    have hz : z ∈ closure ({z,t,v,u,a*v} : Set G) := subset_closure (by simp)
    have ht : t ∈ closure ({z,t,v,u,a*v} : Set G) := subset_closure (by simp)
    have hv : v ∈ closure ({z,t,v,u,a*v} : Set G) := subset_closure (by simp)
    have hu : u ∈ closure ({z,t,v,u,a*v} : Set G) := subset_closure (by simp)
    have ha : a*v ∈ closure ({z,t,v,u,a*v} : Set G) := subset_closure (by simp)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hz
    · exact ht
    · exact hv
    · exact hu
    · exact (mul_mem_cancel_right hv).mp ha

/-- The forced choice y=x²z satisfies (4), is an involution, and centralizes z. -/
public theorem square_mul_z {caseTwo : Bool}
    (h : ParrottSylowSeedRelations caseTwo z t v u w a b c d x) :
    (x^2*z)^2 = 1 ∧ x^2 = (x^2*z)*z ∧ Commute z (x^2*z) := by
  have hxz : Commute (x^2) z := h.comm_zx.symm.pow_left 2
  refine ⟨?_, ?_, (h.comm_zx.pow_right 2).mul_right (Commute.refl z)⟩
  · rw [hxz.mul_pow, ← pow_mul, show 2*2=4 from rfl, h.eq01_x, h.z_sq, one_mul]
  · simp only [mul_assoc, ← pow_two, h.z_sq, mul_one]

/-- Equation (6) already follows from the seed's two a,x alternatives. -/
public theorem square_mul_z_comm_a {caseTwo : Bool}
    (h : ParrottSylowSeedRelations caseTwo z t v u w a b c d x) :
    parrottCommutator (x^2*z) a = 1 := by
  apply (parrottCommutator_eq_one_iff _ _).mpr
  apply Commute.mul_left _ h.comm_az.symm
  rcases h.ax_alternative with ha | ha
  · exact ((parrottCommutator_eq_one_iff _ _).mp ha).symm.pow_left 2
  · have ax := (parrottCommutator_eq_iff _ _ _).mp ha
    have tx := ((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt).symm.eq
    have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
    apply Commute.symm
    change a*x^2=x^2*a
    simp only [pow_two, mul_assoc, tail ax, tx, tt, mul_one]

private theorem right_conj_of_commutator {g k r : G}
    (hr : parrottCommutator g k = r) (hr2 : r^2=1) :
    g⁻¹*k*g=k*r := by
  have hswap := (parrottCommutator_eq_iff _ _ _).mp hr
  have hrr : r*r=1 := by simpa only [pow_two] using hr2
  have heq := congrArg (fun p : G => g⁻¹*p*r) hswap
  simpa only [mul_assoc, inv_mul_cancel_left, hrr, mul_one] using heq.symm

private theorem square_mul_z_conj {caseTwo : Bool}
    (h : ParrottSylowSeedRelations caseTwo z t v u w a b c d x)
    {q : G} (hq : Commute z q) :
    (x^2*z)⁻¹*q*(x^2*z) = x⁻¹*(x⁻¹*q*x)*x := by
  have hz : z⁻¹*q*z=q := by rw [mul_assoc, hq.symm.eq]; simp
  calc
    _ = (x^2)⁻¹*(z⁻¹*q*z)*x^2 := by rw [← (h.comm_zx.pow_right 2).eq]; group
    _ = _ := by rw [hz, pow_two]; group

/-- The forced involution acts on v,u,w by the second power of the outer action. -/
public theorem square_mul_z_action {caseTwo : Bool}
    (h : ParrottSylowSeedRelations caseTwo z t v u w a b c d x) :
    (x^2*z)⁻¹*v*(x^2*z) = v ∧
    (x^2*z)⁻¹*u*(x^2*z) = u*t ∧
    (x^2*z)⁻¹*w*(x^2*z) = w*v := by
  have xv := right_conj_of_commutator h.eq01_xv h.t_sq
  have xu := right_conj_of_commutator h.eq01_xu h.v_sq
  have xw := right_conj_of_commutator h.eq01_xw h.u_sq
  have xt : x⁻¹*t*x=t := by
    simpa only [mul_one] using right_conj_of_commutator h.eq01_xt (one_pow 2)
  have mulconj (g k : G) : x⁻¹*(g*k)*x=(x⁻¹*g*x)*(x⁻¹*k*x) := by group
  have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
  have vv : v*v=1 := by simpa only [pow_two] using h.v_sq
  have uu : u*u=1 := by simpa only [pow_two] using h.u_sq
  refine ⟨?_, ?_, ?_⟩
  · rw [square_mul_z_conj h h.comm_zv, xv, mulconj, xv, xt]
    simp only [mul_assoc, tt, mul_one]
  · rw [square_mul_z_conj h h.comm_zu, xu, mulconj, xu, xv]
    simp only [mul_assoc, ← mul_assoc v v, vv, one_mul]
  · rw [square_mul_z_conj h h.comm_zw, xw, mulconj, xw, xu]
    simp only [mul_assoc, ← mul_assoc u u, uu, one_mul]

end Tits.ParrottSylowSeedRelations
