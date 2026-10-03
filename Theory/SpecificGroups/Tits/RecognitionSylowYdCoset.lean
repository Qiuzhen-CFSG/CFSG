module

public import Theory.SpecificGroups.Tits.RecognitionSylowOuterAdjustment
public import Theory.GroupTheory.CyclicExtension
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.FinCases

/-!
# The four initial values of the outer d-commutator

Write y=x²z and k=[y,d], using Parrott's commutator convention. Comparing
conjugation on z,t,v,u,w shows that kb⁻¹ centralizes their closure. If this
discrepancy belongs to that closure, collect its five binary coordinates.
The relations ak=katz and bk=kb, followed by d⁻¹kd=k⁻¹, leave precisely
k in bw⟨v,z⟩. No completed Sylow frame or odd-order subgroup is assumed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed p.680, the calculation immediately before equation (17).
-/

set_option linter.unusedSimpArgs false
open Subgroup Tits
namespace Tits.ParrottSylowSeedRelations
variable {G : Type*} [Group G] {z t v u w a b c d x : G}
private theorem sqinv {p : G} (hp : p^2=1) : p⁻¹=p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
private theorem tail {p q r : G} (h : p*q=r) (k : G) : p*(q*k)=r*k := by rw [← mul_assoc, h]
private theorem pc_conj_rev {p q r : G} (h : parrottCommutator p q = r)
    (hr : r^2=1) : p⁻¹*q*p=q*r := by
  rw [← sqinv hr, ← h, parrottCommutator]; group
private theorem conj_comm {p q : G} (h : Commute p q) : p⁻¹*q*p=q := by
  rw [mul_assoc, h.symm.eq, inv_mul_cancel_left]

/-- The commutator with d has the same action on the derived generators as b. -/
public theorem yd_discrepancy_centralizes (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    parrottCommutator (x^2*z) d * b⁻¹ ∈ centralizer (closure ({z,t,v,u,w} : Set G) : Set G) := by
  let y := x^2*z
  let Y : G ≃* G := MulAut.conj y⁻¹
  let D : G ≃* G := MulAut.conj d⁻¹
  let B : G ≃* G := MulAut.conj b⁻¹
  have yeq (s : G) : Y s = y⁻¹*s*y := by simp [Y]
  have deq (s : G) : D s = d⁻¹*s*d := by simp [D]
  have beq (s : G) : B s = b⁻¹*s*b := by simp [B]
  have yz : Y z=z := by rw [yeq]; exact conj_comm h.square_mul_z.2.2.symm
  have yt : Y t=t := by
    rw [yeq]
    exact conj_comm ((((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt).pow_left 2).mul_left h.comm_zt)
  have yv : Y v=v := by rw [yeq]; exact h.square_mul_z_action.1
  have yu : Y u=u*t := by rw [yeq]; exact h.square_mul_z_action.2.1
  have yw : Y w=w*v := by rw [yeq]; exact h.square_mul_z_action.2.2
  have dz : D z=z := by rw [deq]; exact conj_comm h.comm_zd.symm
  have dt : D t=t*z := by rw [deq]; exact pc_conj_rev h.eq03_dt h.z_sq
  have dv : D v=v := by
    rw [← h.eq03_b, map_pow]
    have db : D b=b*v := by rw [deq]; exact pc_conj_rev h.eq03_db h.v_sq
    have bv : Commute b v := by rw [← h.eq03_b]; exact Commute.self_pow b 2
    rw [db, bv.mul_pow, h.eq03_b, h.v_sq, mul_one]
  have du : D u=u := by rw [deq]; simpa using pc_conj_rev h.eq08_du (one_pow 2)
  have dw : D w=w := by rw [deq]; simpa using pc_conj_rev h.eq07_dw (one_pow 2)
  have bz : B z=z := by rw [beq]; exact conj_comm h.comm_zb.symm
  have bt : B t=t := by rw [beq]; exact conj_comm h.comm_bt
  have bv : B v=v := by rw [beq, ← h.eq03_b]; exact conj_comm (Commute.self_pow b 2)
  have bu : B u=u*z := by rw [beq]; exact pc_conj_rev h.eq02_bu h.z_sq
  have bw : B w=w := by rw [beq]; simpa using pc_conj_rev h.eq02_bw (one_pow 2)
  have kact (s : G) : (parrottCommutator y d)⁻¹*s*(parrottCommutator y d) = D (Y (D (Y s))) := by
    rw [deq, yeq, deq, yeq]
    simp only [parrottCommutator, mul_inv_rev, inv_inv, sqinv h.d_sq,
      show y⁻¹=y from sqinv h.square_mul_z.1]
    group
  have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
  rw [centralizer_closure]
  intro s hs
  have he : (parrottCommutator y d)⁻¹*s*(parrottCommutator y d) = b⁻¹*s*b := by
    rw [kact, ← beq]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;>
      simp only [yz,yt,yv,yu,yw,dz,dt,dv,du,dw,bz,bt,bv,bu,bw,map_mul,
        mul_assoc, h.comm_zt.eq, tail tt, one_mul, ← pow_two, h.z_sq,h.t_sq,h.v_sq,mul_one]
  have he' := congrArg (fun q => parrottCommutator y d * q * b⁻¹) he
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right, mul_inv_cancel_right, mul_inv_cancel, mul_one] using he'

private theorem rev {p q r : G} (hr : r^2=1) (h : parrottCommutator p q=r) :
    q*p=p*q*r := by
  have he := (parrottCommutator_eq_iff _ _ _).mp h
  calc
    q*p = p*q*r⁻¹ := by rw [he]; group
    _ = _ := by rw [sqinv hr]

/-- Centralization of b by y restricts its d-commutator through a and b. -/
private theorem yd_constraints (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hby : Commute b (x^2*z)) :
    a * parrottCommutator (x^2*z) d = parrottCommutator (x^2*z) d * a * t * z ∧
    b * parrottCommutator (x^2*z) d = parrottCommutator (x^2*z) d * b := by
  let y := x^2*z
  have yi : y⁻¹=y := sqinv h.square_mul_z.1
  have ya : y*a=a*y := ((parrottCommutator_eq_one_iff _ _).mp h.square_mul_z_comm_a).eq
  have yb : y*b=b*y := hby.symm.eq
  have da : d*a=a*d*u := rev h.u_sq (by simpa using h.eq11_ad)
  have db : d*b=b*d*v := (parrottCommutator_eq_iff _ _ _).mp h.eq03_db
  have ud : u*d=d*u := ((parrottCommutator_eq_one_iff _ _).mp h.eq08_du).symm.eq
  have uy : u*y=y*u*t := by
    have he := congrArg (fun q => y*q) h.square_mul_z_action.2.1
    change y*(y⁻¹*u*y)=y*(u*t) at he
    simpa only [mul_assoc, mul_inv_cancel_left] using he
  have vd : v*d=d*v := by
    have db' := pc_conj_rev h.eq03_db h.v_sq
    have bv : Commute b v := by rw [← h.eq03_b]; exact Commute.self_pow b 2
    have he' : d⁻¹*v*d=v := by
      calc
        d⁻¹*v*d = (d⁻¹*b*d)^2 := by rw [← h.eq03_b]; simp only [pow_two]; group
        _ = _ := by rw [db', bv.mul_pow, h.eq03_b,h.v_sq,mul_one]
    exact (mul_inv_eq_iff_eq_mul.mp (by simpa only [sqinv h.d_sq] using he')).symm
  have vy : v*y=y*v := by
    have he := congrArg (fun q => y*q) h.square_mul_z_action.1
    change y*(y⁻¹*v*y)=y*v at he
    simpa only [mul_assoc, mul_inv_cancel_left] using he
  have td : t*d=d*t*z := rev h.z_sq h.eq03_dt
  have ty : t*y=y*t :=
    (((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt).symm.pow_right 2).mul_right h.comm_zt.symm
  have zd := h.comm_zd.eq
  have zy : z*y=y*z := h.square_mul_z.2.2.eq
  have uu : u*u=1 := by simpa only [pow_two] using h.u_sq
  have vv : v*v=1 := by simpa only [pow_two] using h.v_sq
  have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
  have zz : z*z=1 := by simpa only [pow_two] using h.z_sq
  change a * parrottCommutator y d = parrottCommutator y d*a*t*z ∧
    b * parrottCommutator y d = parrottCommutator y d*b
  constructor <;>
    simp only [parrottCommutator, yi, sqinv h.d_sq, mul_assoc,
      tail ya,ya,tail yb,yb,tail da,da,tail db,db,tail ud,ud,tail uy,uy,
      tail vd,vd,tail vy,vy,tail td,td,tail ty,ty,tail zd,zd,tail zy,zy,
      tail h.comm_tu.eq,h.comm_tu.eq,tail h.comm_zu.eq,h.comm_zu.eq,
      tail h.comm_tv.eq,h.comm_tv.eq,tail h.comm_zv.eq,h.comm_zv.eq,
      tail h.comm_zt.eq,h.comm_zt.eq,tail uu,uu,tail vv,vv,tail tt,tt,tail zz,zz,
      one_mul,mul_one]

private theorem derived_coordinates [Finite G]
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    {q : G} (hq : q ∈ closure ({z,t,v,u,w} : Set G)) :
    ∃ i j k l m : Fin 2, q = z^i.val*v^j.val*t^k.val*u^l.val*w^m.val := by
  have step (S : Set G) (g : G) (hg : g^2=1)
      (hc : ∀ r ∈ S, Commute g r) {s : G} (hs : s ∈ closure (insert g S)) :
      ∃ r ∈ closure S, ∃ i : Fin 2, r*g^i.val=s := by
    apply Theory.GroupTheory.exists_mul_pow_of_mem_closure_insert S g 2 (by decide) hg _ hs
    intro r hr
    rw [(hc r hr).eq, mul_inv_cancel_right]
    exact subset_closure hr
  have hq' : q ∈ closure ({w,u,t,v,z} : Set G) := by
    convert hq using 2
    ext r
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  obtain ⟨q1,hq1,m,rfl⟩ := step {u,t,v,z} w h.w_sq (by
    intro r hr
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.comm_uw.symm
    · exact h.comm_tw.symm
    · exact h.comm_vw.symm
    · exact h.comm_zw.symm) hq'
  obtain ⟨q2,hq2,l,rfl⟩ := step {t,v,z} u h.u_sq (by
    intro r hr
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.comm_tu.symm
    · exact h.comm_vu.symm
    · exact h.comm_zu.symm) hq1
  obtain ⟨q3,hq3,k,rfl⟩ := step {v,z} t h.t_sq (by
    intro r hr
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact h.comm_tv
    · exact h.comm_zt.symm) hq2
  obtain ⟨q4,hq4,j,rfl⟩ := step {z} v h.v_sq (by
    intro r hr
    have : r=z := hr
    subst r
    exact h.comm_zv.symm) hq3
  obtain ⟨q5,hq5,i,rfl⟩ := step ∅ z h.z_sq (by simp) (by simpa using hq4)
  have hq5' : q5=1 := by simpa only [Subgroup.closure_empty,mem_bot] using hq5
  exact ⟨i,j,k,l,m,by rw [hq5',one_mul]⟩

set_option maxHeartbeats 1200000 in
/-- A discrepancy in the elementary derived closure leaves only the four
values in bw⟨v,z⟩. The a- and b-relations eliminate the w- and u-errors;
conjugation by d eliminates the t-error. -/
public theorem yd_cases_of_discrepancy_mem [Finite G]
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hy : orderOf (x^2*z) = 2) (hby : Commute b (x^2*z)) (hz : z ≠ 1)
    (hq : parrottCommutator (x^2*z) d * b⁻¹ ∈ closure ({z,t,v,u,w} : Set G)) :
    parrottCommutator (x^2*z) d = b*w ∨
    parrottCommutator (x^2*z) d = b*w*z ∨
    parrottCommutator (x^2*z) d = b*w*v ∨
    parrottCommutator (x^2*z) d = b*w*v*z := by
  obtain ⟨i,j,k,l,m,hq⟩ := derived_coordinates h hq
  have hk : parrottCommutator (x^2*z) d = (z^i.val*v^j.val*t^k.val*u^l.val*w^m.val)*b :=
    mul_inv_eq_iff_eq_mul.mp hq
  obtain ⟨ha,hb⟩ := yd_constraints h hby
  have hy2 : (x^2*z)^2=1 := (orderOf_eq_prime_iff.mp hy).1
  have hd : d⁻¹ * parrottCommutator (x^2*z) d * d = (parrottCommutator (x^2*z) d)⁻¹ := by
    simp only [parrottCommutator,mul_inv_rev,inv_inv,sqinv h.d_sq,sqinv hy2]
    simp only [mul_assoc, show d*d=1 by simpa only [pow_two] using h.d_sq, mul_one]
  have ba : b*a=a*b*t := rev h.t_sq h.eq05_ab
  have wa : w*a=a*w*z := rev h.z_sq h.eq02_aw
  have ub : u*b=b*u*z := rev h.z_sq h.eq02_bu
  have wb : w*b=b*w := ((parrottCommutator_eq_one_iff _ _).mp h.eq02_bw).symm.eq
  have vb : v*b=b*v := by rw [← h.eq03_b]; exact (Commute.self_pow b 2).symm.eq
  have tb := h.comm_bt.symm.eq
  have za := h.comm_az.symm.eq
  have ta := h.comm_at.symm.eq
  have va := h.comm_av.symm.eq
  have ua := h.comm_au.symm.eq
  have zd := h.comm_zd.eq
  have ud : u*d=d*u := ((parrottCommutator_eq_one_iff _ _).mp h.eq08_du).symm.eq
  have wd : w*d=d*w := ((parrottCommutator_eq_one_iff _ _).mp h.eq07_dw).symm.eq
  have td : t*d=d*t*z := rev h.z_sq h.eq03_dt
  have db : d*b=b*d*v := (parrottCommutator_eq_iff _ _ _).mp h.eq03_db
  have dv : d*v=v*d := by
    have he : d⁻¹*v*d=v := by
      calc
        d⁻¹*v*d = (d⁻¹*b*d)^2 := by rw [← h.eq03_b]; simp only [pow_two]; group
        _ = (b*v)^2 := by rw [pc_conj_rev h.eq03_db h.v_sq]
        _ = v := by rw [(show Commute b v from vb.symm).mul_pow,h.eq03_b,h.v_sq,mul_one]
    exact mul_inv_eq_iff_eq_mul.mp (by simpa only [sqinv h.d_sq] using he)
  have vd := dv.symm
  have binv : b⁻¹=b*v := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc,← pow_two,h.eq03_b,← pow_two,h.v_sq]
  have zz : z*z=1 := by simpa only [pow_two] using h.z_sq
  have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
  have vv : v*v=1 := by simpa only [pow_two] using h.v_sq
  have uu : u*u=1 := by simpa only [pow_two] using h.u_sq
  have ww : w*w=1 := by simpa only [pow_two] using h.w_sq
  have dd : d*d=1 := by simpa only [pow_two] using h.d_sq
  rw [hk] at ha hb hd ⊢
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases m
  all_goals
    simp only [Fin.val_zero,Fin.val_one,pow_zero,pow_one,one_mul,mul_one,
      mul_inv_rev,inv_inv,sqinv h.z_sq,sqinv h.t_sq,sqinv h.v_sq,sqinv h.u_sq,
      sqinv h.w_sq,sqinv h.d_sq,binv,mul_assoc,
      tail ba,ba,tail wa,wa,tail ub,ub,tail wb,wb,tail vb,vb,tail tb,tb,
      tail za,za,tail ta,ta,tail va,va,tail ua,ua,
      tail zd,zd,tail ud,ud,tail wd,wd,tail td,td,tail db,db,tail vd,vd,
      tail h.comm_zb.eq,h.comm_zb.eq,
      tail h.comm_zt.eq,h.comm_zt.eq,tail h.comm_zv.eq,h.comm_zv.eq,
      tail h.comm_zu.eq,h.comm_zu.eq,tail h.comm_zw.eq,h.comm_zw.eq,
      tail h.comm_tv.eq,h.comm_tv.eq,tail h.comm_tu.eq,h.comm_tu.eq,
      tail h.comm_tw.eq,h.comm_tw.eq,tail h.comm_vu.eq,h.comm_vu.eq,
      tail h.comm_vw.eq,h.comm_vw.eq,tail h.comm_uw.eq,h.comm_uw.eq,
      tail zz,zz,tail tt,tt,tail vv,vv,tail uu,uu,tail ww,ww,tail dd,dd,
      one_mul,mul_one,true_or,or_true] at ha hb hd ⊢
  all_goals
    simp only [mul_left_cancel_iff,mul_right_cancel_iff,mul_eq_left,mul_eq_right,left_eq_mul,right_eq_mul,
      hz,eq_self,not_false_eq_true,false_or,true_or,or_true] at ha hb hd

end Tits.ParrottSylowSeedRelations
