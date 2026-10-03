module

public import Theory.SpecificGroups.Tits.RecognitionSylowOuterAdjustment

/-!
# The final central correction of Parrott's outer generator

Multiplying x by t preserves the seed relations, its actual generating
closure, and y=x²z. Once (16)–(18) and the c-part of (19) hold, it removes
the remaining factor z in [x,d]. The proofs use only the displayed word
relations; no presentation recognition or fusion assertion is assumed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed p.680, final substitution before equation (19).
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

/-- The final substitution preserves every unprimed seed relation. -/
public theorem adjust_xt_relations (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    ParrottSylowSeedRelations false z t v u w a b c d (x*t) := by
  have ht := (parrottCommutator_eq_one_iff _ _).mp h.eq01_xt
  refine { h with
    comm_zx := h.comm_zx.mul_right h.comm_zt
    eq01_x := ?_
    eq01_xt := ?_
    eq01_xv := pc_mul h.eq01_xv h.comm_tv (Commute.refl t)
    eq01_xu := pc_mul h.eq01_xu h.comm_tu h.comm_tv
    eq01_xw := pc_mul h.eq01_xw h.comm_tw h.comm_tu
    ax_alternative := ?_ }
  · rw [ht.mul_pow, h.eq01_x, show t^4=(t^2)^2 by rw [← pow_mul], h.t_sq]
    simp
  · exact (parrottCommutator_eq_one_iff _ _).mpr (ht.mul_left (Commute.refl t))
  · rcases h.ax_alternative with ha | ha
    all_goals
      have he := (parrottCommutator_eq_iff _ _ _).mp ha
      simp -failIfUnchanged only [mul_one] at he
    · left
      exact (parrottCommutator_eq_one_iff _ _).mpr
        (((parrottCommutator_eq_one_iff _ _).mp ha).mul_right h.comm_at)
    · right
      apply (parrottCommutator_eq_iff _ _ _).mpr
      calc
        a*(x*t) = (a*x)*t := by group
        _ = (x*a*t)*t := by rw [he]
        _ = (x*t)*a*t := by rw [mul_assoc x a t, h.comm_at.eq]; group

/-- Multiplying x by t leaves the prescribed involution y=x²z unchanged. -/
public theorem adjust_xt_square
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    (x*t)^2*z = x^2*z := by
  rw [((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt).mul_pow, h.t_sq, mul_one]

/-- The final substitution preserves the actual Sylow generating closure. -/
public theorem adjust_xt_sylow_closure
    (h : ParrottSylowSeedRelations false z t v u w a b c d x) :
    closure ({x*t,a,b,c,d} : Set G) = closure ({x,a,b,c,d} : Set G) := by
  have ht (L : Subgroup G) (ha : a ∈ L) (hb : b ∈ L) : t ∈ L := by
    rw [← h.eq05_ab]
    exact L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem ha) (L.inv_mem hb)) ha) hb
  apply le_antisymm
  · apply (closure_le _).mpr
    let L := closure ({x,a,b,c,d} : Set G)
    have hx : x ∈ L := subset_closure (by simp)
    have ha : a ∈ L := subset_closure (by simp)
    have hb : b ∈ L := subset_closure (by simp)
    have hc : c ∈ L := subset_closure (by simp)
    have hd : d ∈ L := subset_closure (by simp)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact L.mul_mem hx (ht L ha hb)
    all_goals assumption
  · apply (closure_le _).mpr
    let L := closure ({x*t,a,b,c,d} : Set G)
    have hx : x*t ∈ L := subset_closure (by simp)
    have ha : a ∈ L := subset_closure (by simp)
    have hb : b ∈ L := subset_closure (by simp)
    have hc : c ∈ L := subset_closure (by simp)
    have hd : d ∈ L := subset_closure (by simp)
    have hx' : x ∈ L := (L.mul_mem_cancel_right (ht L ha hb)).mp hx
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Equation (16) survives the final substitution. -/
public theorem adjust_xt_ax
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (ha : parrottCommutator a x = 1) : parrottCommutator a (x*t) = 1 :=
  (parrottCommutator_eq_one_iff _ _).mpr
    (((parrottCommutator_eq_one_iff _ _).mp ha).mul_right h.comm_at)

/-- Equation (18) survives the final substitution. -/
public theorem adjust_xt_bx
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hb : parrottCommutator b x = a) : parrottCommutator b (x*t) = a := by
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have hb := (parrottCommutator_eq_iff _ _ _).mp hb
  calc
    b*(x*t) = (x*b*a)*t := by rw [← mul_assoc, hb]
    _ = (x*t)*b*a := by
      rw [mul_assoc (x*b), h.comm_at.eq, ← mul_assoc, mul_assoc x b t, h.comm_bt.eq]
      group

/-- The c-commutator in (19) survives the final substitution. -/
public theorem adjust_xt_xc
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hc : parrottCommutator x c = a*b*u*v) :
    parrottCommutator (x*t) c = a*b*u*v := by
  exact pc_mul hc ((parrottCommutator_eq_one_iff _ _).mp h.eq10_ct).symm
    (((h.comm_at.symm.mul_right h.comm_bt.symm).mul_right h.comm_tu).mul_right h.comm_tv)

/-- Multiplying x by t toggles precisely the final central factor in (19). -/
public theorem adjust_xt_xd
    (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (hd : parrottCommutator x d = (a*b*c*u*v)*z) :
    parrottCommutator (x*t) d = a*b*c*u*v := by
  have htd : t*d=d*t*z := by
    have hd := (parrottCommutator_eq_iff _ _ _).mp h.eq03_dt
    have hzz : z*z=1 := by simpa only [pow_two] using h.z_sq
    calc
      t*d = (t*d)*(z*z) := by rw [hzz, mul_one]
      _ = (d*t)*z := by rw [← mul_assoc, ← hd]
  have htc := ((parrottCommutator_eq_one_iff _ _).mp h.eq10_ct).symm
  have htr := ((((h.comm_at.symm.mul_right h.comm_bt.symm).mul_right htc).mul_right
    h.comm_tu).mul_right h.comm_tv).mul_right h.comm_zt.symm
  have hd := (parrottCommutator_eq_iff _ _ _).mp hd
  have hzz : z*z=1 := by simpa only [pow_two] using h.z_sq
  apply (parrottCommutator_eq_iff _ _ _).mpr
  calc
    (x*t)*d = x*(d*t*z) := by rw [mul_assoc, htd]
    _ = (x*d)*t*z := by group
    _ = (d*x*((a*b*c*u*v)*z))*t*z := by rw [hd]
    _ = d*(x*t)*(a*b*c*u*v) := by
      rw [mul_assoc (d*x), ← htr.eq]
      simp only [mul_assoc, hzz, mul_one]
end Tits.ParrottSylowSeedRelations
