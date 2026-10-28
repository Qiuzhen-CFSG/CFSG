module
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

/-!
# A central involution from two nonconjugate involutions

In a finite group, two involutions that are not conjugate generate a
subgroup containing an involution that commutes with both. The conclusion
retains membership in the literal join of their cyclic subgroups. Their
generated group is not assumed to be a two-group.

Put r=a*b. Each involution inverts r by conjugation and therefore inverts
every power of r. If r has even order 2k, its half-order power r^k is a
nonidentity involution. Inversion fixes that power, so it commutes with
both generators. If r has odd order 2k+1, then g=r^k satisfies g²=r⁻¹;
the same inversion identity gives g*a*g⁻¹=b, contrary to nonconjugacy.

This elementary dihedral calculation supplies the central involution used
in Stellmacher (10.1)(a3), Journal of Algebra190 (1997), printed p.62 after
(11). The actual path and ambient nonconjugacy are supplied by that caller.
-/

namespace Theory.GroupTheory

/-- The canonical half-order power is an involution centralizing both factors. -/
public theorem half_order_involution_of_not_isConj
    {G : Type*} [Group G] [Finite G]
    (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hnot : ¬ IsConj a b) :
    let u := (a * b) ^ (orderOf (a * b) / 2)
    u ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b ∧
      orderOf u = 2 ∧ Commute u a ∧ Commute u b := by
  have ha2 : a^2=1 := by simpa only [ha] using pow_orderOf_eq_one a
  have hb2 : b^2=1 := by simpa only [hb] using pow_orderOf_eq_one b
  have haa : a*a=1 := by simpa only [pow_two] using ha2
  have hbb : b*b=1 := by simpa only [pow_two] using hb2
  have hai : a⁻¹=a := inv_eq_iff_mul_eq_one.mpr haa
  have hbi : b⁻¹=b := inv_eq_iff_mul_eq_one.mpr hbb
  let r := a*b
  have haRot : MulAut.conj a r=r⁻¹ := by
    change a*(a*b)*a⁻¹=(a*b)⁻¹
    rw [mul_inv_rev,hai,hbi,←mul_assoc a a b,haa,one_mul]
  have hbRot : MulAut.conj b r=r⁻¹ := by
    change b*(a*b)*b⁻¹=(a*b)⁻¹
    rw [mul_inv_rev,hai,hbi]
    calc
      b*(a*b)*b = (b*a)*(b*b) := by group
      _ = b*a := by rw [hbb,mul_one]
  have haPow (k:ℕ) : MulAut.conj a (r^k)=(r^k)⁻¹ := by rw [map_pow,haRot,inv_pow]
  have hbPow (k:ℕ) : MulAut.conj b (r^k)=(r^k)⁻¹ := by rw [map_pow,hbRot,inv_pow]
  rcases Nat.even_or_odd (orderOf r) with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hpos := orderOf_pos r
    have htwok : k*2=orderOf r := by omega
    have hk0 : k≠0 := by omega
    have hkn : k<orderOf r := by omega
    have hsquare : (r^k)^2=1 := by rw [←pow_mul,htwok,pow_orderOf_eq_one]
    have hinv : (r^k)⁻¹=r^k := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hsquare)
    have hhalf : orderOf (a * b) / 2 = k := by change orderOf r / 2 = k; omega
    dsimp only
    rw [hhalf]
    refine ⟨?_,orderOf_eq_prime hsquare (pow_ne_one_of_lt_orderOf hk0 hkn),?_,?_⟩
    · exact (Subgroup.zpowers a ⊔ Subgroup.zpowers b).pow_mem
        (Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers b)) k
    · have hh := haPow k
      rw [hinv] at hh
      change a*(r^k)*a⁻¹=r^k at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · have hh := hbPow k
      rw [hinv] at hh
      change b*(r^k)*b⁻¹=r^k at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · apply False.elim
    apply hnot
    let g := r^k
    have hnum : k*2+1=orderOf r := by omega
    have hsquare : g^2=r⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      change (r^k)^2*r=1
      rw [←pow_mul,←pow_succ,hnum,pow_orderOf_eq_one]
    have hmove : a*g⁻¹=g*a := by
      have hh : MulAut.conj a g⁻¹=g := by
        rw [map_inv,show MulAut.conj a g=g⁻¹ from haPow k,inv_inv]
      exact mul_inv_eq_iff_eq_mul.mp hh
    apply isConj_iff.mpr
    refine ⟨g,?_⟩
    calc
      g*a*g⁻¹ = g*(a*g⁻¹) := by group
      _ = g*(g*a) := by rw [hmove]
      _ = g^2*a := by simp only [pow_two,mul_assoc]
      _ = r⁻¹*a := by rw [hsquare]
      _ = b := by dsimp [r]; rw [mul_inv_rev,hai,hbi,mul_assoc,haa,mul_one]

/-- Two nonconjugate involutions generate a subgroup with a central involution. -/
public theorem exists_central_involution_of_not_isConj
    {G : Type*} [Group G] [Finite G]
    (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hnot : ¬ IsConj a b) :
    ∃ u : G, u ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b ∧
      orderOf u = 2 ∧ Commute u a ∧ Commute u b :=
  ⟨_, half_order_involution_of_not_isConj a b ha hb hnot⟩

end Theory.GroupTheory
