module

public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Fixed conjugators for actions trivial modulo a coprime normal subgroup

Let a prime-power group A act compatibly on a finite group K and a K-set X.
Suppose every displacement in K lies in a normal subgroup N whose order is
prime to the actor prime. Any two A-fixed points in one K-orbit have an
A-fixed transporter, even when the order of K is not coprime to that prime.

Fix a transporter g and retain just those transporters in the coset gN.
This fiber is a coset of the intersection of N with the point stabilizer,
so its cardinality divides |N|. Trivial action on K/N makes the fiber
A-invariant. The prime-power fixed-point congruence supplies the transporter.
The Sylow specialization gives conjugacy by a fixed group element.

This is the fixed-conjugator step for GLS, Volume 4, Chapter 2,
Proposition 3.7(b), printed p.30. The subsequent centralizer application is
in `Theory.GroupAction.ZStarInvariantSylow.Centralizer`.
-/

open Subgroup MulAction
open scoped Pointwise

namespace Theory.GroupAction

/-- Fixed points have fixed transporters if all displacement lies in a
normal subgroup of order prime to the actor prime. -/
public theorem exists_fixed_transporter_of_normal_displacement
    {A K X : Type*} [Group A] [Group K] [Finite K]
    [MulDistribMulAction A K] [MulAction A X] [MulAction K X]
    {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A)
    (N : Subgroup K) [N.Normal] (hN : ¬ p ∣ Nat.card N)
    (hdisp : ∀ (a : A) (k : K), (a • k) * k⁻¹ ∈ N)
    (compat : ∀ (a : A) (k : K) (x : X),
      a • (k • x) = (a • k) • (a • x))
    (x y : X) (hx : ∀ a : A, a • x = x) (hy : ∀ a : A, a • y = y)
    (hxy : ∃ k : K, k • x = y) :
    ∃ k : K, (∀ a : A, a • k = k) ∧ k • x = y := by
  obtain ⟨g, hg⟩ := hxy
  let q := QuotientGroup.mk' N
  have hq (a : A) (k : K) : q (a • k) = q k := by
    exact QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_eq_mul_inv] using hdisp a k)
  let C := stabilizer K x ⊓ N
  let T := {k : K // k • x = y ∧ q k = q g}
  let e : C ≃ T := {
    toFun c := ⟨g * c, by
      constructor
      · rw [mul_smul, c.property.1, hg]
      · have hc : q (c : K) = 1 := (QuotientGroup.eq_one_iff _).mpr c.property.2
        rw [map_mul, hc, mul_one]⟩
    invFun k := ⟨g⁻¹ * k, by
      constructor
      · change (g⁻¹ * (k : K)) • x = x
        rw [mul_smul, k.property.1, ← hg, inv_smul_smul]
      · apply (QuotientGroup.eq_one_iff _).mp
        change q (g⁻¹ * (k : K)) = 1
        rw [map_mul, map_inv, k.property.2, inv_mul_cancel]⟩
    left_inv c := Subtype.ext (by simp)
    right_inv k := Subtype.ext (by simp) }
  let _ : MulAction A T := {
    smul a k := ⟨a • (k : K), by
      constructor
      · calc
          (a • (k : K)) • x = a • ((k : K) • x) := by
            simpa only [hx a] using (compat a k x).symm
          _ = y := by rw [k.property.1, hy]
      · exact (hq a k).trans k.property.2⟩
    one_smul k := Subtype.ext (one_smul A (k : K))
    mul_smul a b k := Subtype.ext (mul_smul a b (k : K)) }
  have hT : ¬ p ∣ Nat.card T := by
    rw [← Nat.card_congr e]
    exact fun h => hN (h.trans (Subgroup.card_dvd_of_le (show C ≤ N from inf_le_right)))
  obtain ⟨k, hk⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card T hT
  exact ⟨k, fun a => congrArg Subtype.val (hk a), k.property.1⟩

/-- Invariant Sylow subgroups are conjugate by a fixed element under an
action trivial modulo a normal subgroup of coprime order. -/
public theorem exists_fixed_sylow_conjugator_of_normal_displacement
    {A K : Type*} [Group A] [Group K] [Finite K]
    [MulDistribMulAction A K] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hA : IsPGroup p A) (N : Subgroup K) [N.Normal]
    (hN : ¬ p ∣ Nat.card N)
    (hdisp : ∀ (a : A) (k : K), (a • k) * k⁻¹ ∈ N)
    (P Q : Sylow q K) (hP : IsInvariant A K (P : Subgroup K))
    (hQ : IsInvariant A K (Q : Subgroup K)) :
    ∃ k : K, (∀ a : A, a • k = k) ∧
      (P : Subgroup K).map (MulAut.conj k).toMonoidHom = Q := by
  have hfixed (R : Sylow q K) (hR : IsInvariant A K (R : Subgroup K))
      (a : A) : a • R = R := by
    apply Sylow.ext
    change (R : Subgroup K).map (MulDistribMulAction.toMulAut A K a).toMonoidHom = R
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hR.invariant a y).mp hy
    · intro hx
      exact ⟨a⁻¹ • x, (hR.invariant a⁻¹ x).mp hx, smul_inv_smul a x⟩
  have hcompat (a : A) (k : K) (R : Sylow q K) :
      a • (k • R) = (a • k) • (a • R) := by
    apply Sylow.ext
    change ((R : Subgroup K).map (MulAut.conj k).toMonoidHom).map
        (MulDistribMulAction.toMulAut A K a).toMonoidHom =
      ((R : Subgroup K).map (MulDistribMulAction.toMulAut A K a).toMonoidHom).map
        (MulAut.conj (a • k)).toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, smul_mul', smul_inv']
  obtain ⟨k, hk, he⟩ := exists_fixed_transporter_of_normal_displacement
    hA N hN hdisp hcompat P Q (hfixed P hP) (hfixed Q hQ) (exists_smul_eq K P Q)
  exact ⟨k, hk, congrArg Sylow.toSubgroup he⟩

end Theory.GroupAction
