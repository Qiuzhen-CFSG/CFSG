module

public import Theory.GroupTheory.BaerSuzuki
public import Theory.GroupTheory.Involution.Basic

/-!
# Odd rotations inverted by an involution outside the two-core

Baer–Suzuki gives a conjugate pair of involutions generating a group which
is not a two-group. Their product has order divisible by an odd prime:
otherwise its cyclic subgroup, together with the original involution,
would generate a two-group. Taking a suitable power gives an inverted
element of odd prime order.

Extracted from `BenderSuzuki.SE.II1Hering31.ii1Hering31_odd_rotation`.
The Baer–Suzuki input is Gorenstein, *Finite Groups*, Chapter 3, Theorem 8.2.
This is the Suzuki extraction used by Parrott (1972), printed p.674.
-/

namespace BenderSuzuki
open PFAppendixIII

/-- A contrapositive Baer--Suzuki extraction: an involution outside the
normal `2`-core inverts an element of odd prime order. -/
public theorem involution_outside_twoCore_inverts_odd_prime
    {G : Type*} [Group G] [Finite G]
    (t : G) (ht : IsInvolution t) (htcore : t ∉ pCore 2 G) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      ∃ r : G, orderOf r = q ∧ rightConjugateElem r t = r⁻¹ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htP : IsPElement (p := 2) t := by
    refine ⟨1, ?_⟩
    simpa using orderOf_eq_prime ht.sq_eq_one ht.ne_one
  have hpair : ∃ y : G,
      (∃ g : G, y = g * t * g⁻¹) ∧
        ¬ IsPGroup 2 (Subgroup.closure ({t, y} : Set G)) := by
    by_contra hpair
    push Not at hpair
    have htmem := gorenstein_3_8_2_conjugacy_class_le_pCore
      (G := G) (p := 2) (x := t) htP hpair t ⟨1, by simp⟩
    exact htcore htmem
  obtain ⟨y, ⟨g, rfl⟩, hnotTwo⟩ := hpair
  let y : G := g * t * g⁻¹
  have hy : IsInvolution y := by
    simpa [y, rightConjugateElem] using
      isInvolution_rightConjugateElem (x := t) (g := g⁻¹) ht
  let a : G := t * y
  have hta : rightConjugateElem a t = a⁻¹ := by
    change t⁻¹ * (t * y) * t = (t * y)⁻¹
    rw [ht.inv_eq_self, mul_inv_rev, ht.inv_eq_self, hy.inv_eq_self]
    calc
      t * (t * y) * t = (t * t) * y * t := by group
      _ = y * t := by rw [← pow_two, ht.sq_eq_one]; simp
  have hnotPow : ∀ n : ℕ, orderOf a ≠ 2 ^ n := by
    intro n haorder
    let A : Subgroup G := Subgroup.zpowers a
    let T : Subgroup G := Subgroup.zpowers t
    have hA2 : IsPGroup 2 A := by
      apply IsPGroup.of_card (p := 2) (G := A) (n := n)
      simpa [A, Nat.card_zpowers] using haorder
    have hT2 : IsPGroup 2 T := by
      apply IsPGroup.of_card (n := 1)
      simpa only [T, Nat.card_zpowers, pow_one] using
        (orderOf_eq_prime ht.sq_eq_one ht.ne_one : orderOf t = 2)
    have htNormA : t ∈ Subgroup.normalizer (A : Set G) := by
      have hforward : ∀ z : G, z ∈ A → t * z * t⁻¹ ∈ A := by
        intro z hz
        rw [Subgroup.mem_zpowers_iff] at hz ⊢
        obtain ⟨k, rfl⟩ := hz
        refine ⟨-k, ?_⟩
        let c : MulAut G := MulAut.conj t
        have hc : c a = a⁻¹ := by
          simpa [c, MulAut.conj_apply, rightConjugateElem,
            ht.inv_eq_self] using hta
        have hpow : c (a ^ k) = (a⁻¹) ^ k := by
          rw [map_zpow, hc]
        simpa [c, MulAut.conj_apply] using hpow.symm
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · exact hforward z
      · intro hz
        have hback := hforward (t * z * t⁻¹) hz
        have heq : t * (t * z * t⁻¹) * t⁻¹ = z := by
          rw [ht.inv_eq_self]
          calc
            t * (t * z * t) * t = (t * t) * z * (t * t) := by group
            _ = z := by rw [← pow_two, ht.sq_eq_one]; simp
        rwa [heq] at hback
    have hTNormA : T ≤ Subgroup.normalizer (A : Set G) :=
      Subgroup.zpowers_le.mpr htNormA
    have hsup2 : IsPGroup 2 (A ⊔ T : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hA2 hT2 hTNormA
    have hclosure : Subgroup.closure ({t, y} : Set G) ≤ A ⊔ T := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]
        exact (show T ≤ A ⊔ T from le_sup_right) (Subgroup.mem_zpowers t)
      · rw [hz]
        have haA : a ∈ A := Subgroup.mem_zpowers a
        have htT : t ∈ T := Subgroup.mem_zpowers t
        have hyEq : y = t * a := by
          calc
            y = 1 * y := by simp
            _ = (t * t) * y := by rw [← pow_two, ht.sq_eq_one]
            _ = t * (t * y) := by simp [mul_assoc]
            _ = t * a := by rfl
        rw [hyEq]
        exact (A ⊔ T).mul_mem
          ((show T ≤ A ⊔ T from le_sup_right) htT)
          ((show A ≤ A ⊔ T from le_sup_left) haA)
    exact hnotTwo (hsup2.to_le hclosure)
  have hprime : ∃ q, Nat.Prime q ∧ q ∣ orderOf a ∧ q ≠ 2 := by
    by_contra! hh
    exact hnotPow _ (Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos a).ne'
      (fun hq hqa => hh _ hq hqa))
  obtain ⟨q, hq, hqa, hq2⟩ := hprime
  let r : G := a ^ (orderOf a / q)
  have hrorder : orderOf r = q :=
    orderOf_pow_orderOf_div (orderOf_pos a).ne' hqa
  have hrinv : rightConjugateElem r t = r⁻¹ := by
    have hpow : ∀ n : ℕ,
        rightConjugateElem (a ^ n) t = (a⁻¹) ^ n := by
      intro n
      induction n with
      | zero => simp [rightConjugateElem]
      | succ n ih =>
          rw [pow_succ, pow_succ]
          simp only [rightConjugateElem] at ih hta ⊢
          calc
            t⁻¹ * (a ^ n * a) * t =
                (t⁻¹ * a ^ n * t) * (t⁻¹ * a * t) := by
                  simp [mul_assoc]
            _ = (a⁻¹) ^ n * a⁻¹ := by rw [ih, hta]
    simpa [r] using hpow (orderOf a / q)
  exact ⟨q, hq, hq2, r, hrorder, hrinv⟩

end BenderSuzuki
