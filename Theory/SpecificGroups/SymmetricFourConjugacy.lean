module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

/-!
# The two-regular conjugacy classes of S₄

An odd-order element has order dividing three, since its order divides 24.
A finite check of the permutations then conjugates every nonidentity such
element to `(0 1 2)`. Thus there are exactly two two-regular conjugacy classes.
The finite check is proved by kernel reduction, without a native-code oracle.

This is the elementary conjugacy input to the characteristic-two character
calculation of S₄; see Fong, *Some Sylow subgroups of order 32*,
J. Algebra 6 (1967), p. 71.
-/

public section

namespace SymmetricFourConjugacy

/-- A fixed representative of the nonidentity odd-order conjugacy class. -/
@[expose] def threeCycle : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem threeCycle_ne_one : threeCycle ≠ 1 := by decide

theorem orderOf_threeCycle : orderOf threeCycle = 3 :=
  orderOf_eq_prime (by decide : threeCycle ^ 3 = 1) threeCycle_ne_one

theorem threeCycle_odd : Odd (orderOf threeCycle) := by
  rw [orderOf_threeCycle]
  decide

theorem cube_eq_one_of_odd (g : Equiv.Perm (Fin 4)) (hg : Odd (orderOf g)) :
    g ^ 3 = 1 := by
  have hd : orderOf g ∣ 24 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
      using orderOf_dvd_natCard g
  have hcop : (orderOf g).Coprime 8 := by
    simpa using hg.coprime_two_right.pow_right 3
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hd)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem cube_conjugacy_check :
    ∀ g : Equiv.Perm (Fin 4), g ^ 3 = 1 →
      g = 1 ∨ ∃ k : Equiv.Perm (Fin 4), k * threeCycle * k⁻¹ = g := by
  decide

/-- Every nonidentity odd-order element is conjugate to a three-cycle. -/
theorem eq_one_or_isConj_threeCycle (g : Equiv.Perm (Fin 4))
    (hg : Odd (orderOf g)) : g = 1 ∨ IsConj threeCycle g := by
  rcases cube_conjugacy_check g (cube_eq_one_of_odd g hg) with h | h
  · exact Or.inl h
  · exact Or.inr (isConj_iff.mpr h)

/-- The actual image in the conjugacy-class quotient consists of two classes. -/
theorem twoRegularClasses_eq_pair :
    ConjClasses.mk '' {g : Equiv.Perm (Fin 4) | Odd (orderOf g)} =
      {ConjClasses.mk 1, ConjClasses.mk threeCycle} := by
  ext c
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases eq_one_or_isConj_threeCycle g hg with rfl | hc
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _
        (Set.mem_singleton_iff.mpr (ConjClasses.mk_eq_mk_iff_isConj.mpr hc).symm)
  · rintro (rfl | hc)
    · exact ⟨1, by simp, rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hc
      exact ⟨threeCycle, threeCycle_odd, rfl⟩

/-- The class count used to exhaust a pair of inequivalent modular simples. -/
theorem card_twoRegularClasses :
    Nat.card (ConjClasses.mk '' {g : Equiv.Perm (Fin 4) | ¬ 2 ∣ orderOf g}) = 2 := by
  have hset : {g : Equiv.Perm (Fin 4) | ¬ 2 ∣ orderOf g} =
      {g : Equiv.Perm (Fin 4) | Odd (orderOf g)} := by
    ext g
    simp only [Set.mem_ofPred_eq, ← even_iff_two_dvd, Nat.not_even_iff_odd]
  rw [hset, twoRegularClasses_eq_pair, Nat.card_coe_set_eq]
  apply Set.ncard_pair
  intro h
  exact threeCycle_ne_one (isConj_one_right.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h))

end SymmetricFourConjugacy
