module
public import Theory.GroupAction.ElementaryNineSylowLine
public import Theory.GroupTheory.ChiefFactorDirectPower

/-!
# Sylow irreducibility of a small elementary cubic chief subgroup

A proper nonzero subgroup of an elementary group of order three or nine
has order three. If a Sylow two-subgroup preserves it, the action on the
four cubic lines supplies an ambient-normal cubic subgroup. Chief
minimality then forces the entire chief subgroup to have order three.

Source: Aschbacher--Smith 13.7.4(1), printed p.937, the assertion that T
is irreducible on the selected elementary three-chief actor.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {Q : Type*} [Group Q] [Finite Q]

theorem chief_elementary_three_sylow_irreducible
    (P : Subgroup Q) [IsElementaryAbelian 3 P]
    (hchief : ChiefFactor.IsChief P ⊥)
    (hcard : Nat.card P = 3 ∨ Nat.card P = 9)
    (S : Sylow 2 Q) (A : Subgroup Q) (hAP : A ≤ P)
    (hSA : (S : Subgroup Q) ≤ normalizer (A : Set Q)) : A = ⊥ ∨ A = P := by
  by_cases hbot : A = ⊥
  · exact Or.inl hbot
  by_cases htop : A = P
  · exact Or.inr htop
  have hAc : Nat.card A = 3 := by
    have hd : Nat.card A ∣ Nat.card P := card_dvd_of_le hAP
    have hne1 : Nat.card A ≠ 1 := fun he => hbot (card_eq_one.mp he)
    rcases hcard with hp | hp
    · rw [hp] at hd
      exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hne1
    · rw [hp] at hd
      obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show Nat.card A ∣ 3 ^ 2 from hd)
      interval_cases n
      · exact (hne1 he).elim
      · exact he
      · exact (htop (eq_of_le_of_card_ge hAP (by omega))).elim
  let : P.Normal := hchief.normal_upper
  obtain ⟨B, hBP, hBn, hBc⟩ := exists_normal_cubic_le_of_sylow_invariant
    P hcard S A hAP hAc hSA
  rcases hchief.minimal B hBn bot_le hBP with hb | hb
  · have hh : Nat.card B = 1 := card_eq_one.mpr hb
    omega
  · have hp : Nat.card P = 3 := hb ▸ hBc
    exact Or.inr (eq_of_le_of_card_ge hAP (by omega))

end Theory.GroupTheory
