module

public import Theory.Mathieu.M12.A5Fixer.Inputs
public import Theory.GroupAction.AutomorphismFixerCardinality
public import Mathlib.Tactic.NormNum

/-!
# Reducing the M₁₂–A₅ fixer to intrinsic model calculations

The inner centralizer bound and outer-index bound give an upper bound of
four for the full abstract automorphism fixer. The supplied lower bound
therefore makes its order exactly four. An element of order four in that
fixer would have a fixed subgroup containing the actual A₅, whose order
is divisible by five. The order-four fixed-subgroup exclusion rules this
out and gives exponent two.

The three inputs in `Inputs` remain explicit. This conditional assembly is
not yet the intrinsic M₁₂ theorem: they must all be proved before its use
in Aschbacher–Smith 16.3.5 (combined manuscript of 1 March 2004, printed
pp.1178–1179). It includes outer automorphisms throughout and uses no
permutation-normalizer proxy for the full automorphism group.
-/

public section
namespace Sporadic.Mathieu.M12A5Fixer
open Subgroup

/-- The two genuine cardinality calculations bound the full automorphism fixer. -/
theorem card_le_four_of_bounds (hinner : InnerCentralizerBound)
    (houter : OuterIndexBound) (P : Subgroup M12)
    (e : P ≃* alternatingGroup (Fin 5)) :
    Nat.card (fixingSubgroup (MulAut M12) (P : Set M12)) ≤ 4 :=
  (MulAut.card_fixingSubgroup_le_centralizer_mul_outer_index P).trans
    (show Nat.card (centralizer (P : Set M12)) *
      (MulAut.innerSubgroup M12).index ≤ 4 from
        Nat.mul_le_mul (hinner P ⟨e⟩) houter)

/-- Conditional assembly for the exact intrinsic contract. The concrete model
obligations in all three parameters remain to be discharged. -/
theorem bound_and_square_of_inputs (hinner : InnerCentralizerBound)
    (houter : OuterIndexBound) (hfour : OrderFourFixedFiveExclusion)
    (P : Subgroup M12) (e : P ≃* alternatingGroup (Fin 5))
    (hlower : 4 ≤ Nat.card (fixingSubgroup (MulAut M12) (P : Set M12))) :
    Nat.card (fixingSubgroup (MulAut M12) (P : Set M12)) ≤ 4 ∧
      ∀ a : fixingSubgroup (MulAut M12) (P : Set M12), a ^ 2 = 1 := by
  let F := fixingSubgroup (MulAut M12) (P : Set M12)
  have hbound : Nat.card F ≤ 4 := card_le_four_of_bounds hinner houter P e
  refine ⟨hbound, ?_⟩
  have hcard : Nat.card F = 4 := Nat.le_antisymm hbound hlower
  have hP : Nat.card P = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  intro a
  have hle : P ≤ (a : MulAut M12).fixedSubgroup := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup (a : MulAut M12) x).mpr
    exact (mem_fixingSubgroup_iff (MulAut M12)).mp a.property x hx
  have hfive : 5 ∣ Nat.card (a : MulAut M12).fixedSubgroup :=
    (show 5 ∣ Nat.card P by rw [hP]; decide).trans (card_dvd_of_le hle)
  have hnot : orderOf a ≠ 4 := by
    intro h
    apply hfour a _ hfive
    exact (orderOf_injective F.subtype Subtype.val_injective a).trans h
  have hd : orderOf a ∣ 4 := hcard ▸ orderOf_dvd_natCard a
  have htwo : orderOf a ∣ 2 := by
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (show orderOf a ∣ 2 ^ 2 from hd)
    have hk' : k ≤ 1 := by
      by_contra hn
      have hk2 : k = 2 := by omega
      subst k
      exact hnot he
    exact he ▸ (pow_dvd_pow 2 hk')
  exact orderOf_dvd_iff_pow_eq_one.mp htwo

end Sporadic.Mathieu.M12A5Fixer
