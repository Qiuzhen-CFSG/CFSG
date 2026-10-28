module
public import Theory.Mathieu.M12.SylowOvergroups.RankTwoCoverage
public import Theory.GroupTheory.TwoPrimeSolvable
public import Theory.GroupTheory.SylowOvergroupSolvability

/-!
# Solvability of proper Sylow overgroups in M₁₂

The concrete Sylow-overgroup calculation bounds every proper overgroup's
order by a divisor of 192. Burnside's two-prime theorem therefore makes
each such overgroup solvable. The same conclusion lifts through an actual
two-core quotient isomorphic to M₁₂: the kernel lies in the full Sylow,
so the image of a proper Sylow overgroup is still proper.

The consumer is the containing-component exclusion in Aschbacher–Smith
5.2.2, printed pp.648–649, using A.3.12, pp.47–48. The concrete model
calculation and its source attribution are in `RankTwoCoverage`.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups

/-- Every proper overgroup of a full Sylow two-subgroup of M₁₂ is solvable. -/
theorem isSolvable_of_ne_top (S : Sylow 2 M12) (P : Subgroup M12)
    (hSP : (S : Subgroup M12) ≤ P) (hP : P ≠ ⊤) : Group.IsSolvable P := by
  have hd := card_dvd_192_of_ne_top P hP ⟨S,hSP⟩
  apply isSolvable_of_prime_dvd_card_eq_two_or_prime P Nat.prime_three
  intro p hp hpP
  have hh : p ∣ 2 ^ 6 * 3 := hpP.trans hd
  rcases hp.dvd_mul.mp hh with htwo | hthree
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow htwo))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hthree)

/-- Retain the entire two-core of a group with literal M₁₂ quotient. -/
theorem isSolvable_of_twoCore_quotient {G : Type*} [Group G] [Finite G]
    (e : (G ⧸ pCore 2 G) ≃* M12) (S : Sylow 2 G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hP : P ≠ ⊤) : Group.IsSolvable P :=
  isSolvable_proper_sylow_overgroup_of_twoCore_quotient
    (isSolvable_proper_sylow_overgroup_of_equiv e isSolvable_of_ne_top) S P hSP hP

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
