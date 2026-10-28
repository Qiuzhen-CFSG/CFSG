module
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.SymplecticSix.OrderRank

/-!
# Five-rank bounds for J₄ and binary symplectic six-space

The certified J₄ order has exactly one factor five. The hyperbolic-pair
recurrence gives order 1451520 for Sp₆(2), again with only one factor five;
the central quotient order divides that matrix-group order. Lagrange's
prime-rank bound therefore gives five-rank at most one in both literal
models, without an exceptional isomorphism or a two-rank computation.

Source application: Aschbacher--Smith 4.4.12, printed p.622.
-/

public section
namespace Theory.SpecificGroups.FiniteModelFiveRank
open Theory.GroupTheory

/-- The actual J₄ matrix carrier has five-rank at most one. -/
theorem j4_le_one : primeRank 5 Janko4.Model ≤ 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply primeRank_le_of_prime_pow_not_dvd
  rw [Janko4.Cardinality.model_card]
  norm_num

/-- The actual projective symplectic six-space over any binary field has five-rank at most one. -/
theorem binary_symplectic_six_le_one {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) : primeRank 5 (SymplecticSix.PSp F) ≤ 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply primeRank_le_of_prime_pow_not_dvd
  intro hdiv
  have hd := hdiv.trans (Subgroup.card_quotient_dvd_card (Subgroup.center (SymplecticSix.Sp F)))
  rw [SymplecticSix.card_sp_of_card_two hF] at hd
  norm_num at hd

end Theory.SpecificGroups.FiniteModelFiveRank
