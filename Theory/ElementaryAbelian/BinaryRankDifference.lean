module

public import Theory.ElementaryAbelian.BinaryQuotientRank
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Binary rank differences are quotient ranks

For elementary abelian two-groups `A ≤ V`, subtracting the logarithms of
their orders gives the binary rank of the actual quotient `V/A`.
The proof takes logarithms in the subgroup-index cardinal identity, using
the already established power-of-two formula for the quotient dimension.

This connects the cardinal rank estimates in Aschbacher–Smith B.2.4 with
the quotient ranks in E.5.5 (combined manuscript, printed pp.75 and 244).
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The difference of binary ranks equals the logarithm of the relative index.
The latter is the dimension of `V/A` by `log_relIndex_eq_quotient_finrank`. -/
public theorem log_card_sub_log_card_eq_log_relIndex (V A : Subgroup G)
    [IsElementaryAbelian 2 V] (hAV : A ≤ V) :
    Nat.log 2 (Nat.card V) - Nat.log 2 (Nat.card A) = Nat.log 2 (A.relIndex V) := by
  let _ : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.of_le hAV
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hprod : Nat.card A * A.relIndex V = Nat.card V := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) A V bot_le hAV
  rw [hn, relIndex_eq_two_pow_quotient_finrank, ← pow_add] at hprod
  have hlog := congrArg (Nat.log 2) hprod
  rw [Nat.log_pow Nat.one_lt_two] at hlog
  rw [hn, Nat.log_pow Nat.one_lt_two, log_relIndex_eq_quotient_finrank]
  omega

end Subgroup
