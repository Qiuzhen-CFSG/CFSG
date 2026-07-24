/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Huppert.IV.Basic

/-!
# Huppert IV.5.4(c)

Book clauses for the two-prime order and the normal Sylow `p`-subgroup
exponent conclusion.
-/

namespace BenderSuzuki
namespace External

universe u

/-- Huppert IV.5.4(c), order clause: the group order has only `p` and one
other prime divisor. -/
public theorem huppert_IV_5_4_c_two_prime_order
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (_hproper : ∀ H : Subgroup Q, H ≠ ⊤ → HasNormalPComplement p H)
    (_hnot : ¬ HasNormalPComplement p Q)
    (hsource : ∃ r a b : ℕ, r.Prime ∧ r ≠ p ∧ 0 < a ∧ 0 < b ∧
      Nat.card Q = p ^ a * r ^ b) :
    ∃ r a b : ℕ, r.Prime ∧ r ≠ p ∧ 0 < a ∧ 0 < b ∧
      Nat.card Q = p ^ a * r ^ b :=
  hsource

/-- Huppert IV.5.4(c), normal Sylow exponent clause: some Sylow `p`-subgroup
is normal; if `p` is odd it has exponent `p`, and if `p = 2` it has exponent at
most `4`. -/
public theorem huppert_IV_5_4_c_normal_sylow_exponent
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (_hproper : ∀ H : Subgroup Q, H ≠ ⊤ → HasNormalPComplement p H)
    (_hnot : ¬ HasNormalPComplement p Q)
    (hsource : ∃ S : Sylow p Q, (S : Subgroup Q).Normal ∧
      (p ≠ 2 → ∀ x : S, x ^ p = 1) ∧
        (p = 2 → ∀ x : S, x ^ 4 = 1)) :
    ∃ S : Sylow p Q, (S : Subgroup Q).Normal ∧
      (p ≠ 2 → ∀ x : S, x ^ p = 1) ∧
        (p = 2 → ∀ x : S, x ^ 4 = 1) :=
  hsource

end External
end BenderSuzuki
