module

public import Theory.GroupTheory.NoNormalFourNormalComplement
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeExclusion.CenterDivisor

/-!
# Discharging the no-normal-four branch of the Sylow-center argument

The order formula in odd prime binary degree excludes three. The normal
two-complement theorem for Sylow groups without normal fours therefore
discharges the literal `hnoFour` premise of the existing center-divisor
consumer. Only Thompson's normal-four fusion consequence remains explicit;
its proof and the final source assembly belong to the parent development.

Source: GLS, Volume 4, Chapter 1, Lemma 3.10 and (3G),
`refs/KGroup/GLS4/Chapter1.tex`, lines 450–462.
-/

open Subgroup MulAction

namespace MulAction.SemilinearPointStabilizer.PrimeExclusion

/-- The center-divisor consumer after discharging its normal-complement
premise. The remaining normal-four hypothesis is relative to S and uses
the actual ambient image for its normalizer. -/
public theorem noncyclic_center_and_divisor_of_normal_four_analysis
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F]
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hn : n.Prime) (hodd : Odd n) (hn3 : 3 < n)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hcore : pCore 2 X = ⊥)
    (hfusion : ∀ z w : X, orderOf z = 2 → orderOf w = 2 → IsConj z w)
    (S : Sylow 2 X)
    (hfour : IsCyclic (center S) →
      ∀ U : Subgroup S, U.Normal → IsElementaryAbelian 2 U → Nat.card U = 4 →
        3 ∣ Nat.card (normalizer (U.map (S : Subgroup X).subtype : Set X))) :
    ¬ IsCyclic (center S) ∧
      ∃ r : ℕ, 1 < r ∧ r ≤ n ∧ 2 ^ r - 1 ∣ Nat.card (normalizer (S : Set X)) := by
  let : IsPreprimitive X F := isPreprimitive_of_is_two_pretransitive htwo
  exact noncyclic_center_and_divisor_of_local_analysis c htwo hn hodd hn3 hF hΓ
    hcore hfusion S
    (fun hnoncyclic hno => S.hasNormalTwoComplement_of_no_normal_four hnoncyclic
      (three_not_dvd_card c hn hodd hn3 hF hΓ) hno) hfour

end MulAction.SemilinearPointStabilizer.PrimeExclusion
