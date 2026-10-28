module

public import Theory.GroupTheory.NormalFourThreeDivisor
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeExclusion.CenterDivisor

/-!
# The normal-four branch of the semilinear Sylow-center argument

Thompson's normal-four divisor discharges the literal `hfour` premise of
`noncyclic_center_and_divisor_of_local_analysis`. The separate normal-complement
input for a Sylow subgroup without a normal four remains explicit. The source
assembly owner supplies that independent branch and the involution fusion.

Source: GLS, Volume 4, Chapter 1, Lemma 3.10 and (3G),
`refs/KGroup/GLS4/Chapter1.tex`, lines 450–462.
-/

open Subgroup MulAction
namespace MulAction.SemilinearPointStabilizer.PrimeExclusion

/-- The center and normalizer divisor follow once the independent no-normal-four
normal-complement branch is supplied. Thompson's normal-four branch is proved. -/
public theorem noncyclic_center_and_divisor_of_no_normal_four_analysis
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F]
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hn : n.Prime) (hodd : Odd n) (hn3 : 3 < n)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hcore : pCore 2 X = ⊥)
    (hfusion : ∀ z w : X, orderOf z = 2 → orderOf w = 2 → IsConj z w)
    (S : Sylow 2 X)
    (hnoFour : ¬ IsCyclic S →
      (¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4) →
      HasNormalPComplement 2 X) :
    ¬ IsCyclic (center S) ∧
      ∃ r : ℕ, 1 < r ∧ r ≤ n ∧ 2 ^ r - 1 ∣ Nat.card (normalizer (S : Set X)) := by
  apply noncyclic_center_and_divisor_of_local_analysis c htwo hn hodd hn3
    hF hΓ hcore hfusion S hnoFour
  intro hcenter U hUn hUe hU
  exact S.three_dvd_normalizer_card_of_normal_four hcenter hfusion U hU

end MulAction.SemilinearPointStabilizer.PrimeExclusion
