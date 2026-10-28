module

public import Stellmacher.Recognition.SuzukiThreeSquareAction
public import Stellmacher.Recognition.SuzukiThreeInvolutionCensus
public import Stellmacher.Recognition.SuzukiThreeProperTorusTransfer
public import Theory.GroupTheory.SevenCentralizerIndexFour

/-!
# The obstruction to a centralizing point swap

An involutory point swap acts nontrivially on the cyclic two-point stabilizer.
If it centralized that torus, the Bruhat-cell census would give one conjugacy
class of involutions, with centralizers of order 96. The action of an involution
centralizer on its four fixed points then gives the order-eight obstruction
proved in `SuzukiThreeProperTorusTransfer`, excluding the centralizing swap.
Together with the existence of a swapping involution, this supplies the input
for the fifth-power torus-action assembly. The index-four obstruction used in
the whole-torus transfer argument is retained below.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Section II, Lemmas 3 and 6.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- The order-96 involution centralizers exclude the index-four normal
subgroup produced by transfer in Suzuki's exceptional branch. -/
public theorem normal_index_ne_four_of_involution_centralizers
    [FaithfulSMul G Ω]
    (hc : ∀ j : G, orderOf j = 2 →
      Nat.card (Subgroup.centralizer ({j} : Set G)) = 96)
    (N : Subgroup G) [N.Normal] : N.index ≠ 4 := by
  let : Finite G := h.finite_group
  apply Subgroup.index_ne_four_of_card_6048_of_seven_free_involution_centralizers
    h.group_card (fun j hj => ?_) N
  rw [hc j hj]
  decide

/-- Every involutory point swap acts nontrivially on the two-point stabilizer. -/
public theorem swap_conj_nontrivial [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (ht : t ^ 2 = 1)
    (hta : t • a = b) (htb : t • b = a) :
    ∃ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t ≠ ((k : stabilizer G a) : G) := by
  classical
  by_contra hcentral
  push Not at hcentral
  exact h.false_of_centralizing_swap_of_involution_census b hb t ht hta hcentral
    (h.involution_centralizer_card_of_centralizing_swap b hb t ht hta htb hcentral)
    (h.involutions_isConj_of_centralizing_swap b hb t ht hta htb hcentral)

/-- A swapping involution with nontrivial torus action exists for any second point. -/
public theorem exists_swap_nontrivial [FaithfulSMul G Ω] (b : Ω) (hb : b ≠ a) :
    ∃ t : G, t ^ 2 = 1 ∧ t • a = b ∧ t • b = a ∧
      ∃ k : stabilizer (stabilizer G a) b,
        t⁻¹ * ((k : stabilizer G a) : G) * t ≠ ((k : stabilizer G a) : G) := by
  obtain ⟨t, ht, hta, htb⟩ := h.exists_swap b hb
  exact ⟨t, ht, hta, htb, h.swap_conj_nontrivial b hb t ht hta htb⟩

end Stellmacher.Recognition.SuzukiThreeHypotheses
