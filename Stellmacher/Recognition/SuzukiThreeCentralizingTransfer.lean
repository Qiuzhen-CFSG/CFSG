module

public import Stellmacher.Recognition.SuzukiThreeCentralizingFusion
public import Theory.GroupTheory.SevenCentralizerIndexFour
public import BenderSuzuki.External.Hall.IndexFour
public import Stellmacher.Recognition.SuzukiThreeWholeTorusTransfer
public import Stellmacher.Recognition.SuzukiThreeProperTorusTransfer

/-!
# The final index-four obstruction in the centralizing-swap case

The involution centralizer census excludes every normal subgroup of index
four. This is the final contradiction in the transfer argument of Suzuki
(1965), Section II, Lemma 3. The common torus-fusion calculation is re-exported
here and supplies the normalizer calculation for both transfer branches.

The whole-torus branch now gives this contradiction directly. In the proper
branch we use the order-eight obstruction on the four fixed points of a torus
involution. The case-split interface below isolates the remaining fixed-point
census, without assuming a transfer conclusion in that branch.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- An index-four transfer kernel contradicts the involution centralizer census. -/
public theorem centralizing_transfer_index_four_obstruction
    [FaithfulSMul G Ω]
    (hc : ∀ j : G, orderOf j = 2 →
      Nat.card (Subgroup.centralizer ({j} : Set G)) = 96)
    (N : Subgroup G) [N.Normal] : N.index ≠ 4 := by
  let : Finite G := h.finite_group
  apply Subgroup.index_ne_four_of_card_6048_of_seven_free_involution_centralizers
    h.group_card (fun j hj => ?_) N
  rw [hc j hj]
  decide

/-- The whole-torus transfer kernel is incompatible with the census. -/
public theorem false_of_centralizing_swap_of_wholeTorus
    [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hc : ∀ j : G, orderOf j = 2 →
      Nat.card (Subgroup.centralizer ({j} : Set G)) = 96)
    (hu : ∃ u : Q, u ≠ 1 ∧ ∀ k : stabilizer (stabilizer G a) b,
      Commute ((u : stabilizer G a) : G) ((k : stabilizer G a) : G)) :
    False := by
  obtain ⟨N, hN, hindex⟩ :=
    h.exists_normal_index_four_of_wholeTorus b hb t hta htb htK hc hu
  let : N.Normal := hN
  exact h.centralizing_transfer_index_four_obstruction hc N hindex

/-- Assemble the two centralizing-swap branches. Only the proper-torus
branch needs the four-fixed-point census. -/
public theorem false_of_centralizing_swap_of_proper_fixed_census
    [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (ht2 : t ^ 2 = 1)
    (hta : t • a = b) (htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hc : ∀ j : G, orderOf j = 2 →
      Nat.card (Subgroup.centralizer ({j} : Set G)) = 96)
    (hconj : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → IsConj i j)
    (hfour : (¬ ∃ u : Q, u ≠ 1 ∧ ∀ k : stabilizer (stabilizer G a) b,
        Commute ((u : stabilizer G a) : G) ((k : stabilizer G a) : G)) →
      ∀ k : stabilizer (stabilizer G a) b, orderOf k = 8 →
        Nat.card {x : Ω // ((k : stabilizer G a) : G) ^ 4 • x = x} = 4) :
    False := by
  by_cases hu : ∃ u : Q, u ≠ 1 ∧ ∀ k : stabilizer (stabilizer G a) b,
      Commute ((u : stabilizer G a) : G) ((k : stabilizer G a) : G)
  · exact h.false_of_centralizing_swap_of_wholeTorus b hb t hta htb htK hc hu
  · exact h.false_of_centralizing_swap_of_four_fixed b hb t ht2 hta htK hconj (hfour hu)

end Stellmacher.Recognition.SuzukiThreeHypotheses
