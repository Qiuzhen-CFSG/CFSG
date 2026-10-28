module

public import Stellmacher.Recognition.SuzukiThreeBruhat
public import Stellmacher.Recognition.SuzukiThreeRootGroup
public import Stellmacher.Recognition.SuzukiThreeTorus
public import Theory.GroupTheory.PGroup.PrimeCubeCenter

/-!
# Local structure for Suzuki's degree-28 action

The original action hypotheses imply that the root group has exponent three,
is noncommutative, and has center of order three. There is a swapping involution
whose conjugation on the two-point stabilizer is the fifth-power map.

The root-group and torus modules supply the exponent, noncommutativity and
swapping involution. Since the root group has order 27, the prime-cube center
theorem supplies the remaining center order. `local_structure` assembles these
conclusions without assuming simplicity or unitary recognition.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
 group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Sections II–III, Lemmas 7–12.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- In this action, noncommutativity already forces the center order. -/
public theorem root_center_card_of_noncommuting
    (hncomm : ∃ x y : Q, x * y ≠ y * x) : Nat.card (Subgroup.center Q) = 3 := by
  let : Finite Q := Nat.finite_of_card_ne_zero (by rw [h.root_card]; decide)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply Subgroup.card_center_eq_prime_of_card_eq_prime_cube
    (by simpa using h.root_card)
  intro hcomm
  obtain ⟨x, y, hxy⟩ := hncomm
  exact hxy (isMulCommutative_iff.mp hcomm x y)

/-- Suzuki's local structure at q = 3, from the original action hypotheses. -/
public theorem local_structure [FaithfulSMul G Ω] (b : Ω) (hb : b ≠ a) :
    SuzukiThreeLocalStructure G Ω a b Q := by
  have hncomm := h.root_noncommuting b hb
  exact
    { root_cube := h.root_cube b hb
      root_noncommuting := hncomm
      root_center_card := h.root_center_card_of_noncommuting hncomm
      swap_exists := h.exists_swap_pow_five b hb }

end Stellmacher.Recognition.SuzukiThreeHypotheses
