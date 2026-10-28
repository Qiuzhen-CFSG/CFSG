module
public import Theory.SpecificGroups.PSL3.QuadraticThreeSylow
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Cubic rank detects the parity of a binary PSL₃ field

In odd field degree the quadratic torus contains a Sylow three-subgroup.
Its cyclicity bounds cubic rank by one. Consequently a binary PSL₃ of
cubic rank at least two has even field degree, the parameter at which
three divides the split torus order.

Source: Aschbacher–Smith, the quadratic-torus calculation in 1.3.4, p.511,
and the split-diagonal alternative of A.3.18, pp.51–53.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.BinaryCubicRankParity
variable {F : Type*} [Field F] [Finite F] {f : ℕ}

/-- Odd binary field degree gives cyclic cubic Sylow subgroups, hence rank at most one. -/
theorem rank_le_one_of_odd (hF : Nat.card F = 2 ^ f) (hf : Odd f) :
    primeRank 3 PSL(3,F) ≤ 1 := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hm : Nat.card F % 3 = 2 := by
    rw [hF, Nat.BinaryTorusParity.two_pow_mod_three,
      if_neg (by have hh := Nat.odd_iff.mp hf; omega)]
  let P : Sylow 3 PSL(3,F) := default
  exact P.primeRank_le_one_of_isCyclic (QuadraticThreeSylow.sylow_three_isCyclic F 2 hm P)

/-- Cubic rank two forces the split, even-degree linear parameter. -/
theorem even_of_rank_two (hF : Nat.card F = 2 ^ f) (hr : 2 ≤ primeRank 3 PSL(3,F)) :
    Even f := by
  apply Nat.not_odd_iff_even.mp
  intro ho
  have hb := rank_le_one_of_odd hF ho
  omega

end Matrix.PSL3.BinaryCubicRankParity
