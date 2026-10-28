module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankSylow
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Two-rank of PSL₃ over an even field

Every elementary abelian subgroup of the upper unitriangular group lies in
one of its two root planes, each of order q². The first plane attains that
bound. The genuine projective embedding identifies this coordinate group
with a Sylow two-subgroup, so PSL₃(2ⁿ) has two-rank 2n.

Source: Aschbacher–Smith, the rank inspection in 16.3.9, printed p.1180;
the root-plane geometry is the calculation in 5.3.5–7, printed p.660.
-/

public section

open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The two root planes attain the upper bound on elementary subgroups of UT₃. -/
theorem unipotent_two_rank {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (U F) = 2 * n := by
  have hcard₁ : Nat.card (V₁ F) = 2 ^ (2 * n) := by
    rw [card_V₁, hF, ← pow_mul, Nat.mul_comm n 2]
  have hcard₂ : Nat.card (V₂ F) = 2 ^ (2 * n) := by
    rw [card_V₂, hF, ← pow_mul, Nat.mul_comm n 2]
  apply le_antisymm
  · apply (primeRank_le_iff_elementary_card_le (U F)).mpr
    intro A hA
    let := hA
    rcases elementary_le_plane F A with h | h
    · exact (Subgroup.card_le_of_le h).trans hcard₁.le
    · exact (Subgroup.card_le_of_le h).trans hcard₂.le
  · exact IsElementaryAbelian.primeRank_ge_of_card (V₁ F) hcard₁

end Matrix.PSL3Even.UnipotentGeometry

namespace Matrix.PSL3Even
variable (F : Type*) [Field F] [Finite F]

/-- Exact two-rank of the actual projective special linear group. -/
theorem two_rank {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 2 * n := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rw [(PSL3.LinearThree.unipotentSylow F hn hF).primeRank_eq]
  change primeRank 2 (PSL3.LinearThree.unipotent F) = _
  rw [← primeRank_equiv 2 (PSL3.LinearThree.unipotentEquiv F)]
  exact UnipotentGeometry.unipotent_two_rank F hF

end Matrix.PSL3Even
