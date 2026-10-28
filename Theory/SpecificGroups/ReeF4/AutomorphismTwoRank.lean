module

public import Theory.GroupTheory.PrimeRankAutomorphismOrder
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.FixedBruhat
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FixedGeometryTransport
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.FieldAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms

/-!
# An order-based two-rank estimate for Ree automorphisms

The positive fixed subgroup is Sylow by the proved odd-index geometry, and
the actual root-coordinate calculation gives its order 2^(12*(2*k+1)).
If every involutory automorphism is inner, each elementary subgroup of the
automorphism group has order dividing the Ree group order and therefore
at most this Sylow order. No simplicity or centerlessness is needed.

The resulting bound 12*n is weaker than the source's 5*n, but still gives
2*(12*n+1) < 26*n for n = 2*k+1 with k >= 1. The numerical comparison is
proved below. The final bounds discharge involution innerness using
ParabolicAmalgam.OuterLocal.LargeAutomorphisms, whose fixed geometry and
compatible local actions prove it for every k >= 1. The conditional
innerness and inner-times-field adapters remain available separately.
The intrinsic Sylow and group-rank statements also hold for the full binary
Ree group; that group is not identified with the simple Tits endpoint.

Sources: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
p.356 and F.1.12, pp.263–264; GLS3, Section 2.5. The root-order calculation
is re-exported from ParabolicAmalgam.RadicalOrders.
-/

public section
noncomputable section

namespace ReeF4.AutomorphismTwoRank

open Parabolics Theory.GroupTheory
open Parabolics.OuterLocal

/-- The fixed positive subgroup has odd index in the canonical matrix carrier. -/
theorem unipotent_index_odd (k : ℕ) : Odd (unipotent k).index :=
  LargeAutomorphisms.unipotent_index_odd_of_standard (canonicalLocalBlockInput k)
    (LargeLocalSeeds.FixedBruhat.standardUnipotent_index_odd (canonicalLocalBlockInput k))

/-- The actual positive fixed subgroup, with its proved Sylow maximality. -/
def sylow (k : ℕ) : Sylow 2 (Model k) :=
  sylowOfOddIndex k (unipotent_index_odd k)

/-- The Sylow subgroup has the order given by its twelve fixed root coordinates. -/
theorem sylow_card (k : ℕ) : Nat.card (sylow k) = 2 ^ (12 * (2 * k + 1)) := by
  change Nat.card (unipotent k) = _
  rw [card_unipotent, ← pow_mul, Nat.mul_comm (2 * k + 1) 12]

/-- A coarse intrinsic rank bound, including the full binary endpoint. -/
theorem model_two_rank_le (k : ℕ) : primeRank 2 (Model k) ≤ 12 * (2 * k + 1) := by
  rw [(sylow k).primeRank_eq]
  exact primeRank_le_of_card_le_prime_pow (sylow_card k).le

/-- Innerness of involutions suffices; no automorphism classification is hidden. -/
theorem automorphism_two_rank_le_of_involutions_inner (k : ℕ)
    (hinner : ∀ a : MulAut (Model k), a ^ 2 = 1 → ∃ g : Model k, MulAut.conj g = a) :
    primeRank 2 (MulAut (Model k)) ≤ 12 * (2 * k + 1) :=
  automorphism_primeRank_le_of_prime_order_inner (sylow k) (sylow_card k).le hinner

/-- Two-power inner-times-field coverage supplies the needed involution innerness. -/
theorem automorphism_two_rank_le_of_twoPower_inner_field (k : ℕ)
    (hcoverage : ∀ (a : MulAut (Model k)) (r : ℕ), a ^ (2 ^ r) = 1 →
      ∃ (g : Model k) (j : ℕ), a = MulAut.conj g * fieldAutomorphism k ^ j) :
    primeRank 2 (MulAut (Model k)) ≤ 12 * (2 * k + 1) := by
  apply automorphism_two_rank_le_of_involutions_inner
  intro a ha
  have ha' : a ^ (2 ^ 1) = 1 := by simpa using ha
  obtain ⟨g, j, hj⟩ := hcoverage a 1 ha'
  exact inner_of_twoPower_of_inner_field k a g j 1 hj ha'

/-- At every large Ree parameter, the coarse estimate suffices for degree 26*n. -/
theorem automorphism_two_rank_degree_gap_of_twoPower_inner_field {k : ℕ} (hk : 1 ≤ k)
    (hcoverage : ∀ (a : MulAut (Model k)) (r : ℕ), a ^ (2 ^ r) = 1 →
      ∃ (g : Model k) (j : ℕ), a = MulAut.conj g * fieldAutomorphism k ^ j) :
    2 * (primeRank 2 (MulAut (Model k)) + 1) < 26 * (2 * k + 1) := by
  have h := automorphism_two_rank_le_of_twoPower_inner_field k hcoverage
  omega

/-- Every large Ree carrier has automorphism two-rank at most 12*(2*k+1).
The proved involution coverage discharges the only structural premise. -/
theorem automorphism_two_rank_le {k : ℕ} (hk : 1 ≤ k) :
    primeRank 2 (MulAut (Model k)) ≤ 12 * (2 * k + 1) :=
  automorphism_two_rank_le_of_involutions_inner k
    (LargeAutomorphisms.inner_of_sq_eq_one hk)

/-- The unconditional rank bound suffices for the degree-26*n exclusion
at every odd field exponent n = 2*k+1 >= 3. -/
theorem automorphism_two_rank_degree_gap {k : ℕ} (hk : 1 ≤ k) :
    2 * (primeRank 2 (MulAut (Model k)) + 1) < 26 * (2 * k + 1) := by
  have h := automorphism_two_rank_le hk
  omega

end ReeF4.AutomorphismTwoRank
