module

public import Theory.SpecificGroups.ProjectiveLinearThree
public import Theory.SpecificGroups.Symplectic.FundamentalPlane
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne

/-!
# Three-divisibility of symplectic groups in every rank

Rank one is the actual projective SL₂ carrier. In larger ranks a fundamental
SL₂ injects into the projective symplectic group, and its projective quotient
already has order divisible by three. Thus complete order formulas are unnecessary.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1.1.5(3) and 15.3.34; the full classical catalogue is used in the K-group premise.
-/

public section
namespace Theory.SpecificGroups.PrimeToFifteen.Classical
open Matrix Subgroup
open scoped MatrixGroups

/-- Every positive-rank projective symplectic carrier has order divisible by three. -/
theorem symplectic_three_dvd (F : Type*) [Field F] {r : ℕ} (hr : 1 ≤ r) :
    3 ∣ Nat.card (Matrix.PSp4Three.PSp r F) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  by_cases hk : k = 0
  · subst k
    rw [Nat.card_congr (SymplecticRoot.rankOneProjectiveEquiv (F := F)).toEquiv]
    exact ProjectiveSpecialLinearGroup.three_dvd_card F 2 le_rfl
  · have h : 3 ∣ Nat.card SL(2,F) :=
      (ProjectiveSpecialLinearGroup.three_dvd_card F 2 le_rfl).trans
        (center SL(2,F)).card_quotient_dvd_card
    exact h.trans (Subgroup.card_dvd_of_injective
      (Symplectic.FundamentalPlane.fundamental (F := F) k)
      (Symplectic.FundamentalPlane.fundamental_injective k (by omega)))

end Theory.SpecificGroups.PrimeToFifteen.Classical
