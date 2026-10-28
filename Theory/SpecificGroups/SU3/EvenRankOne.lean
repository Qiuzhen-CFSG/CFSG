module
public import Theory.SpecificGroups.SU3.BinaryCubicRankParity
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter
public import Theory.SpecificGroups.ThreeDivisibility.Classical
public import Theory.GroupTheory.PrimeRankZero
public import BenderSuzuki.External.Huppert.II.theorem_10_13
/-!
# Even-degree binary PSU₃ as a centerless rank-one component

The actual projective unitary carrier has three-rank one: its cubic
Sylow groups are cyclic and an explicit cubic element gives the lower
bound. The binary projective comparison makes it centerless. Its
semilinear automorphisms have cyclic outer quotient in even degree;
the existing simplicity theorem discharges that calculation's hypothesis.
All statements keep the supplied Hermitian form and Frobenius involution.

Source: Aschbacher--Smith 12.6.31, printed p.836; Huppert II.10.13;
GLS3 Theorem 2.5.12 and Section 2.7. The original point-residual application
is in Chapter12.Section06.NaturalSource.AbelianNormalUnitaryEven.
-/
public section
open Subgroup Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryCubicRankParity
variable {F : Type*} [Field F] [Finite F]

/-- The actual even-degree binary PSU₃ model has rank one and cyclic outer group. -/
theorem even_rank_one_outer (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hc : ∀ x, J.conj x = x ^ (2 ^ n)) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ ∧
      primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) = 1 ∧
      IsCyclic (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hF hc
  have hq : 2 < 2 ^ n := (by decide : 2 < 2 ^ 2).trans_le
    (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J (2 ^ n) hq hF hf
  have hupper := rank_le_one_of_even J (by omega) hF hc he
  have hne : primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) ≠ 0 := by
    intro hz
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz
      (Theory.SpecificGroups.ThreeDivisibility.unitary_three_dvd J n (by omega) hF hc)
  exact ⟨EvenProjectiveComparison.center_eq_bot J (by omega) hF hc, by omega,
    EvenSemilinear.outer_isCyclic_of_even J (by omega) he hF hc⟩
end BenderSuzuki.MatrixGroups.HermitianForm.BinaryCubicRankParity
