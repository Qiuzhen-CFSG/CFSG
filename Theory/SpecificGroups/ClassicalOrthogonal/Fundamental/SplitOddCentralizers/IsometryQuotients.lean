module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.Standard
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.RankOne

/-!
# Prime-to-characteristic full isometry quotients

For the actual split and odd quadratic forms, the index of the Siegel-generated
Omega subgroup in the full isometry group is prime to the odd characteristic.
Consequently Omega is exactly the full group's prime-to-p residual. Two
hyperbolic pairs give the general reflection argument; singular-line transport
and the explicit SL₂ comparison handle the ternary-dimensional endpoint.
Both Ω₃(3) and Ω₄⁺(3) are included, without any perfectness hypothesis.

These are the complementary full-isometry facts used by the projective block
centralizer calculation in Aschbacher–Smith A.2.17, printed p.39. They do not
identify a projective centralizer. Quadratic forms and Omega conventions are
those of GLS3 §2.7.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.SplitOddBlocks.IsometryQuotients
variable {F : Type*} [Field F] [Finite F]
variable (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2)

include hp in
/-- Every positive odd rank has prime-to-characteristic full-isometry index. -/
theorem elementary_index_coprime_formB (k : ℕ) (hk : 1 ≤ k) :
    Nat.Coprime p (elementarySubgroup (formB k F)).index := by
  by_cases h : k = 1
  · subst k
    exact RankOne.index_coprime p ((Fact.out : p.Prime).odd_of_ne_two hp)
  · have htwo : 2 ≤ k := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le htwo
    rw [Nat.add_comm 2 n]
    exact elementary_index_coprime_formB_stable (F := F) p hp n

include hp in
/-- Omega is the prime-to-p residual of the actual full odd isometry group. -/
theorem primeToResidual_formB (k : ℕ) (hk : 1 ≤ k) :
    Subgroup.primeToResidual p (quadraticIsometrySubgroup (formB k F)) =
      elementarySubgroup (formB k F) :=
  primeToResidual_eq_elementary_of_index _ p (elementary_index_coprime_formB p hp k hk)

/-- The Ω₃(3) endpoint, on the literal full isometry carrier. -/
theorem primeToResidual_formB_one_ternary :
    Subgroup.primeToResidual 3 (quadraticIsometrySubgroup (formB 1 (ZMod 3))) =
      elementarySubgroup (formB 1 (ZMod 3)) :=
  primeToResidual_formB 3 (by decide) 1 (by decide)

/-- The Ω₄⁺(3) endpoint, on the literal full isometry carrier. -/
theorem primeToResidual_formD_two_ternary :
    Subgroup.primeToResidual 3 (quadraticIsometrySubgroup (formD 2 (ZMod 3))) =
      elementarySubgroup (formD 2 (ZMod 3)) :=
  primeToResidual_formD 3 (by decide) 2 (by decide)

end ClassicalOrthogonal.Fundamental.SplitOddBlocks.IsometryQuotients
