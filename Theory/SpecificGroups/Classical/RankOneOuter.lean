module

public import Theory.SpecificGroups.PSL2.OuterSolvable.BinaryCyclic
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner

/-!
# Outer groups for the classical three-rank-one alternatives

Binary PSL₂ has cyclic outer group by the proved inner-field coverage.
For prime-field PSL₂, the field part vanishes and the cyclic unit group
maps onto the actual outer quotient. In PSL₃, a diagonal outer element has
both cube one and order dividing the field-unit order. Coprimality kills
the entire diagonal image, leaving the proved abelian field-graph quotient.

The arguments use the actual matrix groups and their full automorphism
coverage. They require no classification or simplicity certification.
These are the linear model calculations used in Aschbacher--Smith,
15.3.43(ii), printed p.1139 (combined manuscript, 1 March 2004).
Source for the automorphism structure: GLS3, Theorem 2.5.12 and §2.7,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Subgroup
open scoped MatrixGroups IsMulCommutative

namespace Theory.PSL2.OuterSolvable

/-- The actual outer group of finite-field PSL₂ in characteristic two is cyclic. -/
theorem charTwo_outer_isCyclic {F : Type*} [Field F] [Finite F] [CharP F 2] :
    IsCyclic (MulAut.Outer (Group F)) :=
  outer_isCyclic_of_field_coverage BenderSuzuki.ZD.Linear.semilinear_coverage

/-- Prime-field PSL₂ has cyclic outer group, including the small primes. -/
theorem prime_outer_isCyclic {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    IsCyclic (MulAut.Outer (Group F)) := by
  by_cases hc : ringChar F = 2
  · let : CharP F 2 := ringChar.of_eq hc
    exact charTwo_outer_isCyclic
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Group F))
  let d := q.comp (diagonalAutHom (K := F))
  apply isCyclic_of_surjective d
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (Group F)) x
  obtain ⟨g, u, σ, ha⟩ := OddCoverage.semilinear_coverage_of_root_reductions
    (OddCoverage.exists_root_weyl_one_normalization hc)
    (fun b hU _ h1 => OddCoverage.rootParameter_mul hc b hU h1) a
  have hσ := FiniteField.ringAut_eq_one_of_card_prime hp hF σ
  have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  refine ⟨u, ?_⟩
  change q (diagonalAutHom u) = q a
  rw [ha, hσ, map_one, mul_one, map_mul, hg, one_mul]

end Theory.PSL2.OuterSolvable

namespace Matrix.PSL3.OuterSolvable
variable (F : Type*) [Field F]

/-- The diagonal outer image vanishes when the unit-group order is prime to three. -/
theorem innerDiagonalOuter_eq_bot_of_coprime
    (hcop : Nat.Coprime 3 (Nat.card F - 1)) : innerDiagonalOuter F = ⊥ := by
  apply bot_unique
  rintro x ⟨g, rfl⟩
  apply mem_bot.mpr
  have hthree : linearOuterAction F g ^ 3 = 1 := by
    change (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) (linearConj F g)) ^ 3 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Matrix.PSL3.CartanActions.ResidualInner.linearConj_cube_inner g)
  have hfield : linearOuterAction F g ^ (Nat.card F - 1) = 1 := by
    rw [← map_pow]
    apply det_ker_le_linearOuterAction_ker F
    change Matrix.GeneralLinearGroup.det (g ^ (Nat.card F - 1)) = 1
    rw [map_pow, ← Nat.card_units F]
    exact pow_card_eq_one'
  apply orderOf_eq_one_iff.mp
  exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
    (orderOf_dvd_of_pow_eq_one hthree) (orderOf_dvd_of_pow_eq_one hfield))

/-- Opposite-sign binary PSL₃ has abelian actual outer automorphism group. -/
theorem outer_isMulCommutative_of_two_power_card_mod_three [Finite F]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hm : 2 ^ n % 3 = 2) :
    IsMulCommutative (MulAut.Outer PSL(3,F)) := by
  have hcop : Nat.Coprime 3 (Nat.card F - 1) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    omega
  have hc := standard_eq_top_of_two_power_card F hn hF
  let := innerDiagonalOuter_normal_of_coverage F hc
  let := outerDiagonalQuotient_isMulCommutative_of_coverage F hc
  let e := (QuotientGroup.quotientMulEquivOfEq
    (innerDiagonalOuter_eq_bot_of_coprime F hcop)).trans QuotientGroup.quotientBot
  apply IsMulCommutative.of_comm
  intro x y
  apply e.symm.injective
  simp only [map_mul]
  exact mul_comm _ _

end Matrix.PSL3.OuterSolvable
