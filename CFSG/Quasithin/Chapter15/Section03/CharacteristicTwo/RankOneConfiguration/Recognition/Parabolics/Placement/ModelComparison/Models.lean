module

public import Theory.SpecificGroups.PSL2.OuterSolvable.BinaryCyclic
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.LinearFactor
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.NumberTheory.BinaryTorusParity
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels

/-!
# Outer groups of the rank-one linear alternatives

Semilinear coverage makes the binary PSL₂ outer group cyclic. For odd-degree
binary PSL₃, a diagonal outer element has order dividing both three and
q−1, hence is trivial. The actual outer quotient is then abelian by the
field–graph calculation. The canonical central quotient equivalences
transfer these assertions to the special linear carriers used by B.5.6.

Source: Aschbacher–Smith, proof of 15.3.27(2), printed p.1131; GLS3,
Theorem 2.5.12 and §2.7. Imported matrix results retain their ATLAS attribution.
-/

public section
open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison

/-- Transport commutativity through an actual multiplicative equivalence. -/
theorem commutative_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) [IsMulCommutative B] : IsMulCommutative A := by
  apply IsMulCommutative.of_comm
  intro a b
  apply e.injective
  rw [map_mul, map_mul, mul_comm]

/-- Transport triviality of the intrinsic center. -/
theorem center_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hb : center B = ⊥) : center A = ⊥ := by
  rw [← Subgroup.card_eq_one, Nat.card_congr (centerCongr e).toEquiv, hb]
  exact Nat.card_unique

/-- The actual binary SL₂ outer quotient is abelian. -/
theorem linearTwo_outer_commutative (F : Type*) [Field F] [Finite F] [CharP F 2] :
    IsMulCommutative (MulAut.Outer SL(2, F)) := by
  let : IsCyclic (MulAut.Outer (Theory.PSL2.Group F)) :=
    Theory.PSL2.OuterSolvable.outer_isCyclic_of_field_coverage
      BenderSuzuki.ZD.Linear.semilinear_coverage
  exact commutative_of_equiv (MulAut.outerCongr (Theory.PSL2.sl2QuotientEquiv F))

open Matrix.PSL3.OuterSolvable

/-- The diagonal outer image vanishes in odd binary degree. -/
theorem linearThree_diagonal_bot (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n) : innerDiagonalOuter F = ⊥ := by
  apply eq_bot_iff.mpr
  rintro z ⟨g, rfl⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  have h3 : q (linearConj F g) ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Matrix.PSL3.CartanActions.ResidualInner.linearConj_cube_inner g)
  have hu : q (linearConj F g) ^ Nat.card Fˣ = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Matrix.PSL3.CartanActions.SixCommutators.linearConj_pow_inner F g)
  have hc : Nat.Coprime 3 (Nat.card Fˣ) := by
    rw [Nat.card_units, hF]
    exact Nat.BinaryTorusParity.coprime_three_sub_one hn
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc
    (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hu))

/-- The actual SL₃ outer quotient is abelian in odd binary degree. -/
theorem linearThree_outer_commutative (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n) :
    IsMulCommutative (MulAut.Outer SL(3, F)) := by
  have hcov : standard F = ⊤ := standard_eq_top_of_two_power_card F hn.pos hF
  let : (innerDiagonalOuter F).Normal := innerDiagonalOuter_normal_of_coverage F hcov
  have ho := outerDiagonalQuotient_isMulCommutative_of_coverage F hcov
  let := ho
  let q := QuotientGroup.mk' (innerDiagonalOuter F)
  have hq : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_mk', linearThree_diagonal_bot F hn hF]
  let : IsMulCommutative (MulAut.Outer PSL(3, F)) := IsMulCommutative.of_comm (fun a b =>
    hq (by rw [map_mul, map_mul, mul_comm]))
  have hz : center SL(3,F) = ⊥ := by
    apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr
    rw [hF, Nat.BinaryTorusParity.two_pow_mod_three, Nat.odd_iff.mp hn]
    decide
  exact commutative_of_equiv (MulAut.outerCongr
    (Matrix.SL3.equivProjectiveOfCenterEqBot F hz))

open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- The actual linear models in comparison case (i), with their parameters.
No rank assertion or outer-automorphism conclusion is built into this predicate. -/
inductive RegularModel (H : Type*) [Group H] : Prop
  | linearTwo (F : BinaryField) (equiv : H ≃* SL(2, F.Carrier))
  | linearThree (F : BinaryField) (odd_degree : Odd F.degree)
      (equiv : H ≃* SL(3, F.Carrier))

/-- Both model facts required by the inner-action argument. -/
theorem RegularModel.center_and_outer {H : Type*} [Group H] (h : RegularModel H) :
    center H = ⊥ ∧ IsMulCommutative (MulAut.Outer H) := by
  cases h with
  | linearTwo F e =>
    let := linearTwo_outer_commutative F.Carrier
    exact ⟨center_bot_of_equiv e BenderSuzuki.Converse.center_SL2_eq_bot,
      commutative_of_equiv (MulAut.outerCongr e)⟩
  | linearThree F hn e =>
    let := linearThree_outer_commutative F.Carrier hn F.card_eq
    have hz : center SL(3, F.Carrier) = ⊥ := by
      apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mpr
      rw [F.card_eq, Nat.BinaryTorusParity.two_pow_mod_three, Nat.odd_iff.mp hn]
      decide
    exact ⟨center_bot_of_equiv e hz, commutative_of_equiv (MulAut.outerCongr e)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison
