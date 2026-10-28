module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus.RankObstruction
public import Theory.SpecificGroups.ClassicalUnitary.EvenSmallRanks
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus.Cover
public import CFSG.Quasithin.ChapterA.Section02.EvenLie
public import CFSG.Quasithin.ClassicalModels
public import Theory.LinearAlgebra.FiniteProjectiveMatrixGroup
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTwoLocal

/-!
# The concrete unitary rank steps of A.2.18

The all-primes line-parabolic calculation supplies the existing arithmetic
interface, including the fifth-primary case. A separate odd-prime formulation
uses exactly the bounds supplied by quasithinness of the actual two-local
parabolic. Ordinary ranks are transported through the literal IsPSU model
isomorphisms, and the actual SU5(4) cover is excluded by its involution
centralizer. The cyclic-by-SU3 subgroup at q=4 is exhibited inside the SU
line stabilizer by an explicit multiplicative equivalence onto its image.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, A.2.18,
printed p.40. These are the concrete rank and exceptional-cover steps, not
the classification of covers or the complete lemma. In particular no general
C_((q+1)/gcd(q+1,5)) x SU3(q) Levi splitting is asserted.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie

/-- The concrete line-parabolic rank calculation supplies the original arithmetic interface. -/
theorem unitary_five_field_size_eq_four_of_concrete_parabolic
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 5 F) (hJ : J.form = 1)
    {q : ℕ} (hcard : Nat.card F = q ^ 2) (hq : Even q) (hq2 : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q)
    (hrank : ∀ p : ℕ, p.Prime → primeRank p (UnitaryFive.lineParabolic J) ≤ 2) : q = 4 :=
  unitary_five_field_size_eq_four_of_parabolic_rank hq hq2
    (fun _p hp hd => UnitaryFive.primeRank_lineParabolic_ge_of_dvd_quotient
      J hJ hcard hq2 hconj hp hd) hrank

/-- The source uses only odd-prime ranks; the divisor of the odd number q+1 is odd. -/
theorem unitary_five_field_size_eq_four_of_odd_parabolic_ranks
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 5 F) (hJ : J.form = 1)
    {q : ℕ} (hcard : Nat.card F = q ^ 2) (hq : Even q) (hq2 : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q)
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p (UnitaryFive.lineParabolic J) ≤ 2) : q = 4 := by
  have hquot : (q + 1) / Nat.gcd (q + 1) 5 = 1 :=
    Nat.eq_one_iff_not_exists_prime_dvd.mpr (by
      intro p hp hd
      have hdq : p ∣ q + 1 := hd.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
      have ho : Odd p := by
        rcases hp.eq_two_or_odd with rfl | ho
        · obtain ⟨a, ha⟩ := hq
          obtain ⟨b, hb⟩ := hdq
          omega
        · exact Nat.odd_iff.mpr ho
      have hr := UnitaryFive.primeRank_lineParabolic_ge_of_dvd_quotient
        J hJ hcard hq2 hconj hp hd
      exact (Nat.not_succ_le_self 2) (hr.trans (hrank p hp ho)))
  apply unitary_five_field_size_eq_four hq hq2
  calc q + 1 = (q + 1) / Nat.gcd (q + 1) 5 * Nat.gcd (q + 1) 5 :=
        (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
       _ = Nat.gcd (q + 1) 5 := by rw [hquot, one_mul]

/-- In characteristic two the literal line parabolic is two-local, so QT supplies the bound. -/
theorem unitary_five_field_size_eq_four_of_quasithin_identity
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 5 F) (hJ : J.form = 1)
    {q : ℕ} (hcard : Nat.card F = q ^ 2) (hq : Even q) (hq2 : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q)
    (hqt : IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup J)) : q = 4 := by
  let : Finite (Matrix.GeneralLinearGroup (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective (UnitaryFive.project J) (UnitaryFive.project_surjective J)
  apply unitary_five_field_size_eq_four_of_odd_parabolic_ranks J hJ hcard hq hq2 hconj
  exact (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt) _
    (UnitaryFive.lineParabolic_isTwoLocal J hJ)

/-- Each odd prime divisor of q+1 has ordinary rank greater than two in every actual PSU₄ model. -/
theorem unitary_four_ordinary_rank_gt_two {G : Type*} [Group G] [Finite G]
    {q p : ℕ} (hq : IsPrimePow q) (hmodel : ClassicalGroup.IsPSU G 4 q)
    (hp : p.Prime) (ho : p ≠ 2) (hd : p ∣ q + 1) : 2 < primeRank p G := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  rw [Theory.GroupTheory.primeRank_equiv p e]
  exact ClassicalUnitary.EvenSmallRanks.four_rank J hq hcard hconj hp ho hd

/-- An even-parameter PSU₄ model has an odd prime whose ordinary rank exceeds two. -/
theorem unitary_four_exists_odd_rank_gt_two {G : Type*} [Group G] [Finite G]
    {q : ℕ} (hq : IsPrimePow q) (he : Even q) (hmodel : ClassicalGroup.IsPSU G 4 q) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 < primeRank p G := by
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show q + 1 ≠ 1 by have := hq.one_lt; omega)
  have hn : p ≠ 2 := by
    rintro rfl
    obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := hd
    omega
  exact ⟨p, hp, Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hn),
    unitary_four_ordinary_rank_gt_two hq hmodel hp hn hd⟩

/-- The exceptional surviving simple model has ordinary five-rank greater than two. -/
theorem unitary_five_four_ordinary_rank_gt_two {G : Type*} [Group G] [Finite G]
    (hmodel : ClassicalGroup.IsPSU G 5 4) : 2 < primeRank 5 G := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective e.symm e.symm.injective
  rw [Theory.GroupTheory.primeRank_equiv 5 e]
  exact ClassicalUnitary.EvenSmallRanks.five_rank J
    ((isPrimePow_nat_iff _).mpr ⟨2, 2, Nat.prime_two, by decide, rfl⟩)
    hcard hconj (by decide) (by decide)

/-- An actual SU₅(4) covering model fails QT, independently of a cover-classification tag. -/
theorem unitary_five_four_cover_not_quasithin
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (e : G ≃* J.specialSubgroup) :
    ¬ IsQuasithin G := by
  let : Finite (Matrix.GeneralLinearGroup (Fin 5) F) :=
    Finite.of_injective Units.val Units.val_injective
  intro hqt
  exact UnitaryFive.not_quasithin_special_four_of_form J hcard hconj
    (Theory.GroupTheory.isQuasithin_of_equiv e hqt)

/-- The cyclic-by-SU₃ subgroup in the nontrivial-center case q=4 lies in the actual SU line stabilizer. -/
theorem unitary_five_four_cover_parabolic_subgroup
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 5 F) (hJ : J.form = 1) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) :
    Nat.card (rootsOfUnity 5 F) = 5 ∧ IsCyclic (rootsOfUnity 5 F) ∧
      ∃ L : Subgroup J.specialSubgroup, L ≤ UnitaryFive.specialStabilizer J (UnitaryFive.line F) ∧
        Nonempty ((rootsOfUnity 5 F × (UnitaryFive.LineCore.Parabolic.middleForm J).specialSubgroup) ≃* L) := by
  refine ⟨UnitaryFive.card_fifthRoots hcard, UnitaryFive.fifthRoots_cyclic,
    (UnitaryFive.coverProduct J hJ hconj).range, ?_,
    ⟨MonoidHom.ofInjective (UnitaryFive.coverProduct_injective J hJ hconj)⟩⟩
  rintro x ⟨a, rfl⟩
  exact UnitaryFive.coverProduct_mem_line J hJ hconj a
end CFSG.Quasithin.ChapterA.Section02.EvenLie
