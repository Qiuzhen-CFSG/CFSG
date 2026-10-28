module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.OuterRank
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.UnitaryThree.FieldQuotient
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport

/-!
# Outer three-rank of rank-one binary PSU₃

For a group isomorphic to PSU₃(2^f) with three-rank one, the diagonal/cycle
construction excludes odd f: it gives an actual elementary subgroup of
order nine in the projective group. Hence 2^f is one modulo three and the
diagonal outer contribution is trivial. Explicit semilinear coverage then
makes the whole outer group cyclic, proving the required three-rank bound.

The model predicate permits any nondegenerate Hermitian form over the field
of order (2^f)^2. Quadratic Frobenius gives its fixed-field cardinality 2^f;
an actual projective group equivalence transports it to the antidiagonal
form used by coverage. No order or simplicity certification is needed.

This is a conditional helper for the automorphism inspection in the proof
of Aschbacher--Smith 15.3.38, printed p.1137, with the Bender models listed
in A.2.3--4, printed p.33. The automorphism description is GLS3,
Theorem 2.5.12 and Section 2.7. The parent retains the coverage obligation
and the unconditional Bender assembly.
-/

public section
open BenderSuzuki.MatrixGroups BenderSuzuki.MatrixGroups.HermitianForm
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne.UnitaryThree

/-- The exact universal coverage input for the antidiagonal binary models.
The parent source-theorem assembly owns its discharge. -/
@[expose] def SemilinearCoverage : Prop :=
  ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E) (n : ℕ),
    2 ≤ n → J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
    Nat.card E = (2 ^ n) ^ 2 → Nat.card {z : E // J.conj z = z} = 2 ^ n →
    ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ

open OddPrimeSylow.NormalizedOuter.FormTransport
variable {S : Type*} [Group S] [Finite S]

/-- Rank one excludes odd degree via an actual elementary subgroup of order
nine. For even degree the diagonal quotient vanishes, and coverage gives a
cyclic outer group. This transports arbitrary Hermitian forms to the standard
form without changing the field involution. -/
theorem outer_cyclic_of_coverage (hcoverage : SemilinearCoverage)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU S 3 (2 ^ f))
    (hr : primeRank 3 S = 1) : IsCyclic (MulAut.Outer S) := by
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective e e.surjective
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 f (by omega) hcard hconj
  have heven : Even f := by
    rcases Nat.even_or_odd f with he | ho
    · exact he
    · have htwo := Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective
        J (by omega : 0 < f) hcard hconj ho
      rw [← primeRank_equiv 3 e, hr] at htwo
      omega
  have hmod : 2 ^ f % 3 = 1 := by
    rw [Nat.BinaryTorusParity.two_pow_mod_three, Nat.even_iff.mp heven, if_pos rfl]
  obtain ⟨b⟩ := exists_projectiveEquiv J (2 ^ f) hcard hfixed
  have hc : IsCyclic (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup (standardForm J))) :=
    outer_cyclic (standardForm J) rfl
      (unitary_inner (standardForm J) (2 ^ f) hmod hconj)
      (hcoverage E (standardForm J) f hf rfl hcard hfixed)
  exact (MulAut.outerCongr (e.trans b)).isCyclic.mpr hc

/-- The requested outer three-rank bound for binary PSU₃, conditional only
on the universal semilinear coverage input. -/
theorem outer_three_rank_le_one_of_coverage (hcoverage : SemilinearCoverage)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU S 3 (2 ^ f))
    (hr : primeRank 3 S = 1) : primeRank 3 (MulAut.Outer S) ≤ 1 := by
  let := outer_cyclic_of_coverage hcoverage hf hmodel hr
  let P : Sylow 3 (MulAut.Outer S) := Classical.choice inferInstance
  exact P.primeRank_le_one_of_isCyclic inferInstance

/-- The rank-one automorphism property consumed by the Bender assembly. -/
theorem cubic_of_coverage (hcoverage : SemilinearCoverage)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU S 3 (2 ^ f))
    (hr : primeRank 3 S = 1) : CubicAutomorphismsAbelian S :=
  cubic_of_outer_three_rank_le_one hr.le
    (outer_three_rank_le_one_of_coverage hcoverage hf hmodel hr)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne.UnitaryThree
