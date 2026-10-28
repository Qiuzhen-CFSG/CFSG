module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.UnitaryThreeFixed.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.UnitaryThreeFixed.InnerRank
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.UnitaryThreeFixed.OrthogonalRank
public import Theory.SpecificGroups.SU3.OddInvolutionFixed
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Odd-prime unitary involution inspection

The full fixed group of an outer involution is identified with the ternary
special orthogonal group over the actual fixed field, whose three-rank is at
most one. For inner involutions, the first commutator of the covering
centralizer embeds in SL₂(p), and the bound passes through the scalar quotient.
Transport along the actual model equivalence gives
`InvolutionDerivedThreeRank` for every odd-prime PSU₃ branch of Theorem C,
including p = 3 and arbitrary nondegenerate Hermitian Gram matrices.

Source: Aschbacher–Smith E.6.18, printed p.252, and Theorem C, printed p.33.
-/

public section
open Theory.GroupTheory BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie
open UnitaryThreeFixed

/-- Assembly from the two independent rank calculations. Outer normalization,
fixed-group identification and model transport are discharged in this theorem. -/
theorem involutionDerivedThreeRank_unitary_of_inner_and_orthogonal
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hS : ClassicalGroup.IsPSU S 3 p)
    (hinner : InnerDerivedThreeRank p) (horth : OrthogonalThreeRank p) :
    InvolutionDerivedThreeRank S := by
  obtain ⟨E, hfield, hfinite, J, hcard, hconj, ⟨e⟩⟩ := hS
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv S e.toEquiv
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa using hcard) (by simpa using hconj)
  apply InvolutionDerivedThreeRank.of_equiv (e := e)
  intro a ha
  by_cases hi : ∃ k, a = MulAut.conj k
  · obtain ⟨k, rfl⟩ := hi
    exact hinner E J inferInstance hcard hconj k ha
  · obtain ⟨f⟩ := OddInvolutionNormalization.fixed_equiv_orthogonal J hp ho hcard hfixed a
      (by simpa only [ha] using pow_orderOf_eq_one a) hi
    have hr : primeRank 3 a.fixedSubgroup ≤ 1 := by
      rw [primeRank_congr 3 f]
      exact horth (FixedBy.subfield E J.conj) hfixed
    exact (primeRank_subgroup_le 3 (commutator a.fixedSubgroup)).trans hr

/-- Every involutory automorphism of an odd-prime PSU₃ model has derived
fixed-group three-rank at most one, including in characteristic three. -/
theorem involutionDerivedThreeRank_unitary
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hS : ClassicalGroup.IsPSU S 3 p) :
    InvolutionDerivedThreeRank S :=
  involutionDerivedThreeRank_unitary_of_inner_and_orthogonal hp ho hS
    (innerDerivedThreeRank_unitary hp ho) (orthogonalThreeRank hp ho)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie
