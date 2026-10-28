module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.Automorphisms
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.OddModels.Reduction
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeSquares
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeSquares
public import Theory.SpecificGroups.SU3.CyclicNormalOuter.PrimeSquares
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Cubic automorphisms of the odd models in Theorem C

For PSL₂(pᵉ), e ≤ 2, PSL₃(p), and PSU₃(p), the actual automorphism
formulas put every outer square in a cyclic diagonal image. Hence a cubic
automorphism subgroup has outer image of order at most three. Three-rank
one bounds its inner kernel by three, making the subgroup abelian.

The field and graph calculations work for every displayed parameter, so
no further rank-dependent parameter exclusions are necessary. Finiteness
and simplicity are transported from the input group, and the unitary
matrix field and its fixed field retain orders p² and p respectively.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, Theorem C
on printed p.33 (PDF p.44) and its automorphism inspection on printed
p.1137 (PDF p.1154); GLS3, Theorem 2.5.12 and §2.7.
-/

public section
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.ChapterA.Section02
open Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne

/-- Every exponent-three subgroup of the actual automorphism group of an
odd-characteristic Theorem C model of three-rank one is abelian. -/
theorem cubic_of_odd_model {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ¬ IsMulCommutative S) (hr : primeRank 3 S = 1)
    (hmodel : IsTheoremCOddModel S) : CubicAutomorphismsAbelian S := by
  cases hmodel with
  | linear_two p n hp ho hn iso =>
    obtain ⟨F, hfield, hfinite, hcard, ⟨e⟩⟩ := iso
    apply cubic_of_mulEquiv e
    have hrF : primeRank 3 PSL(2,F) = 1 := (primeRank_equiv 3 e).symm.trans hr
    exact cubic_of_outer_squares hrF.le
      (Theory.PSL2.OuterSolvable.SmallDegreeSquares.diagonalOuter (F := F)).range
      Theory.PSL2.OuterSolvable.SmallDegreeSquares.diagonalOuter_range_isCyclic
      (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_square_mem hp ho hn hcard)
  | linear_three p hp ho iso =>
    obtain ⟨F, hfield, hfinite, hcard, ⟨e⟩⟩ := iso
    let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
    have hns : ¬ Group.IsSolvable PSL(3,F) := by
      intro hs
      let : IsMulCommutative PSL(3,F) :=
        IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr hs)
      exact hna (IsMulCommutative.of_comm fun x y => e.injective (by simp only [map_mul, mul_comm]))
    apply cubic_of_mulEquiv e
    have hrF : primeRank 3 PSL(3,F) = 1 := (primeRank_equiv 3 e).symm.trans hr
    exact cubic_of_outer_squares hrF.le (Matrix.PSL3.OuterSolvable.innerDiagonalOuter F)
      (Matrix.PSL3.OuterSolvable.innerDiagonalOuter_isCyclic F)
      (Matrix.PSL3.OuterSolvable.OddPrimeSquares.outer_square_mem hns hp ho hcard)
  | unitary_three p hp ho iso =>
    obtain ⟨F, hfield, hfinite, J, hcard, hconj, ⟨e⟩⟩ := iso
    let : Fact p.Prime := ⟨hp⟩
    have hfixed : Nat.card {x : F // J.conj x = x} = p := by
      simpa only [pow_one] using
        FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
          (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
    obtain ⟨f⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
      J p hcard hfixed
    let K := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    let a := e.trans f
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup K) :=
      Finite.of_injective a.symm a.symm.injective
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup K) :=
      a.symm.isSimpleGroup
    apply cubic_of_mulEquiv a
    have hrK : primeRank 3 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup K) = 1 :=
      (primeRank_equiv 3 a).symm.trans hr
    exact cubic_of_outer_squares hrK.le K.unitaryOuterHom.range
      K.unitaryOuterHom_range_isCyclic
      (K.outer_square_mem_unitary_of_odd_prime rfl hp ho hcard hfixed)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
