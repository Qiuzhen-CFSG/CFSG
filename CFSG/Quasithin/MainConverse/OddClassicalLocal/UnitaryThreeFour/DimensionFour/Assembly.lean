module

public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.DimensionFour
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.ElementaryThreeRank.Assembly
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.ElementaryTwoCore.Conclusion

/-!
# PSU₄(3): the two local conditions

The elementary-normalizer rank calculation proves quasithinness of the concrete
projective SU₄ image over `FiniteField.Nine`. The independent intrinsic two-core
calculation proves even characteristic. Both results are unconditional and cover
the required two-locals through the elementary-normalizer reductions.

An actual equivalence of projective matrix groups transports these results to
every nondegenerate Hermitian form over a field of order nine with cube
conjugation. This retains the full scalar kernel of SU₄ → PSU₄ and the cores
inside the local subgroups. In particular it applies to identity Gram matrices;
no simplicity, noncommutativity or extra local hypotheses are needed.

This leaf assembles the completed calculations without changing the conditional
interfaces they import from `DimensionFour`.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 of
`refs/quasithin.pdf`, repeated as Theorem 0.1.1(4), printed p.482.
The QT and E definitions are on printed pp.3–4 and 481–482.
-/

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

namespace CFSG.Quasithin.MainConverse.UnitaryFourThree

/-- Every allowed field-nine Hermitian model in dimension four is quasithin
and has even characteristic. The equivalence is between the actual images in PGL. -/
public theorem quasithin_and_evenCharacteristic
    {F : Type} [Field F] [Finite F] (J : HermitianForm 4 F)
    (hcard : Nat.card F = 3 ^ 2) (hconj : ∀ x, J.conj x = x ^ 3) :
    IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup J) ∧
      IsEvenCharacteristic (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨e⟩ := exists_model_equiv J (by simpa using hcard) hconj
  exact ⟨Theory.GroupTheory.isQuasithin_of_equiv e.symm model_quasithin,
    IsEvenCharacteristic.of_equiv e.symm model_evenCharacteristic⟩

/-- The explicit source clauses: every two-local has odd-prime ranks at most
two, and every Sylow-containing maximal two-local has a self-centralizing
intrinsic two-core. All model calculation premises have been discharged. -/
public theorem local_conditions
    {F : Type} [Field F] [Finite F] (J : HermitianForm 4 F)
    (hcard : Nat.card F = 3 ^ 2) (hconj : ∀ x, J.conj x = x ^ 3) :
    (∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsTwoLocal M →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p M ≤ 2) ∧
    (∀ T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      ∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsMaximalTwoLocal M →
        (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ M →
          Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M) := by
  obtain ⟨hqt, hE⟩ := quasithin_and_evenCharacteristic J hcard hconj
  exact ⟨Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt, hE⟩

end CFSG.Quasithin.MainConverse.UnitaryFourThree
