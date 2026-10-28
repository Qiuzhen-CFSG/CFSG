module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondefiningRank

/-!
# PSU₄(3): the remaining defining-prime and two-core calculations

The nondefining odd-prime bounds hold for every subgroup, by divisibility
of the actual projective image order into |GL₄(9)|. Thus quasithinness only
requires the three-rank bound for normalizers of nonidentity two-subgroups.
For even characteristic it suffices to calculate the intrinsic two-cores
of maximal two-locals containing one Sylow two-subgroup; Sylow conjugacy
then supplies the source condition for every Sylow two-subgroup. The
elementary-normalizer reduction restricts the first calculation to elementary
abelian subgroups in one Sylow subgroup, and the second to those normal in
one Sylow subgroup whose ambient normalizers are maximal two-local. The
two chosen Sylow subgroups may differ, so the calculations are independent.

The assembly lemmas transport these two calculations from the concrete model
over `FiniteField.Nine` to every field-nine Hermitian model. It uses the
proved equivalence of the actual images in PGL, retaining the scalar kernel.
Its two local calculation premises remain explicit: this is a conditional
assembly, not yet the PSU₄(3) source converse.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4, and its repetition
as Theorem 0.1.1(4), printed p.482, with definitions on pp.3–4 and 481–482.
-/

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

namespace CFSG.Quasithin.MainConverse.UnitaryFourThree

/-- Only the defining prime remains after the general linear order bound.
The input ranges over all actual nonidentity two-subgroups. -/
public theorem model_quasithin_of_three_normalizer_rank
    (hthree : ∀ Q : Subgroup (Carrier 4), Q ≠ ⊥ → IsPGroup 2 Q →
      primeRank 3 (Subgroup.normalizer (Q : Set (Carrier 4))) ≤ 2) :
    IsQuasithin (Carrier 4) := by
  apply Theory.GroupTheory.isQuasithin_iff_twoLocal.mpr
  intro M hM p hp ho
  by_cases h3 : p = 3
  · subst p
    obtain ⟨Q, hQ, hQtwo, rfl⟩ := hM
    exact hthree Q hQ hQtwo
  · exact subgroup_odd_primeRank_le_two_of_ne_three (form 4)
      FiniteField.Nine.natCard M hp ho h3

/-- Conditional assembly of the two source clauses from concrete local
calculations. The core is taken inside each local subgroup, and only
Sylow-containing maximal two-locals are tested. Both premises still need
proof before this yields the source converse. -/
public theorem local_conditions_of_model_calculations
    (hthree : ∀ Q : Subgroup (Carrier 4), Q ≠ ⊥ → IsPGroup 2 Q →
      primeRank 3 (Subgroup.normalizer (Q : Set (Carrier 4))) ≤ 2)
    (hcore : ∃ T : Sylow 2 (Carrier 4),
      ∀ M : Subgroup (Carrier 4), IsMaximalTwoLocal M → (T : Subgroup (Carrier 4)) ≤ M →
        Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    {F : Type} [Field F] [Finite F] (J : HermitianForm 4 F)
    (hcard : Nat.card F = 3 ^ 2) (hconj : ∀ x, J.conj x = x ^ 3) :
    (∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsTwoLocal M →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p M ≤ 2) ∧
    (∀ T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      ∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsMaximalTwoLocal M →
        (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ M →
          Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M) := by
  obtain ⟨e⟩ := exists_model_equiv J (by simpa using hcard) hconj
  have hqt : IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Theory.GroupTheory.isQuasithin_of_equiv e.symm
      (model_quasithin_of_three_normalizer_rank hthree)
  refine ⟨Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt, ?_⟩
  obtain ⟨T, hT⟩ := hcore
  have hE : IsEvenCharacteristicAt T := hT
  exact (IsEvenCharacteristicAt.all hE).of_equiv e.symm

/-- Only elementary abelian normalizers inside one fixed Sylow subgroup
need the defining-prime calculation. Conjugacy covers all maximal locals. -/
public theorem model_quasithin_of_elementary_normalizer_rank
    (S : Sylow 2 (Carrier 4))
    (hthree : ∀ A : Subgroup (Carrier 4), A ≤ (S : Subgroup (Carrier 4)) →
      A ≠ ⊥ → IsElementaryAbelian 2 A →
        primeRank 3 (Subgroup.normalizer (A : Set (Carrier 4))) ≤ 2) :
    IsQuasithin (Carrier 4) := by
  apply Theory.GroupTheory.isQuasithin_iff_maximalTwoLocal.mpr
  intro M hM p hp ho
  by_cases h3 : p = 3
  · subst p
    obtain ⟨A, hAS, hA, hEA, g, rfl⟩ :=
      Theory.GroupTheory.exists_elementary_normalizer_in_sylow S hM
    rw [← Theory.GroupTheory.primeRank_equiv 3
      (Subgroup.equivMapOfInjective (Subgroup.normalizer (A : Set (Carrier 4)))
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)]
    exact hthree A hAS hA hEA
  · exact subgroup_odd_primeRank_le_two_of_ne_three (form 4)
      FiniteField.Nine.natCard M hp ho h3

/-- For condition E, elementary normalizer witnesses can be taken normal
in the chosen Sylow subgroup. The maximality condition is retained. -/
public theorem model_evenCharacteristicAt_of_normal_elementary_cores
    (T : Sylow 2 (Carrier 4))
    (hcore : ∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
      let N := Subgroup.normalizer (R.map (T : Subgroup (Carrier 4)).subtype :
        Set (Carrier 4))
      IsMaximalTwoLocal N → Subgroup.centralizer (pCore 2 N : Set N) ≤ pCore 2 N) :
    IsEvenCharacteristicAt T := by
  intro M hM hTM
  obtain ⟨R, hR, hn, he, hMN⟩ :=
    Theory.GroupTheory.exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  subst M
  exact hcore R hR hn he hM

/-- Conditional assembly from two independent elementary-normalizer
calculations. The Sylow witnesses need not coincide; both calculation
premises must still be proved to obtain the source converse. -/
public theorem local_conditions_of_elementary_calculations
    (hthree : ∃ S : Sylow 2 (Carrier 4),
      ∀ A : Subgroup (Carrier 4), A ≤ (S : Subgroup (Carrier 4)) →
        A ≠ ⊥ → IsElementaryAbelian 2 A →
          primeRank 3 (Subgroup.normalizer (A : Set (Carrier 4))) ≤ 2)
    (hcore : ∃ T : Sylow 2 (Carrier 4),
      ∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
        let N := Subgroup.normalizer (R.map (T : Subgroup (Carrier 4)).subtype :
          Set (Carrier 4))
        IsMaximalTwoLocal N → Subgroup.centralizer (pCore 2 N : Set N) ≤ pCore 2 N)
    {F : Type} [Field F] [Finite F] (J : HermitianForm 4 F)
    (hcard : Nat.card F = 3 ^ 2) (hconj : ∀ x, J.conj x = x ^ 3) :
    (∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsTwoLocal M →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p M ≤ 2) ∧
    (∀ T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      ∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsMaximalTwoLocal M →
        (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ M →
          Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M) := by
  obtain ⟨S, hS⟩ := hthree
  obtain ⟨T, hT⟩ := hcore
  apply local_conditions_of_model_calculations ?_
    ⟨T, model_evenCharacteristicAt_of_normal_elementary_cores T hT⟩ J hcard hconj
  intro Q hQ hQtwo
  exact Theory.GroupTheory.isQuasithin_iff_twoLocal.mp
    (model_quasithin_of_elementary_normalizer_rank S hS)
    _ ⟨Q, hQ, hQtwo, rfl⟩ 3 (by decide) (by decide)

end CFSG.Quasithin.MainConverse.UnitaryFourThree
