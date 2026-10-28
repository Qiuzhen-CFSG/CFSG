module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Inputs
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearFixer
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage

/-!
# Pointwise Borel rigidity for binary PSU₃

Write q = 2ⁿ, with n ≥ 2. Every automorphism of the standard projective
unitary group over the matrix field of order q² has an actual unitary-semilinear
formula. The intrinsic Borel-fixer theorem then shows that an involutory
automorphism fixing a Sylow normalizer pointwise is trivial.

The Frobenius conjugation x ↦ x^q supplies the fixed-field cardinality needed
by coverage. A Hermitian basis change and the equivalence stored in `IsPSU`
transport rigidity to the supplied group and Sylow subgroup. This discharges
the rigidity input used to identify C_V(L ∩ M) with C_V(L) in E.6.8(1).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1),
printed pp.247–248; GLS3, Theorem 2.5.12 and §2.7 for automorphism coverage.
-/

public section

open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction

/-- Semilinear coverage and the intrinsic fixer calculation give Borel rigidity
in the standard matrix model, retaining its full field automorphism parameter. -/
theorem standard_borelRigid
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) : BorelRigid S := by
  intro a ha hfix
  obtain ⟨σ, hσ⟩ := J.semilinear_coverage n hn hJ hcard
    (fixed_card J n (by omega) hcard hconj) a
  exact HermitianForm.BorelTorus.unitary_semilinear_fixer_eq_one
    J hJ hn hcard hconj S a σ hσ ha hfix

/-- The actual model equivalence and Hermitian basis change transport the
pointwise Borel-fixer theorem to any marked Sylow subgroup of PSU₃(2ⁿ). -/
theorem borelRigid_of_isPSU
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSU H 3 (2 ^ n)) (S : Sylow 2 H) : BorelRigid S := by
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e₀⟩⟩ := hmodel
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n (by omega) hcard hconj
  let e := e₀.trans (FormTransport.projectiveEquiv J C hC)
  apply BorelRigid.of_equiv S e
  exact standard_borelRigid (FormTransport.standardForm J) n hn hcard hconj rfl _

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction
