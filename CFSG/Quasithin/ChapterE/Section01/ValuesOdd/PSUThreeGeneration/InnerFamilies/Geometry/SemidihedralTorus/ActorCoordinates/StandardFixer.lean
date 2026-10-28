module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.Setup
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.StandardFixer.Semilinear
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.StandardFixer.Diagonalization
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.StandardFixer.TwoSubgroups

/-!
# The full standard-four fixer has diagonal semilinear coordinates

Transport odd-prime automorphism coverage from the antidiagonal form to the
original identity Gram basis, then use the odd scalar kernel to lift fixation
of projective signs to exact matrix commutation. This proves that every
automorphism in the full pointwise fixer has a diagonal unitary semilinear
formula, with field part identity or the stored Frobenius.

The final adapter retains one explicit premise: simultaneously conjugating
a two-subgroup of these diagonal semilinear automorphisms into sign formulas.
It uses the proved diagonal formula of the conjugator to preserve the four-group
pointwise. That arithmetic and Sylow calculation is still needed to establish
`StandardFixerCoordinates`; the conditional adapter is not the final source result.

Source: Aschbacher--Smith E.1.14(7), printed p.214, A.3.21(a)--(b), printed p.55,
and Aschbacher (1982), Lemma 4.11. The eventual consumer is the `hfix` argument
of `ActorCoordinates.exists_sign_coordinates_of_model_inputs`.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
variable {F : Type*} [Field F]

/-- Unconditional diagonal semilinear coverage for every automorphism fixing
the literal standard four-group. No two-group or innerness hypothesis is needed. -/
theorem hasDiagonalSemilinearForm_of_fixes_standardFour [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ x ∈ standardFour J, a x = x) : HasDiagonalSemilinearForm J a := by
  obtain ⟨σ, hσ, hsem⟩ := StandardFixer.identityGram_semilinear_coverage J hJ hp ho hcard hc a
  have h2 : (2 : F) ≠ 0 :=
    Field.two_ne_zero_of_odd_card F (by rw [hcard]; exact ho.pow)
  exact StandardFixer.diagonal_form_of_fixes_standardFour J hJ h2 a σ hσ hsem hfix

/-- The only remaining premise is simultaneous normalization inside the concrete
diagonal semilinear group. Coverage and exact diagonal placement are discharged here. -/
theorem standardFixerCoordinates_of_diagonal_normalization [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hnormalize : ∀ U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)),
      IsPGroup 2 U → (∀ a ∈ U, HasDiagonalSemilinearForm J a) →
      ∃ c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
        HasDiagonalSemilinearForm J c ∧
        ∀ a ∈ U, HasSignSemilinearForm J (MulAut.congr c a)) :
    StandardFixerCoordinates J := by
  intro U hU hfix
  have hdiag : ∀ a ∈ U, HasDiagonalSemilinearForm J a := by
    intro a ha
    exact hasDiagonalSemilinearForm_of_fixes_standardFour J hJ hp ho hcard hc a (hfix a ha)
  obtain ⟨c, hcd, hcoords⟩ := hnormalize U hU hdiag
  exact ⟨c, hcd.fixes_standardFour, hcoords⟩

/-- Every two-subgroup in the pointwise fixer of the standard four-group admits
simultaneous sign and Frobenius coordinates. -/
theorem standardFixerCoordinates [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p) :
    StandardFixerCoordinates J := by
  apply standardFixerCoordinates_of_diagonal_normalization J hJ hp ho hcard hc
  intro U hU hdiag
  exact StandardFixer.exists_sign_conjugator_of_diagonal J hJ hp ho hmod hcard hc U hU hdiag

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
