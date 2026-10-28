module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.NormalizerCalculation.CosetControl.Action

/-!
# Matrix obligations for the Ree unitary normalizer

The centralizer problem asks that the kernel of the ambient socle action
lie in the supplied PGU image. The independent semilinear problem asks for
actual projective matrix formulas with field part identity or the Hermitian
involution, together with the compatible Gram equation. Both problems
retain the original local hypotheses and the arbitrary supplied extension.
Neither is asserted here to have a solution.

The formulas use the PSU marking induced by the extension itself, rather
than the potentially different marking in the original socle equivalence.
Thus their assembly needs no unproved comparison with a standard embedding.

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; the PGU₃(q):2 entry is case 7 of the
unconditional list in the proof of Theorem 5 of arXiv:0910.4758, p.3.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup Matrix BenderSuzuki.MatrixGroups

/-- The exact centralizer containment needed to lift the projective action.
The given relative equality `C_M(S) = 1` is not this assertion. -/
@[expose] def UnitaryNormalizerCentralizerControl : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
        Nat.card F = (2 ^ (2 * m + 1)) ^ 2 →
        (∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) →
        (S ≃* ProjectiveSpecialUnitaryMatrixGroup J) →
        ∀ E : ProjectiveExtension (S.map M.subtype) J,
          centralizer (S.map M.subtype : Set (Model m)) ≤ E.embedding.range

/-- The Ree normalizer induces only linear or Hermitian-semilinear isometries.
The formula is on the supplied projective image, marked by the supplied
extension. The compatible Gram equation permits arbitrary Hermitian forms. -/
@[expose] def UnitaryNormalizerSemilinearActions : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
        Nat.card F = (2 ^ (2 * m + 1)) ^ 2 →
        (∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) →
        (S ≃* ProjectiveSpecialUnitaryMatrixGroup J) →
        ∀ E : ProjectiveExtension (S.map M.subtype) J,
          ∀ k : normalizer (S.map M.subtype : Set (Model m)),
            E.HasCompatibleSemilinearAction k (RingEquiv.refl F) ∨
              E.HasCompatibleSemilinearAction k J.conj

end ReeF4.MaximalSubgroups.SimpleNormal
