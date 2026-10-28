module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.Centralizers

/-!
# Geometric inputs for linear-actor escape

These two independent model calculations are consumed by
`LinearActors.escape_of_tori_and_nine`. The torus calculation supplies a
normalized odd commutator. The field-of-nine calculation supplies an
actual field-involution centralizer, its literal Sylow intersection and
nontrivial actor image in the two-core quotient. Neither assumes an
E-member or an E-generation conclusion.

The full semilinear centralizer is retained throughout. The construction
allows all odd-prime groups in the torus branch and uses the actual field
centralizer in the exceptional branch, without asserting an exhaustive
S₄/dihedral catalogue.

Source: Aschbacher–Smith E.1.2 and E.1.14(6), pp.209–210, 214;
Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
variable (F : Type*) [Field F] [Finite F] [Finite (PGammaL2 F)]

/-- The torus calculation, including the full semilinear Sylow centralizer.
The exception is precisely an inner actor over the field of nine. The odd
subgroup need only be a prime-power group, and no local-model exhaustion
is assumed. -/
@[expose] def OddTorusPlacement (p : ℕ) : Prop :=
  ∀ (T : Sylow 2 (PGammaL2 F)) (A : Subgroup (PGammaL2 F)),
    IsElementaryAbelian 2 A → Group.rank A = 2 → A ≤ pGammaL2PGLRange F →
    A ≤ (T : Subgroup _) → (5 ≤ p ∨ ¬ A ≤ pGammaL2PSLRange F) →
    ∀ M : Subgroup (PGammaL2 F), IsCoatom M → (T : Subgroup _) ≤ M →
      ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup (PGammaL2 F),
        IsPGroup r X ∧
        (T : Subgroup _) ⊓ centralizer (A : Set (PGammaL2 F)) ≤ normalizer (X : Set _) ∧
        ¬ ⁅X, A⁆ ≤ M

/-- Small-field placement is a statement about actual field involutions,
centralizers, the local two-core and the original Sylow. It contains no
E-membership assumption. -/
@[expose] def NineFieldPlacement : Prop :=
  ∀ (T : Sylow 2 (PGammaL2 F)) (A : Subgroup (PGammaL2 F)),
    IsElementaryAbelian 2 A → Group.rank A = 2 → A ≤ pGammaL2PSLRange F →
    A ≤ (T : Subgroup _) →
    ∃ x : PGammaL2 F, orderOf x = 2 ∧ x.right ≠ 1 ∧
      x ∈ centralizer (A : Set (PGammaL2 F)) ∧
      (∃ S : Sylow 2 (centralizer ({x} : Set (PGammaL2 F))),
        (S : Subgroup _) = (T : Subgroup _).subgroupOf (centralizer ({x} : Set _))) ∧
      (¬ A.subgroupOf (centralizer ({x} : Set (PGammaL2 F))) ≤
        pCore 2 (centralizer ({x} : Set (PGammaL2 F)))) ∧
      (T : Subgroup _) ⊔ centralizer ({x} : Set (PGammaL2 F)) = ⊤

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
