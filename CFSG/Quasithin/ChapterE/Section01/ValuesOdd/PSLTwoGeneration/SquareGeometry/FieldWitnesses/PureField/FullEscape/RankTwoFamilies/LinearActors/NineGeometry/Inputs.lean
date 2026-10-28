module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.Geometry

/-!
# Two independent normalizer calculations over the field of nine

An inner four-group has an S₄ normalizer in PGL₂. The exceptional
semilinear placement needs two further facts about its full normalizer:
it is the centralizer of a genuine field involution, and its intersection
with a prescribed Sylow has order sixteen and generates with that Sylow.

These are explicit geometric obligations, not asserted model theorems.
`NineGeometry` combines them with the checked paired-S₄ construction.
In particular neither obligation contains an E-member, an actor image in
a quotient, or the desired `NineFieldPlacement` conclusion.

Source: Aschbacher–Smith E.1.2 and E.1.14(6), printed pp.209–210, 214,
citing Aschbacher (1982), Lemma 4.10.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry

variable (F : Type*) [Field F]

/-- Identify the actual full normalizer of each inner four-group with
the centralizer of a field involution. No ambient Sylow is prescribed. -/
@[expose] def FourNormalizerField : Prop :=
  ∀ B : Subgroup (PGL2 F), IsKleinFour B →
    B ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range →
    ∃ x : PGammaL2 F, orderOf x = 2 ∧ x.right ≠ 1 ∧
      centralizer ({x} : Set (PGammaL2 F)) =
        normalizer (B.map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) : Set _)

/-- The full normalizer's position relative to an arbitrary ambient
Sylow. This statement does not mention or assume a field involution. -/
@[expose] def FourNormalizerSylowGeometry : Prop :=
  ∀ (T : Sylow 2 (PGammaL2 F)) (B : Subgroup (PGL2 F)), IsKleinFour B →
    B ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range →
    B.map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) ≤
      (T : Subgroup (PGammaL2 F)) →
    let N := normalizer
      (B.map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) : Set (PGammaL2 F))
    Nat.card ((T : Subgroup (PGammaL2 F)).subgroupOf N) = 16 ∧
      (T : Subgroup (PGammaL2 F)) ⊔ N = ⊤

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry
