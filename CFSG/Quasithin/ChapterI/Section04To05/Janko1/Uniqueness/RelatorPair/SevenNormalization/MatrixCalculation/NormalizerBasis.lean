module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.Definitions
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.Coordinates
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis.CharacterMarking
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis.Eigenbasis
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis.MatrixTransport

/-!
# Normalizer matrices in the supplied faithful representation

The prime-field decomposition, multiplicity-one argument, normalization of
the cubic fixed vector, and change of basis give the three literal matrix
images. Either orientation of the seven-generator is retained.

The finite character marking is constructed from the actual source normalizer
frame, so the final theorem requires only the supplied Bruhat frame and faithful
representation. Simplicity, ambient order, and involution fusion are not needed
for this step. Its matrix conclusion is consumed by
`exists_source_pair_of_normalizer_images` in the parent matrix calculation,
which this producer deliberately does not import. The intermediate theorem
with an explicit character marking remains available.

Source: Gorenstein, *Finite Groups*, §16.6, pp.482–483, equations (6.1)–(6.2),
describing Janko, J. Algebra 3 (1966), 147–186,
DOI 10.1016/0021-8693(66)90010-X.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

/-- Construct the actual change of basis from a marking of the seven Sylow
characters. No multiplicity, irreducibility, or representation basis is assumed. -/
public theorem exists_normalizer_images_of_characterFrame
    {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}
    (D : NormalizerFrame h) (C : NormalizerCharacterFrame D)
    (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ) :
    ∃ c : Janko1.Ambient,
      (c * ρ D.x * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = normalX ∧
      (c * ρ D.u * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = normalU ∧
      ((c * ρ D.y * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY ∨
        (c * ρ D.y⁻¹ * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY) := by
  obtain ⟨b, hx, hu, hy⟩ := characterFrame_basis D C ρ hρ
  obtain ⟨c, hx, hu, hy⟩ := exists_normalizer_images_of_basis ρ D.x D.u
    (orientedY D C.reverse) b hx hu hy
  refine ⟨c, hx, hu, ?_⟩
  cases hr : C.reverse
  · left
    simpa only [orientedY, hr, Bool.false_eq_true, ↓reduceIte] using hy
  · right
    simpa only [orientedY, hr, ↓reduceIte] using hy

/-- Normalize the marked Sylow normalizer in the supplied faithful representation.
The character marking, its multiplicities over F₁₁, and the change of basis are
all constructed. Either orientation of the source seven-generator is allowed. -/
public theorem exists_normalizer_images
    {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}
    (D : BruhatFrame h) (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ) :
    ∃ c : Janko1.Ambient,
      (c * ρ D.x * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = normalX ∧
      (c * ρ D.u * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = normalU ∧
      ((c * ρ D.y * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY ∨
        (c * ρ D.y⁻¹ * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY) := by
  obtain ⟨C⟩ := exists_normalizerCharacterFrame_of_bruhat D
  exact exists_normalizer_images_of_characterFrame D.toNormalizerFrame C ρ hρ

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation
