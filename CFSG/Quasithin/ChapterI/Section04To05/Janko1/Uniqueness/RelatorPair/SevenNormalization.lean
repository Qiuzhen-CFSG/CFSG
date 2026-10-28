module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.Normalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SourceMatrices
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.ElementOrders
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.BruhatConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation

/-!
# Normalizing Janko's supplied seven-dimensional representation

The local construction gives the actual `7:3` complement, its cubic fixed
involution x, and an involution w centralizing the cubic generator and
inverting the seven-generator, with `(xw)^5 = 1`. All these data follow
from the original finite simple group hypotheses and the supplied order.

For an explicitly supplied faithful representation over F₁₁, the character
decomposition of the elementary abelian Sylow subgroup constructs a basis
normalizing x, the cubic generator, and either orientation of the
seven-generator. The relations for w then force the image of xw to be
`sourceV`. The theorem below assembles these arguments, giving one change
of basis for both literal matrices in (6.1), with no configuration or
representation-normalization premise left over.

The conclusion supplies exactly the matrix hypotheses of
`exists_atlas_pair_of_conjugated_source_matrix_images` in `RelatorPair`.
Existence of the faithful representation remains a separate obligation
of that source-theorem assembly; no generation assertion is needed here.

Source: Gorenstein, *Finite Groups*, §16.6, (6.1)–(6.2), pp.482–483;
Z. Janko, J. Algebra 3 (1966), 147–186. The source-access limitation is
recorded in `RelatorPair/Source/README.md`.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization

/-- A supplied faithful seven-dimensional representation admits simultaneous
normalization to Janko's two literal matrices. The local configuration and
all representation-normalization premises are proved from the source inputs. -/
public theorem exists_conjugated_source_matrix_images_of_source
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (horder : Nat.card G = 175560)
    (hfusion : ∀ x : G, orderOf x = 2 → ∃ g : G, g * x * g⁻¹ = h.z)
    (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ) :
    ∃ c : Janko1.Ambient, ∃ y v : G,
      (c * ρ y * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY ∧
      (c * ρ v * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceV := by
  obtain ⟨D⟩ := exists_bruhatFrame_of_source h horder hfusion
  exact MatrixCalculation.exists_conjugated_source_matrix_images D ρ hρ

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
