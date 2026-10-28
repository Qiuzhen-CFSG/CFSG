module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointRecognition
public import Theory.Representation.BinaryOffender.InvolutionFixedKernel
public import Theory.Representation.BinaryOffender.InnerNormalizerActors

/-!
# Local calculations required for the G₂ adjoint obstruction

The first contract separates the involution displacement calculation from
the equality case: the pointwise kernel on an eight-dimensional fixed space,
inside the involution centralizer, has order at most q. The second concerns
the actual binary linear normalizer. A noninner involution there moves at
least half the fourteen-dimensional module after restriction of scalars.

Neither contract asserts an offender inequality. Their construction is still
required; `AdjointObstruction.lean` proves their implication and applies it
to the literal normalizer, supplying the parent's adjoint premise.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 8.2,
pp.53–54, and Lemma 8.5, pp.55–56 of the author manuscript.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction
open Representation Representation.BinaryOffender Subgroup
attribute [local instance] ZMod.algebra

variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The inner involution calculation and its relatively normal pointwise kernel.
The kernel is in `C_G(t)`, not a normal subgroup of the whole G₂ group. -/
structure InnerCalculations (r : ℕ) : Prop where
  involution_codim : ∀ t : Atlas.G2.Model F, t ≠ 1 → t ^ 2 = 1 →
    6 * r ≤ fixedCodim (adjointBinary F) (zpowers t)
  fixed_kernel_card : ∀ t : Atlas.G2.Model F, t ≠ 1 → t ^ 2 = 1 →
    fixedCodim (adjointBinary F) (zpowers t) = 6 * r →
    Nat.card (involutionFixedKernel (adjointBinary F) t) ≤ 2 ^ r

/-- Normalizer facts needed in addition to the inner calculation. Faithfulness
and binary irreducibility concern the actual restricted derivation action. -/
structure NormalizerCalculations (r : ℕ) : Prop where
  faithful : Function.Injective (adjointBinary F)
  irreducible : IsIrreducible (adjointBinary F)
  involution_alternative : ∀ t : linearNormalizer (adjointBinary F), t ^ 2 = 1 →
    t ∈ (normalizerEmbedding (adjointBinary F)).range ∨
      7 * r ≤ fixedCodim (normalizerRepresentation (adjointBinary F)) (zpowers t)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction
