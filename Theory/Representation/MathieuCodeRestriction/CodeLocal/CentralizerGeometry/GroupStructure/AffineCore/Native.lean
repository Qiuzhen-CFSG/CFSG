module

public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.GroupStructure.AffineCore
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.GroupStructure

/-!
# Native applications of the affine translation-centralizer calculation

The concrete affine order and two-core product transfer through the published
embedding into native M24. For every nonidentity pointwise octad-kernel element,
the actual native carrier has order sixteen and supplements the octad kernel
in its full centralizer's intrinsic two-core. Both applications discharge the
corresponding model premise of the existing carrier transport theorems.

Source: Aschbacher--Smith H.16.2(6), printed pp.402--403, citing Asc94, 39.1.
The supplement record and its Sylow-center application remain with the parent
assembly; identification with the source code-space centralizer is separate.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise

namespace MathieuCode.OctadAffine

/-- The actual native carrier has order sixteen for a nonidentity octad translation. -/
theorem carrier_card_of_ne_one (O : Octad) (a : octadPointwiseKernel O) (ha : a.val ≠ 1) :
    Nat.card (carrier O a) = 16 :=
  carrier_card O a (fiberKernel_card (vector O a) (vector_ne_zero O a ha))

/-- The actual native carrier gives the literal two-core product without a model premise. -/
theorem carrier_product_of_ne_one (O : Octad) (a : octadPointwiseKernel O) (ha : a.val ≠ 1) :
    (octadPointwiseKernel O : Set M24) * (carrier O a : Set M24) =
      ((pCore 2 (Subgroup.centralizer ({a.val} : Set M24))).map
        (Subgroup.centralizer ({a.val} : Set M24)).subtype : Set M24) :=
  carrier_product O a ha
    (translations_mul_fiberKernel_eq_core (vector O a) (vector_ne_zero O a ha))

end MathieuCode.OctadAffine
