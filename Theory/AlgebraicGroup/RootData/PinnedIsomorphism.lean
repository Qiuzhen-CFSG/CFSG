module

public import Theory.AlgebraicGroup.RootData.Chevalley
public import Theory.AlgebraicGroup.Quotient
public import Theory.AlgebraicGroup.Isomorphism
public import Theory.AlgebraicGroup.Morphism.QuotientComparison

universe u

/-!
Geometric descent endpoint for a pinned root-datum comparison.

The common cover, its two quotient morphisms, and reciprocal coordinate
factorisations are explicit fields.  This is intentional: `ChevalleyData` and
an abstract generators-and-relations presentation determine a point-group map,
but do not by themselves prove that the map is regular.  The theorem below
invokes the lower quotient-comparison interface to construct regular forward
and inverse maps through the common kernel, then transports the chosen root
elements.  The remaining Chevalley construction task is to supply this
geometric package from root-system and weight-lattice data.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A geometric common-cover package for a pinned Chevalley comparison.

The field `kernel_eq` and the reciprocal coordinate-factorisation hypotheses
are the descent data needed to turn the point-group comparison into regular
morphisms.  They identify each target coordinate with a function pulled back
from the other quotient, rather than incorrectly requiring pullback onto the
full coordinate ring of the common cover.  `coverK` and `coverL` record the
common-cover lifts of the chosen generators, so the resulting comparison is
pinned with the same parameter.
-/
public structure PinnedChevalleyQuotientData
    {U K L : Variety k} [AlgebraicGroup U] [AlgebraicGroup K]
    [AlgebraicGroup L]
    {TK : ClosedSubgroup K} {TL : ClosedSubgroup L}
    {DK : RootGroupData K TK} {DL : RootGroupData L TL}
    (CK : ChevalleyData K DK) (CL : ChevalleyData L DL)
    (ρ : DK.Root ≃ DL.Root) where
  πK : AlgebraicGroup.Morphism U K
  πL : AlgebraicGroup.Morphism U L
  πK_surjective : Function.Surjective πK.onPoints
  πL_surjective : Function.Surjective πL.onPoints
  kernel_eq : πK.kernel = πL.kernel
  πK_coordinate_factorization :
    ∀ a : Variety.PolynomialFunction L,
      ∃ q : Variety.PolynomialFunction K,
        πK.toVariety.pullbackAlgHom q = πL.toVariety.pullbackAlgHom a
  πL_coordinate_factorization :
    ∀ a : Variety.PolynomialFunction K,
      ∃ q : Variety.PolynomialFunction L,
        πL.toVariety.pullbackAlgHom q = πK.toVariety.pullbackAlgHom a
  coverX : DK.Root → k → Variety.Point U
  coverK : ∀ α t, πK.onPoints (coverX α t) = CK.x α t
  coverL : ∀ α t, πL.onPoints (coverX α t) = CL.x (ρ α) t

/-- Realize the pinned comparison supplied by a common geometric cover.

The proof uses only the quotient kernel and coordinate-descent interfaces: a
point-group factorization is upgraded to a regular morphism in each direction,
and the two factorizations are shown to be inverse by surjectivity of the
cover maps.  Thus the regularity claim does not rely on an abstract
point-group presentation alone.
-/
public theorem pinnedChevalleyIso_of_quotientData
    {U K L : Variety k} [AlgebraicGroup U] [AlgebraicGroup K]
    [AlgebraicGroup L]
    {TK : ClosedSubgroup K} {TL : ClosedSubgroup L}
    {DK : RootGroupData K TK} {DL : RootGroupData L TL}
    (CK : ChevalleyData K DK) (CL : ChevalleyData L DL)
    (ρ : DK.Root ≃ DL.Root)
    (P : PinnedChevalleyQuotientData (U := U) CK CL ρ)
    : ∃ e : AlgebraicGroup.Iso K L,
        e.hom.comp P.πK = P.πL ∧
        e.inv.comp P.πL = P.πK ∧
        ∀ α t, e.toMulEquiv (CK.x α t) = CL.x (ρ α) t := by
  obtain ⟨e, hcompKL, hcompLK⟩ :=
    quotient_comparison_iso_of_surjective_kernel_eq_of_coordinate_factorization
      P.πK P.πL P.πK_surjective P.πL_surjective P.kernel_eq
      P.πK_coordinate_factorization P.πL_coordinate_factorization
  refine ⟨e, hcompKL, hcompLK, ?_⟩
  intro α t
  change e.hom.onPoints (CK.x α t) = CL.x (ρ α) t
  rw [← P.coverK α t, ← P.coverL α t]
  exact congrArg (fun f : AlgebraicGroup.Morphism U L => f.onPoints (P.coverX α t)) hcompKL

end Theory.AlgebraicGroup
