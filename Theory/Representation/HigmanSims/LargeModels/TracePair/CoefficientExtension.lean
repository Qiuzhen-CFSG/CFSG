module

public import Theory.Representation.AbsolutelyIrreducible
public import Theory.Representation.InjectiveDescent

/-!+# Absolute irreducibility under coefficient embeddings

Extend a finite coordinate representation to the algebraic closure of the
target field. Entrywise coefficient maps compose, so this is equivalent to
extending the original representation directly to that closure. Thus absolute
irreducibility is preserved. In particular this applies to the Frobenius
conjugate of the degree-896 HS candidate without a second matrix certificate.

This is the usual scalar-extension argument, using the tensor-product
definition of absolute irreducibility in `Theory.Representation`.
-/

public section
namespace Representation

/-- Every coefficient embedding preserves absolute irreducibility of a
finite coordinate representation. -/
theorem isAbsolutelyIrreducible_mapCoefficients
    {k K G ι : Type*} [Field k] [Field K] [Monoid G]
    [Fintype ι] [DecidableEq ι]
    (f : k →+* K) (ρ : Representation k G (ι → k))
    (hρ : ρ.IsAbsolutelyIrreducible) :
    (mapCoefficients f ρ).IsAbsolutelyIrreducible := by
  let j : k →+* AlgebraicClosure K := (algebraMap K (AlgebraicClosure K)).comp f
  let : Algebra k (AlgebraicClosure K) := j.toAlgebra
  let := hρ
  have hi : (mapCoefficients j ρ).IsIrreducible :=
    (extendScalarsMapCoefficientsEquiv (E := AlgebraicClosure K) ρ).irreducible_euqiv.mp
      (IsAbsolutelyIrreducible.irreducible_of_extension ρ (AlgebraicClosure K))
  have he : mapCoefficients (algebraMap K (AlgebraicClosure K)) (mapCoefficients f ρ) =
      mapCoefficients j ρ := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.toMatrix'.injective
    simp only [mapCoefficients_toMatrix]
    rfl
  constructor
  apply (extendScalarsMapCoefficientsEquiv
    (E := AlgebraicClosure K) (mapCoefficients f ρ)).irreducible_euqiv.mpr
  rwa [he]

end Representation
