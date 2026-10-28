module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Theory.AlgebraicGroup.Bor1.CoordinateRingSmooth
public import Theory.AlgebraicGroup.Bor1.MaximalCotangentLocalization
public import Theory.AlgebraicGroup.Bor1.SmoothRegularLocal
public import Theory.AlgebraicGroup.Bor1.TangentCotangentDimension
public import Theory.AlgebraicGroup.Dimension.Fiber

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup IsLocalRing

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false in
/-- The identity tangent space of an irreducible algebraic group has the
dimension of the group. -/
public theorem identityPointDerivation_finrank_eq_dimension_of_isIrreducible
    (K : Variety k) [AlgebraicGroup K]
    (hK : IsIrreducible (Set.univ : Set (Variety.Point K))) :
    Module.finrank k (IdentityPointDerivation K) =
      Cardinal.toNat (Variety.dimension K) := by
  let A := Variety.PolynomialFunction K
  let m : Ideal A := (K.pointPrime 1).asIdeal
  letI : m.IsMaximal := K.pointPrime_isMaximal 1
  letI : m.IsPrime := inferInstance
  letI : IsDomain (coordinateRing K) :=
    isDomain_coordinateRing_of_isIrreducible K hK
  letI : IsDomain A :=
    (coordinateRingAlgEquivPolynomialFunction K).toRingEquiv.isDomain_iff.mp
      inferInstance
  let eResidue : (A ⧸ m) ≃ₐ[k] k :=
    Ideal.quotientKerAlgEquivOfSurjective
      (polynomialFunctionPointAlgHom_surjective K 1)
  have hbase : Module.finrank k m.Cotangent =
      Module.finrank (A ⧸ m) m.Cotangent := by
    have hrank := rank_eq_of_equiv_equiv eResidue.symm
      (AddEquiv.refl m.Cotangent) eResidue.symm.bijective (by
        intro r z
        have hr : eResidue.symm r =
            Ideal.Quotient.mk m (algebraMap k A r) := by
          exact eResidue.symm.commutes r
        rw [hr]
        rfl)
    simpa only [Module.finrank] using congrArg Cardinal.toNat hrank
  letI : Algebra.Smooth k A :=
    polynomialFunction_smooth_of_algebraicGroup K
  letI : IsRegularLocalRing (Localization.AtPrime m) :=
    isRegularLocalRing_localizationAtPrime_of_smooth k A m
  letI : IsNoetherian (Localization.AtPrime m)
      (Localization.AtPrime m) := IsRegularLocalRing.toIsNoetherian
  have hregular :
      Module.finrank (ResidueField (Localization.AtPrime m))
          (CotangentSpace (Localization.AtPrime m)) =
        ringKrullDim (Localization.AtPrime m) :=
    (IsRegularLocalRing.iff_finrank_cotangentSpace
      (Localization.AtPrime m)).mp inferInstance
  have hheight : m.height = Cardinal.toNat (Algebra.trdeg k A) :=
    domain_maximal_height_eq_trdeg A m
  have hdimension : Variety.dimension K = Algebra.trdeg k A := by
    rw [dimension_eq_fractionRing_of_isIrreducible K hK,
      trdeg_fractionRing_eq]
    exact (coordinateRingAlgEquivPolynomialFunction K).trdeg_eq
  rw [identityPointDerivation_finrank_eq_cotangent K, hbase,
    maximalCotangent_finrank_eq_localization A m (Localization.AtPrime m)]
  have hlocal :
      Module.finrank (ResidueField (Localization.AtPrime m))
          (CotangentSpace (Localization.AtPrime m)) =
        Cardinal.toNat (Algebra.trdeg k A) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m
      (Localization.AtPrime m), hheight] at hregular
    exact_mod_cast hregular
  rw [hlocal, ← hdimension]

end Theory.AlgebraicGroup.Bor1
