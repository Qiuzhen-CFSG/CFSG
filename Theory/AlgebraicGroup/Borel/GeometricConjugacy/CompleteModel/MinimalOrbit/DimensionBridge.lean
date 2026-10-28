module
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.FiberAlgebra
public import Theory.AlgebraicGroup.Variety.GeometricDimension
public import Theory.AlgebraicGroup.Variety.AffineGroupScheme
import all Theory.AlgebraicGroup.Dimension.Fiber
import all Theory.AlgebraicGroup.Variety.GeometricDimension

/-!
# Comparing affine and geometric group dimensions

The geometric Krull dimension of an affine algebraic group is the natural-number
image of its componentwise transcendence-degree dimension. For the upper bound,
every maximal-ideal height is bounded by the dimensions of the minimal-prime
quotients below it. The lower bound comes from the irreducible identity component
and the surjective restriction of polynomial functions. Disconnected groups and
zero-dimensional groups are included.

This supplies the dimension-convention bridge in Borel's orbit–stabilizer argument,
*Linear Algebraic Groups*, §11.1 (`refs/KGroup/Bor1/Chapter4.tex`). The internal
imports reuse the commutative-algebra proofs without widening their old interfaces.
-/

open Theory.AlgebraicGroup TopologicalSpace AlgebraicGeometry
open Cardinal

universe u
namespace Theory.AlgebraicGroup.Variety.Geometric.MinimalOrbit

public theorem ringKrullDim_eq_trdeg_toNat
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [IsDomain A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toNat (Algebra.trdeg k A) : WithBot ℕ∞) := by
  obtain ⟨n, hn, htr⟩ := exists_dimension_eq_nat_and_trdeg
    (k := k) (A := A) (K := FractionRing A)
  rw [trdeg_isFractionRing_eq (k := k) (A := A)] at htr
  rw [htr, Cardinal.toNat_natCast]
  exact hn

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem ofAffine_group_dimension (G : Theory.AlgebraicGroup.Variety k) [AlgebraicGroup G] :
    dimension (ofAffine G) = (Cardinal.toNat (Variety.dimension G) : WithBot ℕ∞) := by
  let A := Variety.PolynomialFunction G
  let : Algebra k A := polynomialFunctionAlgebra G
  let : Algebra.FiniteType k A := polynomialFunction_finiteType G
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hmain : ringKrullDim A = (Cardinal.toNat (Variety.dimension G) : WithBot ℕ∞) := by
    apply le_antisymm
    · apply (ringKrullDim_le_iff_isMaximal_height_le _).mpr
      intro M hM
      let : M.IsMaximal := hM
      have hbound : M.height ≤ (Cardinal.toNat (Variety.dimension G) : ℕ∞) := by
        apply height_le_of_minimalPrimes_quotient_height_le
        intro q hq hqM
        let : q.IsPrime := hq.isPrime
        let : (M.map (Ideal.Quotient.mk q)).IsMaximal :=
          Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
            (by rw [Ideal.mk_ker]; exact hqM)
        rw [domain_maximal_height_eq_trdeg (k := k) (A ⧸ q)]
        have hdim : Algebra.trdeg k (A ⧸ q) ≤ Variety.dimension G := by
          rw [← dimension_closedSubvariety_polynomialFunctionIdealZeroSet_of_isPrime G q]
          exact closedSubvariety_dimension_le G _
        exact_mod_cast (Cardinal.toNat_le_iff_le_of_lt_aleph0
          (trdeg_lt_aleph0_of_finiteType (R := k) (S := A ⧸ q))
          (variety_dimension_lt_aleph0 G)).mpr hdim
      exact WithBot.coe_le_coe.mpr hbound
    · let H := identityComponentClosedSubgroup G
      let B := Variety.PolynomialFunction H.carrierVariety
      let : Algebra k B := polynomialFunctionAlgebra H.carrierVariety
      let : Algebra.FiniteType k B := polynomialFunction_finiteType H.carrierVariety
      have hirr : _root_.IsIrreducible (Set.univ : Set (Variety.Point H.carrierVariety)) :=
        connectedAlgebraicGroup_irreducible H.carrierVariety
          (identityComponentClosedSubgroup_carrier_isConnected G)
      let : IsDomain (coordinateRing H.carrierVariety) :=
        isDomain_coordinateRing_of_isIrreducible _ hirr
      let : IsDomain B :=
        (coordinateRingAlgEquivPolynomialFunction H.carrierVariety).toRingEquiv.isDomain_iff.mp
          inferInstance
      have hdimB : Variety.dimension G = Algebra.trdeg k B := by
        rw [← dimension_identityComponentClosedSubgroup G]
        exact dimension_eq_trdeg_polynomialFunction_of_isIrreducible H.carrierVariety hirr
      rw [hdimB, ← ringKrullDim_eq_trdeg_toNat (k := k) (A := B)]
      exact ringKrullDim_le_of_surjective H.restrictionRingHom H.restrictionRingHom_surjective
  change topologicalKrullDim (PrimeSpectrum (coordinateRing G)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  rw [(coordinateRingAlgEquivPolynomialFunction G).toRingEquiv.ringKrullDim]
  exact hmain

end Theory.AlgebraicGroup.Variety.Geometric.MinimalOrbit
