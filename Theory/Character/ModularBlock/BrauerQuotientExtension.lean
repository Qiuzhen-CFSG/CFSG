module

public import Theory.Character.ModularBlock.BrauerCharacterBasis
public import Theory.Character.ModularBlock.CompatibleQuotientCongruence
public import Theory.Character.ModularBlock.CyclotomicDVR

/-!
# Compatible quotient splitting fields and eigenvalue lifts

The contracted quotient residue field embeds in the ambient residue field.
The latter is finite, hence algebraic over the former, so their algebraic
closures are isomorphic over the quotient residue field. We choose such an
isomorphism, retaining its commutative reduction square as part of the API.

For odd-order roots, injectivity of reduction on roots of unity identifies
the characteristic-zero lifts under this isomorphism. This supplies the
coefficient comparison for genuine Brauer-character inflation, at the
specified modular prime (the quotient construction in
`CompatibleQuotientCongruence` and the root-lifting construction in
`BrauerCoefficientExtension`). No block or Cartan comparison is assumed.
-/

public section
noncomputable section
namespace ModularBlock.BrauerCoefficientExtension
open PrincipalBlockConstruction BrauerBlockReduction CompatibleLocalBlock
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem residueFinite (d : PrincipalCongruenceBlockData G) :
    Finite (principalResidueField d) := by
  have hprime : d.primeIdeal ≠ ⊥ := by
    intro hbot
    have htwo := BlockPreliminaries.two_mem_of_liesOver d.primeIdeal d.primeIdeal_liesOverTwo
    rw [hbot, Ideal.mem_bot] at htwo
    exact two_ne_zero htwo
  exact CyclotomicDVR.cyclotomicOrder_quotient_finite
    (Nat.card_pos (α := G)).ne' d.eta_spec d.primeIdeal hprime

theorem exists_quotientSplittingFieldEquiv (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] :
    ∃ e : splittingField (compatibleQuotientPrincipalCongruenceBlockData d N) ≃+* splittingField d,
      ∀ x, e (residueInclusion (compatibleQuotientPrincipalCongruenceBlockData d N) x) =
        residueInclusion d (compatibleQuotientResidueFieldInclusion d N x) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  let K := principalResidueField q
  let J := principalResidueField d
  let L := splittingField d
  let M := splittingField q
  let : Algebra K J := (compatibleQuotientResidueFieldInclusion d N).toAlgebra
  let : Finite J := residueFinite d
  let : Algebra.IsAlgebraic K J := inferInstance
  let e : L ≃ₐ[K] M := IsAlgClosure.equivOfAlgebraic K J L M
  refine ⟨e.symm.toRingEquiv, ?_⟩
  intro x
  exact e.symm.commutes x

@[expose] def quotientSplittingFieldEquiv (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal] :
    splittingField (compatibleQuotientPrincipalCongruenceBlockData d N) ≃+* splittingField d :=
  (exists_quotientSplittingFieldEquiv d N).choose

theorem quotientSplittingFieldEquiv_residueInclusion (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal]
    (x : principalResidueField (compatibleQuotientPrincipalCongruenceBlockData d N)) :
    quotientSplittingFieldEquiv d N
        (residueInclusion (compatibleQuotientPrincipalCongruenceBlockData d N) x) =
      residueInclusion d (compatibleQuotientResidueFieldInclusion d N x) :=
  (exists_quotientSplittingFieldEquiv d N).choose_spec x

theorem quotientSplittingFieldEquiv_reduction (d : PrincipalCongruenceBlockData G)
    (N : Subgroup G) [N.Normal]
    (x : cyclotomicOrder (compatibleQuotientPrincipalCongruenceBlockData d N).eta) :
    quotientSplittingFieldEquiv d N
        (reduction (compatibleQuotientPrincipalCongruenceBlockData d N) x) =
      reduction d (cyclotomicOrderInclusion (quotientRoot_mem d N) x) := by
  exact quotientSplittingFieldEquiv_residueInclusion d N _

end ModularBlock.BrauerCoefficientExtension

namespace ModularBlock.BrauerCharacter
open PrincipalBlockConstruction BrauerCoefficientExtension CompatibleLocalBlock
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The coefficient equivalence preserves the complex lifts at the fixed prime. -/
theorem eigenvalueLift_quotientSplittingFieldEquiv
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (x : splittingField (compatibleQuotientPrincipalCongruenceBlockData d N))
    (hx : IsLiftable (compatibleQuotientPrincipalCongruenceBlockData d N) x) :
    eigenvalueLift d (quotientSplittingFieldEquiv d N x) =
      cyclotomicOrderInclusion (quotientRoot_mem d N)
        (eigenvalueLift (compatibleQuotientPrincipalCongruenceBlockData d N) x) := by
  obtain ⟨n, hn, hdiv, hpow⟩ := hx
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  have himage : quotientSplittingFieldEquiv d N x ^ n = 1 := by
    rw [← map_pow, hpow, map_one]
  rw [eigenvalueLift_eq_liftAtOrder d n hn
    (hdiv.trans N.card_quotient_dvd_card) _ himage,
    eigenvalueLift_eq_liftAtOrder q n hn hdiv x hpow]
  apply odd_root_eq_of_reduction_eq d hn hn
    (hdiv.trans N.card_quotient_dvd_card) (hdiv.trans N.card_quotient_dvd_card)
    (liftAtOrder_pow _ _ _ _ _ _)
  · let inclusion : cyclotomicOrder q.eta →+* cyclotomicOrder d.eta :=
      cyclotomicOrderInclusion (quotientRoot_mem d N)
    change inclusion (liftAtOrder q n hn hdiv x hpow) ^ n = 1
    rw [← map_pow, liftAtOrder_pow, map_one]
  · rw [reduction_liftAtOrder, ← quotientSplittingFieldEquiv_reduction,
      reduction_liftAtOrder]

end ModularBlock.BrauerCharacter
