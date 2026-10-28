module
public import Theory.Character.ModularBlock.RelativeTransferBasic

/-!
# The nonidentity-coset remainder of relative transfer

The identity coset contributes the embedded subgroup-algebra element to
relative transfer. All other cosets form an explicit remainder. Restricting
back to an involution centralizer recovers the original element plus the
restricted remainder. For an idempotent, multiplicative recovery is exactly
annihilation of the remainder's cross terms.

Split the finite sum at the identity coset, use representative independence,
and use that centralizer restriction is a left inverse to subgroup embedding.
The remainder sum is exposed for the subsequent coset-involution cancellation.

Ported from the identity-coset decomposition in
`Submission/ZStar/RelativeTransferBrauer.lean` at revision `c3503435`
of `public/lean-eval/glauberman_zStar`. The statements use only generic
transfer and restriction, with no principal-block or isolation hypothesis.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.RelativeTransferBrauer
universe u v
attribute [local instance] Fintype.ofFinite

@[simp] theorem conjugationMap_one
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (b : MonoidAlgebra R H) :
    conjugationMap R H 1 b = subgroupSubtypeMap R H b := by
  rw [conjugationMap_apply, inv_one, map_one, one_mul, mul_one]

/-- The sum of all transfer terms except the distinguished identity coset. -/
noncomputable def relativeTransferRemainder
    (R : Type u) {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) (b : MonoidAlgebra R H) :
    MonoidAlgebra R G := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  exact ∑ q ∈ (Finset.univ.erase
      (QuotientGroup.mk (1 : G) : G ⧸ H)),
    conjugationMap R H q.out b

/-- The identity coset contributes exactly the embedded local element; all
other cosets form the explicit transfer remainder. -/
theorem relativeTransfer_eq_subtypeMap_add_remainder
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) (b : MonoidAlgebra R H)
    (hb : b ∈ Set.center (MonoidAlgebra R H)) :
    relativeTransfer R H b =
      subgroupSubtypeMap R H b + relativeTransferRemainder R H b := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let q0 : G ⧸ H := QuotientGroup.mk (1 : G)
  have hterm :
      conjugationMap R H (Quotient.out q0) b =
        subgroupSubtypeMap R H b := by
    calc
      conjugationMap R H (Quotient.out q0) b =
          conjugationMap R H 1 b :=
        conjugationMap_out_eq_of_mk_eq H q0 1 rfl b hb
      _ = subgroupSubtypeMap R H b := conjugationMap_one H b
  have hsum := Finset.sum_erase_add
    (Finset.univ : Finset (G ⧸ H))
    (fun q : G ⧸ H => conjugationMap R H q.out b)
    (Finset.mem_univ q0)
  rw [hterm] at hsum
  simpa [relativeTransfer, relativeTransferRemainder, q0, add_comm] using hsum.symm

/-- Restriction back to a centralizer is a left inverse to the subgroup
algebra embedding. -/
@[simp] theorem centralizerRestriction_subgroupSubtypeMap
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) :
    BrauerMap.centralizerRestriction R z
        (subgroupSubtypeMap R (Subgroup.centralizer ({z} : Set G)) b) = b := by
  classical
  ext h
  simp [BrauerMap.centralizerRestriction_apply, subgroupSubtypeMap,
    MonoidAlgebra.mapDomainRingHom_apply]

/-- Exact elementary part of the transfer/Brauer calculation: the identity
coset gives `b`, and every unresolved contribution lies in the displayed
nonidentity-coset remainder. -/
theorem centralizerRestriction_relativeTransfer_eq_add_remainder
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (z : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (hb : b ∈ Set.center
      (MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))) :
    BrauerMap.centralizerRestriction R z
        (relativeTransfer R (Subgroup.centralizer ({z} : Set G)) b) =
      b + BrauerMap.centralizerRestriction R z
        (relativeTransferRemainder R
          (Subgroup.centralizer ({z} : Set G)) b) := by
  rw [relativeTransfer_eq_subtypeMap_add_remainder _ b hb, map_add,
    centralizerRestriction_subgroupSubtypeMap]

/-- For an idempotent local factor, the desired self-recovery under
`Brauer ∘ transfer` is equivalent to annihilation of all nonidentity-coset
cross terms. The isolated-involution calculation proves this cancellation
by pairing cosets. -/
theorem mul_centralizerRestriction_relativeTransfer_eq_self_iff_crossTerms
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (z : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (hbCenter : b ∈ Set.center
      (MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))))
    (hbIdem : IsIdempotentElem b) :
    b * BrauerMap.centralizerRestriction R z
          (relativeTransfer R (Subgroup.centralizer ({z} : Set G)) b) = b ↔
      b * BrauerMap.centralizerRestriction R z
          (relativeTransferRemainder R
            (Subgroup.centralizer ({z} : Set G)) b) = 0 := by
  rw [centralizerRestriction_relativeTransfer_eq_add_remainder z b hbCenter,
    mul_add, hbIdem.eq, add_eq_left]

end ModularBlock.RelativeTransferBrauer

