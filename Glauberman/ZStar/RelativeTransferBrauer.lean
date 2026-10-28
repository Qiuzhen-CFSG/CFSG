module
public import Theory.Character.ModularBlock.PrincipalCornerTransfer
public import Theory.Character.ModularBlock.IsolatedTransferRecovery
public import Glauberman.ZStar.LocalIsolation

/-!
# Principal Brauer equality from weak closure

An involution central and weakly closed in a chosen Sylow two-subgroup has
principal Brauer equality at its centralizer. Weak closure first gives the
usual commuting-conjugates isolation condition. The characteristic-two
coset pairing then shows that centralizer restriction recovers the relative
transfer of every central local element.

Apply this recovery to the extra central-idempotent factor of the ambient
Brauer image over the compatible local principal selector. It is orthogonal
to the local principal selector and has augmentation zero. Its ambient
principal-corner transfer is nilpotent by the proved principal-primitivity
theorem, so recovery forces the extra factor to vanish.

This assembles the source-faithful endpoint of
`Submission/ZStar/RelativeTransferBrauer.lean` at revision `c3503435`
of `public/lean-eval/glauberman_zStar`. Generic transfer, recovery, and
corner calculations live in their lower `Theory` modules. Compatibility
exports preserve the source-facing transfer API for the subsequent Third
Main argument. The additional cross-term interfaces are retained, while the
actual isolated-involution proof uses cancellation of the full remainder.
-/

public section
noncomputable section
open scoped BigOperators
namespace Glauberman.ZStar.RelativeTransferBrauer
open ModularBlock PrincipalBlockConstruction BenderSuzuki.PFAppendixIII
universe u v
attribute [local instance] Fintype.ofFinite

export ModularBlock.RelativeTransferBrauer
  (subgroupSubtypeMap
    conjugationMap
    subgroupSubtypeMap_single
    subgroupSubtypeMap_of
    conjugationMap_single
    conjugationMap_apply_image
    centralizerRestriction_conjugationMap_apply_image
    conjugationMap_apply
    conjugationMap_mul_subgroup_eq
    conjugationMap_out_eq_of_mk_eq
    relativeTransfer
    relativeTransfer_zero
    relativeTransfer_add
    relativeTransfer_conjugation_invariant
    relativeTransfer_mem_center
    augmentation_conjugationMap
    augmentation_relativeTransfer
    mapRingHom_relativeTransfer
    conjugationMap_one
    relativeTransferRemainder
    relativeTransfer_eq_subtypeMap_add_remainder
    centralizerRestriction_subgroupSubtypeMap
    centralizerRestriction_relativeTransfer_eq_add_remainder
    mul_centralizerRestriction_relativeTransfer_eq_self_iff_crossTerms
    centralizerFactor_relativeTransfer_augmentation_eq_zero
    principalCornerTransfer
    principalCornerTransfer_mem_center
    principalCornerTransfer_mul_reducedPrincipalBlockElement
    principalCornerTransfer_augmentation_eq_zero
    centralizerRestriction_principalCornerTransfer_mul_eq_self
    centralizerFactor_eq_zero_of_relativeTransfer_recovery
    augmentation_eq_zero_of_mul_eq_zero_of_right_eq_one
    centralizerFactor_augmentation_eq_zero
    extraBrauerFactor
    extraBrauerFactor_mem_center
    extraBrauerFactor_isIdempotent
    extraBrauerFactor_mul_local_eq_zero
    extraBrauerFactor_mul_brauer_eq_self
    centralizerRestriction_conjugationMap_z_mul
    fixedCoset_eq_one_of_isolated
    centralizerRestriction_relativeTransfer_eq_self_of_isolated
    representativeIsolation_of_isolated)

/-- If every nonidentity-coset cross term annihilates the extra factor, then
the ambient and compatible local principal Brauer selectors coincide. -/
theorem involutionPrincipalBrauerEquality_of_extraFactor_crossTerms_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1)
    (hcross :
      extraBrauerFactor d z * BrauerMap.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z
          (relativeTransferRemainder
            (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer ({z} : Set G)) (extraBrauerFactor d z)) = 0) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  let b := extraBrauerFactor d z
  have hbCenter := extraBrauerFactor_mem_center d z
  have hbIdem := extraBrauerFactor_isIdempotent d z hz
  have hrecover : b * BrauerMap.centralizerRestriction
      (BrauerBlockReduction.principalResidueField d) z
      (relativeTransfer (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G)) b) = b :=
    (mul_centralizerRestriction_relativeTransfer_eq_self_iff_crossTerms
      z b hbCenter hbIdem).2 hcross
  have hzero : b = 0 :=
    centralizerFactor_eq_zero_of_relativeTransfer_recovery d z hz b hbCenter
      (by exact extraBrauerFactor_mul_local_eq_zero d z hz)
      (by exact extraBrauerFactor_mul_brauer_eq_self d z hz)
      hrecover
  change CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer ({z} : Set G)) =
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  exact (sub_eq_zero.mp hzero).symm

/-- A nonidentity right coset has no representative in the subgroup. -/
theorem quotientOut_not_mem_of_ne_identityCoset
    {G : Type v} [Group G] (H : Subgroup G) (q : G ⧸ H)
    (hq : q ≠ (QuotientGroup.mk (1 : G) : G ⧸ H)) :
    q.out ∉ H := by
  intro hout
  apply hq
  calc
    q = QuotientGroup.mk q.out := (QuotientGroup.out_eq' q).symm
    _ = QuotientGroup.mk (1 : G) := by
      simpa using (QuotientGroup.mk_mul_of_mem (1 : G) hout)

/-- Outside the involution centralizer, a conjugate cannot commute with the
involution under the standard isolation hypothesis. -/
theorem conjugate_not_commute_of_not_mem_centralizer
    {G : Type v} [Group G] (z g : G)
    (hisolated : ∀ x : G,
      (x * z * x⁻¹) * z = z * (x * z * x⁻¹) → x * z * x⁻¹ = z)
    (hg : g ∉ Subgroup.centralizer ({z} : Set G)) :
    ¬ (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
  intro hcomm
  apply hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have heq := hisolated g hcomm
  have h := congrArg (fun x : G => x * g) heq
  simpa [mul_assoc] using h

/-- Hence every nonidentity transfer representative conjugates the isolated
involution to a noncommuting involution. -/
theorem nonidentity_transferRepresentative_conjugate_not_commute
    {G : Type v} [Group G] (z : G)
    (hisolated : ∀ x : G,
      (x * z * x⁻¹) * z = z * (x * z * x⁻¹) → x * z * x⁻¹ = z)
    (q : G ⧸ Subgroup.centralizer ({z} : Set G))
    (hq : q ≠ (QuotientGroup.mk (1 : G) :
      G ⧸ Subgroup.centralizer ({z} : Set G))) :
    ¬ (q.out * z * q.out⁻¹) * z = z * (q.out * z * q.out⁻¹) := by
  exact conjugate_not_commute_of_not_mem_centralizer z q.out hisolated
    (quotientOut_not_mem_of_ne_identityCoset
      (Subgroup.centralizer ({z} : Set G)) q hq)

/-- The preceding noncommutation conclusion under the actual local Z-star
hypotheses. -/
theorem nonidentity_transferRepresentative_conjugate_not_commute_of_weaklyClosed
    {G : Type v} [Group G] [Finite G]
    (S : Sylow 2 G) (z : G)
    (hzI : BenderSuzuki.PFAppendixIII.IsInvolution z)
    (hzCentral : ∀ s, s ∈ (S : Subgroup G) → s * z = z * s)
    (hzWeak : IsWeaklyClosedInSylow z (S : Subgroup G))
    (q : G ⧸ Subgroup.centralizer ({z} : Set G))
    (hq : q ≠ (QuotientGroup.mk (1 : G) :
      G ⧸ Subgroup.centralizer ({z} : Set G))) :
    ¬ (q.out * z * q.out⁻¹) * z = z * (q.out * z * q.out⁻¹) := by
  exact nonidentity_transferRepresentative_conjugate_not_commute z
    (isolated_of_central_weaklyClosed
      S z hzI hzCentral hzWeak) q hq

/-- Termwise annihilation implies annihilation of the full nonidentity-coset
Brauer remainder.  Thus the remaining block-theoretic input can be supplied
one coset at a time. -/
theorem mul_centralizerRestriction_remainder_eq_zero_of_each
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (z : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (hterm : ∀ q : G ⧸ Subgroup.centralizer ({z} : Set G),
      q ≠ (QuotientGroup.mk (1 : G) :
        G ⧸ Subgroup.centralizer ({z} : Set G)) →
      b * BrauerMap.centralizerRestriction R z
        (conjugationMap R (Subgroup.centralizer ({z} : Set G)) q.out b) = 0) :
    b * BrauerMap.centralizerRestriction R z
        (relativeTransferRemainder R
          (Subgroup.centralizer ({z} : Set G)) b) = 0 := by
  classical
  let H := Subgroup.centralizer ({z} : Set G)
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let q0 : G ⧸ H := QuotientGroup.mk (1 : G)
  change b * BrauerMap.centralizerRestriction R z
      (∑ q ∈ (Finset.univ.erase q0), conjugationMap R H q.out b) = 0
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro q hq
  apply hterm q
  exact (Finset.mem_erase.mp hq).1

/-- Per-coset cross-term orthogonality is sufficient for principal Brauer
equality. The isolated-involution argument instead proves cancellation of
the full remainder by pairing cosets. -/
theorem involutionPrincipalBrauerEquality_of_extraFactor_each_crossTerm_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1)
    (hterm : ∀ q : G ⧸ Subgroup.centralizer ({z} : Set G),
      q ≠ (QuotientGroup.mk (1 : G) :
        G ⧸ Subgroup.centralizer ({z} : Set G)) →
      extraBrauerFactor d z * BrauerMap.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z
        (conjugationMap (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer ({z} : Set G)) q.out
          (extraBrauerFactor d z)) = 0) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  apply involutionPrincipalBrauerEquality_of_extraFactor_crossTerms_zero d z hz
  exact mul_centralizerRestriction_remainder_eq_zero_of_each z
    (extraBrauerFactor d z) hterm

/-- Principal Brauer equality at an isolated involution, obtained solely from
the characteristic-two relative-transfer pairing and the primitive-corner
argument. -/
theorem involutionPrincipalBrauerEquality_of_isolated
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : BenderSuzuki.PFAppendixIII.IsInvolution z)
    (hisolated : ∀ x : G,
      (x * z * x⁻¹) * z = z * (x * z * x⁻¹) → x * z * x⁻¹ = z) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  let b := extraBrauerFactor d z
  have hz : z * z = 1 := by simpa [pow_two] using hzI.sq_eq_one
  have hbCenter : b ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))) := by
    simpa [b] using extraBrauerFactor_mem_center d z
  have hbIdem : IsIdempotentElem b := by
    simpa [b] using extraBrauerFactor_isIdempotent d z hz
  have hrestriction :
      BrauerMap.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z
          (relativeTransfer (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer ({z} : Set G)) b) = b :=
    centralizerRestriction_relativeTransfer_eq_self_of_isolated z hz b hbCenter
      (representativeIsolation_of_isolated z hisolated)
  have hrecover : b * BrauerMap.centralizerRestriction
      (BrauerBlockReduction.principalResidueField d) z
      (relativeTransfer (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G)) b) = b := by
    rw [hrestriction, hbIdem.eq]
  have hzero : b = 0 :=
    centralizerFactor_eq_zero_of_relativeTransfer_recovery d z hz b hbCenter
      (by simpa [b] using extraBrauerFactor_mul_local_eq_zero d z hz)
      (by simpa [b] using extraBrauerFactor_mul_brauer_eq_self d z hz)
      hrecover
  change CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer ({z} : Set G)) =
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  have hextra : extraBrauerFactor d z = 0 := by simpa [b] using hzero
  exact (sub_eq_zero.mp hextra).symm

/-- In particular, the local Z-star hypotheses force principal Brauer
equality at the distinguished weakly closed involution. -/
theorem involutionPrincipalBrauerEquality_of_weaklyClosed
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (S : Sylow 2 G) (z : G)
    (hzI : BenderSuzuki.PFAppendixIII.IsInvolution z)
    (hzCentral : ∀ s, s ∈ (S : Subgroup G) → s * z = z * s)
    (hzWeak : IsWeaklyClosedInSylow z (S : Subgroup G)) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  exact involutionPrincipalBrauerEquality_of_isolated d z hzI
    (isolated_of_central_weaklyClosed S z hzI hzCentral hzWeak)

end Glauberman.ZStar.RelativeTransferBrauer

