module

public import Theory.Character.ModularBlock.PrincipalPrimitivity

/-!
# The extra involution Brauer factor

The compatible local principal selector is a central-idempotent factor of
an involution Brauer image. Their difference is therefore a central
idempotent orthogonal to the local selector and contained in the Brauer
image. An element orthogonal to an augmentation-one selector has
augmentation zero, by applying the augmentation homomorphism.

These elementary complement identities underlie both the relative-transfer
proof and the primitive-factor extraction in Brauer's Third Main argument.
Ported from the corresponding statements in
`c3503435:glauberman_zStar/Submission/ZStar/RelativeTransferBrauer.lean`.
The complement definition is exposed for the subsequent factor calculations.
-/

public section
noncomputable section
namespace ModularBlock.RelativeTransferBrauer
open ModularBlock PrincipalBlockConstruction
universe u v

theorem augmentation_eq_zero_of_mul_eq_zero_of_right_eq_one
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (b e : MonoidAlgebra R G)
    (hbe : b * e = 0)
    (he : groupAlgebraAugmentation R G e = 1) :
    groupAlgebraAugmentation R G b = 0 := by
  have h := congrArg (groupAlgebraAugmentation R G) hbe
  simpa [map_mul, he] using h


theorem centralizerFactor_augmentation_eq_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (horth : b *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) = 0) :
    groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G)) b = 0 := by
  exact augmentation_eq_zero_of_mul_eq_zero_of_right_eq_one b _ horth
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
      d (Subgroup.centralizer ({z} : Set G)))

@[expose] noncomputable def extraBrauerFactor
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)) :=
  BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer ({z} : Set G))

theorem extraBrauerFactor_mem_center
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    extraBrauerFactor d z ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  rw [extraBrauerFactor, mul_sub, sub_mul]
  rw [Semigroup.mem_center_iff.mp
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z) a,
    Semigroup.mem_center_iff.mp
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_mem_center
        d (Subgroup.centralizer ({z} : Set G))) a]

theorem extraBrauerFactor_isIdempotent
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    IsIdempotentElem (extraBrauerFactor d z) := by
  let eB := BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  let eL := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
    (Subgroup.centralizer ({z} : Set G))
  have hfactor : eL * eB = eL := by
    exact BlockPrimitivity.localPrincipalBlockElement_mul_involutionBrauer_eq_self
      d z hz
  have hcomm : eB * eL = eL := by
    have hc := Semigroup.mem_center_iff.mp
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z) eL
    rw [← hc, hfactor]
  exact IsIdempotentElem.sub
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d (Subgroup.centralizer ({z} : Set G)))
    (BrauerBlockReduction.involutionBrauerPrincipalBlockElement_isIdempotent d z hz)
    hfactor hcomm

theorem extraBrauerFactor_mul_local_eq_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    extraBrauerFactor d z *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) = 0 := by
  let eB := BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  let eL := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
    (Subgroup.centralizer ({z} : Set G))
  have hfactor : eL * eB = eL := by
    exact BlockPrimitivity.localPrincipalBlockElement_mul_involutionBrauer_eq_self
      d z hz
  have hcomm : eB * eL = eL := by
    have hc := Semigroup.mem_center_iff.mp
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z) eL
    rw [← hc, hfactor]
  change (eB - eL) * eL = 0
  rw [sub_mul, hcomm,
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d (Subgroup.centralizer ({z} : Set G)), sub_self]

theorem extraBrauerFactor_mul_brauer_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    extraBrauerFactor d z *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
      extraBrauerFactor d z := by
  let eB := BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  let eL := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
    (Subgroup.centralizer ({z} : Set G))
  have hfactor : eL * eB = eL := by
    exact BlockPrimitivity.localPrincipalBlockElement_mul_involutionBrauer_eq_self
      d z hz
  change (eB - eL) * eB = eB - eL
  rw [sub_mul,
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement_isIdempotent d z hz,
    hfactor]

end ModularBlock.RelativeTransferBrauer

