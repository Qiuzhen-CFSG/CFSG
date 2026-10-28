module
public import Theory.Character.ModularBlock.RelativeTransferBasic
public import Theory.Character.ModularBlock.PrimitiveCorner
public import Theory.Character.ModularBlock.InvolutionExtraFactor

/-!
# Vanishing from principal-corner transfer recovery

A local central factor orthogonal to the compatible principal selector
has augmentation zero. Multiplying its relative transfer by the ambient
principal selector gives a central augmentation-zero element in the
principal corner. If Brauer restriction followed by multiplication recovers
the local factor, primitive-corner nilpotence forces that factor to vanish.

The proof verifies centrality, corner membership, and augmentation using the
proved transfer formulas. Multiplicativity of Brauer restriction on central
elements and the local factor relation supply recovery by the corner witness.
The completed primitive-corner theorem then gives the contradiction.

Ported from the principal-corner transfer section of
`Submission/ZStar/RelativeTransferBrauer.lean` at revision `c3503435`
of `public/lean-eval/glauberman_zStar`. Principal primitivity is a proved
import; the local recovery hypothesis is discharged separately by isolation.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.RelativeTransferBrauer
open PrincipalBlockConstruction
universe u v
attribute [local instance] Fintype.ofFinite

/-- Consequently the ambient relative transfer of a nonprincipal local
factor also has augmentation zero. -/
theorem centralizerFactor_relativeTransfer_augmentation_eq_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (horth : b *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) = 0) :
    groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d) G
        (relativeTransfer (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer ({z} : Set G)) b) = 0 := by
  rw [augmentation_relativeTransfer,
    centralizerFactor_augmentation_eq_zero d z b horth, mul_zero]

/-- The ambient principal-corner witness obtained by multiplying a relative
transfer by the reduced ambient principal selector. -/
noncomputable def principalCornerTransfer
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G))) :
    MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G :=
  BrauerBlockReduction.reducedPrincipalBlockElement d *
    relativeTransfer (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)) b

theorem principalCornerTransfer_mem_center
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (hb : b ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G)))) :
    principalCornerTransfer d z b ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) := by
  exact Set.mul_mem_center
    (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)
    (relativeTransfer_mem_center _ b hb)

theorem principalCornerTransfer_mul_reducedPrincipalBlockElement
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G))) :
    principalCornerTransfer d z b *
        BrauerBlockReduction.reducedPrincipalBlockElement d =
      principalCornerTransfer d z b := by
  let e := BrauerBlockReduction.reducedPrincipalBlockElement d
  let T := relativeTransfer (BrauerBlockReduction.principalResidueField d)
    (Subgroup.centralizer ({z} : Set G)) b
  have heCenter : e ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) :=
    BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d
  have hcomm : T * e = e * T :=
    Semigroup.mem_center_iff.mp heCenter T
  have heIdem : IsIdempotentElem e :=
    BrauerBlockReduction.reducedPrincipalBlockElement_isIdempotent d
  change (e * T) * e = e * T
  calc
    (e * T) * e = e * (T * e) := mul_assoc _ _ _
    _ = e * (e * T) := by rw [hcomm]
    _ = (e * e) * T := (mul_assoc _ _ _).symm
    _ = e * T := by rw [heIdem.eq]

theorem principalCornerTransfer_augmentation_eq_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (horth : b *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) = 0) :
    groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d) G
        (principalCornerTransfer d z b) = 0 := by
  rw [principalCornerTransfer, map_mul,
    BrauerBlockReduction.reducedPrincipalBlockElement_augmentation_eq_one,
    centralizerFactor_relativeTransfer_augmentation_eq_zero d z b horth,
    one_mul]

/-- If a local factor is a factor of the ambient Brauer selector and is
recovered by `Brauer ∘ transfer`, then the principal-corner transfer witness
acts as the identity on that local factor. -/
theorem centralizerRestriction_principalCornerTransfer_mul_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (hbCenter : b ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))))
    (hbBrauer : b *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z = b)
    (hrecover : b * BrauerMap.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z
        (relativeTransfer (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer ({z} : Set G)) b) = b) :
    BrauerMap.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z
          (principalCornerTransfer d z b) * b = b := by
  let e := BrauerBlockReduction.reducedPrincipalBlockElement d
  let T := relativeTransfer (BrauerBlockReduction.principalResidueField d)
    (Subgroup.centralizer ({z} : Set G)) b
  have heCenter : e ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) :=
    BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d
  have hTCenter : T ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) :=
    relativeTransfer_mem_center _ b hbCenter
  have hBr :
      BrauerMap.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z
          (principalCornerTransfer d z b) =
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z *
          BrauerMap.centralizerRestriction
            (BrauerBlockReduction.principalResidueField d) z T := by
    change BrauerMap.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z (e * T) = _
    exact BrauerMap.centralizerRestriction_mul_of_mem_center
      z hz e T heCenter hTCenter
  rw [hBr]
  have hbComm := Semigroup.mem_center_iff.mp hbCenter
    (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z *
      BrauerMap.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z T)
  calc
    (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z *
          BrauerMap.centralizerRestriction
            (BrauerBlockReduction.principalResidueField d) z T) * b =
        b * (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z *
          BrauerMap.centralizerRestriction
            (BrauerBlockReduction.principalResidueField d) z T) := hbComm
    _ = (b * BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z) *
          BrauerMap.centralizerRestriction
            (BrauerBlockReduction.principalResidueField d) z T :=
      (mul_assoc _ _ _).symm
    _ = b * BrauerMap.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z T := by rw [hbBrauer]
    _ = b := hrecover

/-- The complete transfer contradiction, with the sole remaining input
isolated as self-recovery of the local factor under `Brauer ∘ transfer`. -/
theorem centralizerFactor_eq_zero_of_relativeTransfer_recovery
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (hbCenter : b ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))))
    (horth : b *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) = 0)
    (hbBrauer : b *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z = b)
    (hrecover : b * BrauerMap.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z
        (relativeTransfer (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer ({z} : Set G)) b) = b) :
    b = 0 := by
  apply PrimitiveCorner.eq_zero_of_brauerRestriction_mul_eq_self_of_corner_augmentation_zero
    d z hz (principalCornerTransfer d z b) b
  · exact principalCornerTransfer_mem_center d z b hbCenter
  · exact principalCornerTransfer_mul_reducedPrincipalBlockElement d z b
  · exact principalCornerTransfer_augmentation_eq_zero d z b horth
  · exact centralizerRestriction_principalCornerTransfer_mul_eq_self
      d z hz b hbCenter hbBrauer hrecover

end ModularBlock.RelativeTransferBrauer

