module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Theory.GroupTheory.DihedralInvolutionLift
public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoFusion
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# The rotation preimage in the quaternion-core dihedral case

An identification of the Sylow quotient by the actual core with the dihedral
group of order eight defines the rotation preimage canonically. It contains
the core and has index two. Also, an element of the core has fixed core of
order at least sixteen, so no fixed-eight involution belongs to the core.

These reductions separate the elementary quotient and extraspecial arguments
from the quaternion action calculations in Janko–Thompson, Math. Z. 113
(1970), §4, case (c), printed p.392. No rank bound on arbitrary elementary
subgroups is used.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G]

/-- The actual Sylow-to-dihedral quotient map, for a supplied identification. -/
@[expose] public def quaternionDihedralHom (S : Sylow 2 G)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4) : S →* DihedralGroup 4 :=
  e.toMonoidHom.comp (QuotientGroup.mk' (omegaCorePreimage S))

/-- The maximal subgroup lying above the cyclic-four rotations. -/
@[expose] public def quaternionDihedralMaximal (S : Sylow 2 G)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4) : Subgroup S :=
  DihedralGroup.rotationPreimage (quaternionDihedralHom S e)

/-- The dihedral quotient map is onto. -/
public theorem quaternionDihedralHom_surjective (S : Sylow 2 G)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4) :
    Function.Surjective (quaternionDihedralHom S e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The kernel is precisely the original core preimage. -/
public theorem quaternionDihedralHom_ker (S : Sylow 2 G)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4) :
    (quaternionDihedralHom S e).ker = omegaCorePreimage S := by
  ext x
  change e ((QuotientGroup.mk' (omegaCorePreimage S)) x) = 1 ↔ _
  rw [map_eq_one_iff e e.injective]
  exact QuotientGroup.eq_one_iff x

/-- Core membership is detected by the dihedral quotient. -/
public theorem quaternionDihedralHom_eq_one_iff (S : Sylow 2 G)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4) (x : S) :
    quaternionDihedralHom S e x = 1 ↔ x ∈ omegaCorePreimage S := by
  change x ∈ (quaternionDihedralHom S e).ker ↔ _
  rw [quaternionDihedralHom_ker]

/-- The rotation preimage has index two in the original Sylow. -/
public theorem quaternionDihedralMaximal_index (S : Sylow 2 G)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4) :
    (quaternionDihedralMaximal S e).index = 2 :=
  DihedralGroup.rotationPreimage_index _ (quaternionDihedralHom_surjective S e)

/-- The actual core is contained in the maximal rotation preimage. -/
public theorem omegaCorePreimage_le_quaternionDihedralMaximal (S : Sylow 2 G)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4) :
    omegaCorePreimage S ≤ quaternionDihedralMaximal S e := by
  rw [← quaternionDihedralHom_ker S e]
  exact DihedralGroup.ker_le_rotationPreimage _

/-- A fixed core of order eight forces its actor outside the order-32 core. -/
public theorem not_mem_omegaCorePreimage_of_fixed_card_eight [Finite G] (S : Sylow 2 G)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (x : S) (hx : Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8) :
    x ∉ omegaCorePreimage S := by
  intro hxP
  let P := omegaCorePreimage S
  let : IsExtraspecial 2 P :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  have hcard : Nat.card P = 32 := (card_omegaCorePreimage S).trans hH
  have hbound := IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two
    hcard (⟨x, hxP⟩ : P)
  have hmap := map_subtype_centralizer_singleton P (⟨x, hxP⟩ : P)
  have hcount : Nat.card (centralizer ({(⟨x, hxP⟩ : P)} : Set P)) = 8 := by
    rw [← card_map_of_injective P.subtype_injective, hmap]
    exact hx
  omega

end Stellmacher.Recognition.NormalEightNonnormalImage
