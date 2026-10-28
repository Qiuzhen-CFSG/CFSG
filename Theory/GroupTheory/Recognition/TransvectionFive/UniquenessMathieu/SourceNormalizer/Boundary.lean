module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Orientation
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Transport
public import Theory.GroupTheory.SolvableResidual

/-!
# Corrected Mathieu ambient-normalizer and marked-local data

The boundary uses the full ambient normalizer quotients of the original
pulled-back row, column, and two rectangles. The last quotient has a normal
subgroup of order three with symmetric-six quotient: the source notation
S₆/Z₃ denotes this extension. The 40.4(2) data use the actual involution
centralizer I, its solvable residual I^∞, the fixed subgroup C_{A₂}(I^∞),
and the product XI inside N_G(A₂). The marked normalizer intersections are
retained for the coset geometry.

These records specify outstanding source conclusions; they do not assert their
existence. The proved consumers recover the natural row action and splitting
from actual point movement, using source 39.3. Construction from simplicity,
PointCoreFusion and MathieuFusion remains with the source-normalizer owner.
The incompatible legacy normalizer and pair-graph records are not used here.

Source: Aschbacher, *Sporadic Groups* (1994), 40.3–40.5 and the local data
used in 41.1–41.2, printed pp.217–221.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The second involution class is defined by actual G-conjugates of involutions
in Q outside the two marked root groups; Q is the original point two-core. -/
@[expose] def SecondInvolutionClass (t : G) : Prop :=
  ∃ q : G, q ∈ (centralizer ({z} : Set G)).pCoreIn 2 ∧ orderOf q = 2 ∧
    q ∉ F.row ∧ q ∉ F.column ∧ IsConj q t

/-- The source I is C_{N_G(A₂)}(t), as an ambient intersection. -/
abbrev involutionCentralizer (t : G) : Subgroup G :=
  threeSpaceNormalizer F ⊓ centralizer ({t} : Set G)

instance threeSpace_normal_in_involutionCentralizer (t : G) :
    (F.threeSpace.subgroupOf (involutionCentralizer F t)).Normal :=
  normal_subgroupOf_of_le_normalizer inf_le_left

abbrev involutionCentralizerQuotient (t : G) :=
  involutionCentralizer F t ⧸ F.threeSpace.subgroupOf (involutionCentralizer F t)

/-- I^∞ denotes the solvable residual, mapped through the actual inclusion. -/
@[expose] def involutionFour (t : G) : Subgroup G :=
  F.threeSpace ⊓ centralizer
    (((solvableResidual (involutionCentralizer F t)).map
      (involutionCentralizer F t).subtype) : Set G)

/-- The fixed subgroup used in 40.4(2) is elementary abelian before its
order-four assertion is known. -/
theorem involutionFour_elementary (t : G) : IsElementaryAbelian 2 (involutionFour F t) := by
  let := marked_rectangle_elementary F 3
  exact IsElementaryAbelian.of_injective (inclusion (show involutionFour F t ≤ F.threeSpace from inf_le_left))
    (inclusion_injective _)

/-- The denominator in I/A₂ is the whole A₂ whenever t lies in A₂. -/
theorem threeSpace_le_involutionCentralizer (t : G) (ht : t ∈ F.threeSpace) :
    F.threeSpace ≤ involutionCentralizer F t := by
  refine le_inf le_normalizer ?_
  intro a ha
  have hc : a ∈ centralizer (F.threeSpace : Set G) :=
    (threeSpace_centralizer_eq F).symm ▸ ha
  exact mem_centralizer_singleton_iff.mpr (hc t ht).symm

/-- The full local assertion of 40.4(2), on its literal centralizer and fixed
four-subgroup. This is a contract, not a proof that these data exist. -/
structure InvolutionCentralizerData (t : G) where
  quotient_equiv : Nonempty (involutionCentralizerQuotient F t ≃* Equiv.Perm (Fin 5))
  four_card : Nat.card (involutionFour F t) = 4
  cubic : Subgroup (threeSpaceNormalizer F)
  cubic_card : Nat.card cubic = 3
  cubic_extension_normal : (cubic ⊔ F.threeSpace.subgroupOf (threeSpaceNormalizer F)).Normal
  four_normalizer :
    (normalizer (involutionFour F t : Set G)).subgroupOf (threeSpaceNormalizer F) =
      (cubic ⊔ (involutionCentralizer F t).subgroupOf (threeSpaceNormalizer F))
  product :
    ((normalizer (involutionFour F t : Set G)).subgroupOf (threeSpaceNormalizer F) :
      Set (threeSpaceNormalizer F)) =
      (cubic : Set (threeSpaceNormalizer F)) *
        ((involutionCentralizer F t).subgroupOf (threeSpaceNormalizer F) :
          Set (threeSpaceNormalizer F))

/-- The corrected ambient-normalizer boundary, including the marked subgroups
required for the source coset geometry. Every field remains a producer obligation. -/
structure LocalData where
  orientation : MathieuFusionOrientation F
  row_moves_point : ∃ g : rowNormalizer F, (g : G) * z * (g : G)⁻¹ ≠ z
  column_normalizer : columnNormalizer F = centralizer ({z} : Set G)
  plane_equiv : Nonempty (planeQuotient F ≃*
    (((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) × Equiv.Perm (Fin 3)))
  cubicKernel : Subgroup (threeSpaceQuotient F)
  cubicKernel_normal : cubicKernel.Normal
  cubicKernel_card : Nat.card cubicKernel = 3
  cubicKernel_quotient : letI := cubicKernel_normal
    Nonempty ((threeSpaceQuotient F ⧸ cubicKernel) ≃* Equiv.Perm (Fin 6))
  row_plane_card : Nat.card ↥(F.row ⊓ F.plane) = 8
  row_threeSpace_card : Nat.card ↥(F.row ⊓ F.threeSpace) = 4
  planes_intersection_card : Nat.card ↥(F.plane ⊓ F.threeSpace) = 16
  row_plane_normalizer : rowNormalizer F ⊓ planeNormalizer F =
    rowNormalizer F ⊓ normalizer ((F.row ⊓ F.plane : Subgroup G) : Set G)
  row_threeSpace_normalizer : rowNormalizer F ⊓ threeSpaceNormalizer F =
    rowNormalizer F ⊓ normalizer ((F.row ⊓ F.threeSpace : Subgroup G) : Set G)
  involution_data : ∀ t ∈ F.plane ⊓ F.threeSpace,
    SecondInvolutionClass F t → Nonempty (InvolutionCentralizerData F t)

/-- The source boundary retains the original marking and its checked interchange. -/
structure SourceData where
  oriented : OrientedMarking F
  localData : LocalData oriented.marking

namespace LocalData
variable (D : LocalData F)
include D

/-- Movement of the marked point selects the full-action branch of source 39.3. -/
theorem row_normalizer_ne_centralizer : rowNormalizer F ≠ centralizer ({z} : Set G) := by
  intro he
  obtain ⟨g, hg⟩ := D.row_moves_point
  have hc := mem_centralizer_singleton_iff.mp
    (show (g : G) ∈ centralizer ({z} : Set G) by rw [← he]; exact g.property)
  apply hg
  rw [hc, mul_inv_cancel_right]

/-- The actual row quotient, with its natural four-dimensional action. -/
def rowEquiv : rowQuotient F ≃* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
  (MulEquiv.ofBijective (rowQuotientAction F) ⟨rowQuotientAction_injective F, by
    intro a
    obtain ⟨g, hg⟩ := row_action_surjective_of_normalizer_ne_centralizer F
      (D.row_normalizer_ne_centralizer F) a
    refine ⟨QuotientGroup.mk g, ?_⟩
    rw [← hg]
    ext x
    exact rowQuotientAction_mk_apply F g x⟩).trans (rowAutLinearEquiv F)

/-- The quotient isomorphism agrees with ambient conjugation under the marked
coordinates; thus it is the natural action, not an abstract group tag. -/
theorem rowEquiv_action (g : rowNormalizer F) (x : F.row) :
    rowEquiv F D (QuotientGroup.mk g) (rowCoordinates F x).toAdd =
      (rowCoordinates F (F.row.normalizerMonoidHom g x)).toAdd := by
  change rowAutLinearEquiv F (rowQuotientAction F (QuotientGroup.mk g))
    (rowCoordinates F x).toAdd = _
  rw [rowAutLinearEquiv_apply]
  congr 2
  apply Subtype.ext
  exact rowQuotientAction_mk_apply F g x

omit D in
/-- The literal row extension splits, using the checked source 39.3 theorem. -/
theorem row_splits [Finite G] :
    ∃ K : Subgroup (rowNormalizer F),
      (F.row.subgroupOf (rowNormalizer F)).IsComplement' K :=
  row_normalizer_splits F

end LocalData
end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
