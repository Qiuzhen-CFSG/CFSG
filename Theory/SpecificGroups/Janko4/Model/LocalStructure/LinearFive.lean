module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.HallActors
public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction
public import Theory.Mathieu.M24.LocalGeometry.Seed
public import Theory.Mathieu.M24.LocalGeometry.OctadOrder
public import Theory.Representation.MathieuCodeRestriction.M22.HexadGeometry
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry

/-!
# The native octad pullbacks in the J₄ Mathieu local subgroup

This leaf fixes the literal quotient and the literal octad geometry used by the
linear-five branch.  In particular, `Q` and `D` are actual subgroups of the
matrix model: they are the pullbacks of the pointwise and setwise stabilizers of
`standardOctad` through the proved Mathieu quotient, followed by the literal
embedding of `max1Subgroup` in `Model`.

`LinearFive.Construction` constructs the native elementary subgroup of order
`2^10` in these pullbacks, with its exact image, kernel intersection and full
ambient centralizer. The intrinsic `SL₅(2)` normalizer action and global
occurrence geometry require their additional native certificates.
-/

@[expose] public section

noncomputable section

open Subgroup
open scoped Pointwise
open Janko4 Janko4.Cardinality
open Janko4.LocalStructure
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode

namespace Janko4.LocalStructure.LinearFive

abbrev M : Subgroup Model := max1Subgroup matrixA_mul_self matrixB_pow_four
abbrev E : Subgroup Model :=
  Subgroup.map M.subtype (localKernel matrixA_mul_self matrixB_pow_four)

/-- The actual quotient map from the literal maximal subgroup to native M₂₄. -/
abbrev projection : M →* Sporadic.Mathieu.M24 := MathieuHallActors.projection

/-- The fixed native octad used for the local pullbacks. -/
abbrev O : Octad := standardOctad

/-- The pointwise octad kernel in native M₂₄. -/
abbrev A : Subgroup Sporadic.Mathieu.M24 := octadPointwiseKernel O

/-- The actual preimage of the pointwise octad kernel, embedded in `Model`. -/
def Q : Subgroup Model := (A.comap projection).map M.subtype

/-- The actual preimage of the setwise octad stabilizer, embedded in `Model`. -/
def D : Subgroup Model :=
  ((octadStabilizer O).comap projection).map M.subtype

theorem pointwise_le_stabilizer : A ≤ octadStabilizer O := by
  unfold A MathieuCode.octadPointwiseKernel
  exact map_subtype_le _

theorem Q_le_D : Q ≤ D := by
  unfold Q D
  exact map_mono (comap_mono pointwise_le_stabilizer)

theorem Q_le_M : Q ≤ M := by
  unfold Q
  exact map_subtype_le _

theorem D_le_M : D ≤ M := by
  unfold D
  exact map_subtype_le _

theorem projection_preimage_A :
    (A.comap projection).map projection = A := by
  exact map_comap_eq_self_of_surjective MathieuHallActors.projection_surjective A

theorem projection_preimage_stabilizer :
    ((octadStabilizer O).comap projection).map projection = octadStabilizer O := by
  exact map_comap_eq_self_of_surjective MathieuHallActors.projection_surjective _

theorem A_elementary : IsElementaryAbelian 2 A :=
  MathieuCode.octad_pointwiseKernel_elementary O

theorem A_card : Nat.card A = 16 := by
  unfold A
  rw [← MathieuCode.octad_core_map_eq_pointwise O]
  rw [Subgroup.card_map_of_injective (octadStabilizer O).subtype_injective]
  exact Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction.core_card O

theorem Q_contains_E : E ≤ Q := by
  unfold Q
  apply map_mono
  intro x hx
  have hker : projection.ker = localKernel matrixA_mul_self matrixB_pow_four :=
    MathieuHallActors.projection_ker
  change projection x ∈ A
  have hxk : x ∈ projection.ker := hker ▸ hx
  rw [MonoidHom.mem_ker] at hxk
  rw [hxk]
  exact one_mem A

end Janko4.LocalStructure.LinearFive

end
