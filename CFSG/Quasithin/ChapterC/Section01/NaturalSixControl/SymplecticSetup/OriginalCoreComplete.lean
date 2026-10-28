module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CoreComplete
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Assembly

/-!
# Core reconstruction on the original natural-six pair

In the full Thompson-image branch the original Baumann subgroup already has
the full marked point-core image. The native symplectic core theorem therefore
applies to the original component--Baumann product. Pulling back through that
single inclusion identifies the intrinsic component core with the specified
natural module and gives the alternating block. Combining this with the
established small-image and characteristic-normal branches proves the original
characteristic-or-block alternative without a characteristic replacement.

Source: Aschbacher--Smith C.1.37, printed pp.141--143, using MS93 (3.6) and
(5.12), printed pp.870--871 and 924--927. The original natural module, marked
action and full Baumann subgroup are retained throughout.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T) (hm : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J
include d hm

/-- The full original Baumann image in the unchanged natural coordinates. -/
theorem originalSource_full_point_image
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    (R).map (originalSource d hm).projection =
      Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
  apply (map_injective (f := (MulAut.conj d.relabeler.val).toMonoidHom)
    (MulAut.conj d.relabeler.val).injective)
  rw [originalSource_projection, ← map_map,
    map_subgroupOf_eq_of_le (show d.B ≤ J from le_sup_right), map_map]
  change d.B.map d.q0 = _
  rw [d.baumann_image_eq_full hne, map_map]
  have he : (MulAut.conj d.relabeler.val).toMonoidHom.comp
      (MulAut.conj d.relabeler.val⁻¹).toMonoidHom = MonoidHom.id Model.S := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

/-- The original symplectic graph reconstructs the whole core directly. -/
theorem originalSource_core_eq_U
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    core R (alpha R) = U R (alpha R) :=
  (originalSource d hm).core_eq_U (d.sqtk.subgroup J) d.relabeler.val⁻¹
    (originalSource_full_point_image d hm hne)

/-- The original component commutator core is precisely the given module. -/
theorem original_core_image_eq
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    (blockU L).map L.subtype = V :=
  core_image_eq_of_original_core_eq_U d hm (originalSource_core_eq_U d hm hne)

/-- All original whole-core structural clauses follow with no replacement. -/
theorem original_coreReconstruction
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    CoreReconstruction L :=
  d.coreReconstruction_of_core_image_eq (original_core_image_eq d hm hne)

/-- The original full-image MS pair gives its alternating-six block. -/
theorem originalSource_alternatingBlock
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    IsAlternatingBlock L 6 :=
  (d.intrinsic_ms_block_of_coreReconstruction hm
    (original_coreReconstruction d hm hne)).2

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : SourceData L V T)

/-- The original natural-six C.1.37 alternative, with its MS core premise
discharged on the actual full Baumann subgroup. -/
theorem characteristic_or_block_source :
    (∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) ∨ IsAlternatingBlock L 6 := by
  by_cases hs : (elementaryAbelianMaxJ d.R).map d.q0 ≤ last
  · exact d.characteristic_or_block_of_small_thompson_image hs
  by_cases hc : ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal
  · exact Or.inl hc
  exact Or.inr (SymplecticSetup.SourceData.originalSource_alternatingBlock d
    (d.intrinsicMSPair_of_full_image hs hc) hs)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SourceData
