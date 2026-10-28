module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.FlagGeometry

/-!
# The ordinary A₆ source flag

A marking of L/O₂(L) over the prescribed six-letter quotient equips the
actual V with the natural action. The original V₁,V₂,V₃ are exactly the
preimages of the one-, two- and three-dimensional Sylow-stable subspaces.
This supplies the ordinary local core setup used by 13.8.5.

Source: Aschbacher–Smith, Notation 13.2.1, printed p.877.
-/

public section

open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)

/-- The compatible ordinary local setup on the literal source flag. -/
theorem local_ordinary_flag_model
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (he : ∀ l : L, e (QuotientGroup.mk' (pCore 2 L) l) =
      d.local_quotient (QuotientGroup.mk' (centralCore L) l)) :
    Nonempty (TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃) := by
  let P := local_flag_image d V₁
  let W := local_flag_image d V₂
  let U := local_flag_image d V₃
  refine ⟨{
    model := e
    normalizes_L := d.normalizes_L
    normalizes_V := d.normalizes_V
    coordinate := d.coordinate
    conjugation := ?_
    point := P
    plane := W
    hyperplane := U
    point_dim := ?_
    plane_dim := ?_
    hyperplane_dim := ?_
    point_le_plane := local_flag_image_mono d V₁ V₂ d.line_le_plane
    plane_le_hyperplane := local_flag_image_mono d V₂ V₃ d.plane_le_seed
    line_eq := ?_
    plane_eq := ?_
    seed_eq := ?_
    line_stable := d.line_stable
    plane_stable := d.plane_stable
    seed_stable := d.seed_stable }⟩
  · intro l v
    rw [he]
    exact d.conjugation l v
  · exact local_flag_image_dim d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 (by simpa using d.line_card)
  · exact local_flag_image_dim d V₂ (d.plane_le_seed.trans d.seed_le) 2
      (by simpa using d.plane_card)
  · exact local_flag_image_dim d V₃ d.seed_le 3 (by simpa using d.seed_card)
  · exact local_flag_preimage_simple d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
  · exact local_flag_preimage_simple d V₂ (d.plane_le_seed.trans d.seed_le)
  · exact local_flag_preimage_simple d V₃ d.seed_le

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
