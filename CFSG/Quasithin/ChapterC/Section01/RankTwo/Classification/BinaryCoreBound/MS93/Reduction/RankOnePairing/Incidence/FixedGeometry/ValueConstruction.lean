module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.Values
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.RelativeClosure

/-!
# Transport of the marked value geometry

The finite matrix calculation supplies the small invariant seed line, its
incident plane, and two matrix actors giving three distinct lines. The natural
coordinates transport these to the extension, and surjectivity of the actual
local normalizer image lifts both actors. Relative normalization of the plane
extends the seed commutator bound to the neighboring local normal closure.

`of_fixed` constructs all six value-space conclusions from `SourceData`,
`LocalFacts`, and the nonzero local residual fixed space. Faithful coordinates
turn this last hypothesis into a nonzero marked parabolic fixed space, selecting
the point member of the incident pair in the matrix calculation.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(i), printed p.847.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open Subgroup
universe u
variable {M : Type u} [Group M] [Finite M]
    {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M}
    [Z.Normal] [W.Normal]

/-- Transport of the concrete matrix geometry to the actual local normalizers. -/
theorem of_modelGeometry (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (g : ModelGeometry d.natural.marking e.flag i) : ValueGeometry e i Z W X := by
  let n := d.natural
  have hcoord (j : Bool) : coordinateImage n (localFixed e Z j) =
      modelValues n.marking e.flag j :=
    coordinateImage_localFixed n f.component_image f j
  have hseed : ⁅X, W⁆ ≤ localFixed e Z i := by
    apply (coordinateImage_le_iff n d.commutator_le).mp
    rw [hcoord]
    apply g.small_invariant
    · rw [card_coordinateImage n d.commutator_le]
      exact d.commutator_card_le
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := ha
      rw [← f.parabolic_image i] at hq
      obtain ⟨m, hm, rfl⟩ := hq
      change (coordinateImage n ⁅X, W⁆).map
        (vectorAction (n.marking (e.projection m))).toMonoidHom = coordinateImage n ⁅X, W⁆
      rw [← coordinateImage_conjugate n f.component_image _ d.commutator_le m]
      have he : conjugate m ⁅X, W⁆ = ⁅X, W⁆ :=
        mem_normalizer_iff_map_conj_eq.mp (seed_commutator_normalized d f hm)
      rw [he]
  have hinc : localFixed e Z i ≤ localFixed e Z (!i) := by
    apply (coordinateImage_le_iff n (A := localFixed e Z i) inf_le_left).mp
    rw [hcoord, hcoord]
    exact g.incident
  refine
    { seed_bound := hseed
      local_bound := ?_
      local_proper := ?_
      seed_fixed := ?_
      seed_card := ?_
      value_neighbors := ?_ }
  · exact localGenerated_commutator_bound_of_normalizes
      (generated X) W Z (localParabolic e (!i)) X (localFixed e Z (!i))
      d.generated_commutator (f.z_central_generated d) le_normalClosure
      (hseed.trans hinc) (localFixed_normalized e Z (!i))
  · intro h
    have hm := (coordinateImage_le_iff n (A := Z) le_rfl).mpr h
    rw [coordinateImage_self, hcoord] at hm
    exact g.other_proper (top_unique hm)
  · have hm : coordinateImage n (localFixed e Z i) ≤
        coordinateImage n (Z ⊓ centralizer (localResidual (localParabolic e i) : Set M)) := by
      rw [hcoord, coordinateImage_centralizer n f.component_image, f.residual_image]
      exact g.seed_fixed
    exact ((coordinateImage_le_iff n (A := localFixed e Z i) inf_le_left).mp hm).trans inf_le_right
  · rw [← card_coordinateImage n (A := localFixed e Z i) inf_le_left, hcoord]
    exact g.seed_card
  · obtain ⟨a, b, ha, hb, hia, hib, hab⟩ := g.neighbors
    obtain ⟨qa, hqa, rfl⟩ := ha
    obtain ⟨qb, hqb, rfl⟩ := hb
    rw [← f.parabolic_image (!i)] at hqa hqb
    obtain ⟨ma, hma, rfl⟩ := hqa
    obtain ⟨mb, hmb, rfl⟩ := hqb
    refine ⟨ma, mb, hma, hmb, ?_, ?_, ?_⟩
    · apply (coordinateImage_eq_bot_iff n
        (A := localFixed e Z i ⊓ conjugate ma (localFixed e Z i))
        (inf_le_left.trans inf_le_left)).mp
      rw [coordinateImage_inf,
        coordinateImage_conjugate n f.component_image (localFixed e Z i) inf_le_left ma, hcoord]
      exact hia
    · apply (coordinateImage_eq_bot_iff n
        (A := localFixed e Z i ⊓ conjugate mb (localFixed e Z i))
        (inf_le_left.trans inf_le_left)).mp
      rw [coordinateImage_inf,
        coordinateImage_conjugate n f.component_image (localFixed e Z i) inf_le_left mb, hcoord]
      exact hib
    · apply (coordinateImage_eq_bot_iff n
        (A := conjugate ma (localFixed e Z i) ⊓ conjugate mb (localFixed e Z i))
        (inf_le_left.trans (conjugate_le_normal _ Z inf_le_left ma))).mp
      rw [coordinateImage_inf,
        coordinateImage_conjugate n f.component_image (localFixed e Z i) inf_le_left ma,
        coordinateImage_conjugate n f.component_image (localFixed e Z i) inf_le_left mb, hcoord]
      exact hab

/-- The fixed-case value spaces and three-line orbit, with precisely the source
data, local-structure facts, and nonzero residual fixed-space hypothesis. -/
theorem of_fixed (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥) :
    ValueGeometry e i Z W X :=
  of_modelGeometry d f (modelGeometry_of_fixed d.natural.marking e.flag i
    (model_fixed_ne_bot d.natural f.component_image f i h))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
