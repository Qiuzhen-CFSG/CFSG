module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Linear
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple

/-!
# The local seed plane and its fixed midpoint line

The edge index and large-intersection hypothesis make the actual midpoint
image a line. The geometric displacement calculation identifies the midpoint
actor with the first intrinsic core. The parabolic plane theorem then proves
that the seed is a plane, its midpoint commutator fills that line, and the
second parabolic's conjugates of the line span the seed.

The line lies in the seed, so the second core fixes it. Together with the
first ordered residual's fixation and the binary full-actor generation
identity, this gives fixation by the first full actor. Literal quotient
transport supplies the ambient conjugate-span and commutator equalities.

The conditional assembly keeps the earlier (4.6.8) FlagControl explicit.
The final constructor `localConsequences` discharges it by the proved marked
flag theorem, using the early facts already supplied by RadiusFacts. Thus
all five conclusions follow from the source, geometry, radius facts and
compatible seed, with no additional local recognition premise.

Source: Meierfrankenfeld--Stellmacher (1993), notation on printed p.905
and the first paragraph after (4.6.12)(3), printed p.910.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- All five local seed conclusions, conditional only on the supplied source
inputs and the earlier marked flag theorem (4.6.8). -/
theorem localConsequences_of_flagControl
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Frame source) (hf : Compatible f s)
    (x : Input (geometry := geometry) d f s.middle)
    (control : Flags.RankOne.FlagControl source) : LocalConsequences d f s.middle x := by
  have hactor := midpointActor_eq_first_core common radius hb s hbc f hf control
  have hline := midpoint_line_dimension d radius s hs hbc
  have hbound := x.midpoint_moved_le_line common radius s hbc
  rw [hactor] at hbound
  obtain ⟨hdim, hmoved, horbit⟩ := parabolic_plane_of_line_bound f d.representation
    x.space (d.subspace (Z R s.middle)) x.normalized x.le_second_core_fixed
    x.nonzero x.moved hline hbound
  have hline_seed : d.subspace (Z R s.middle) ≤ x.space := by
    rw [← horbit]
    intro v hv
    exact Submodule.subset_span ⟨1, Subgroup.one_mem _, v, hv, by simp⟩
  have hres := midpoint_line_le_residual_fixed common radius s hbc d f hf control
  have hfixed : d.subspace (Z R s.middle) ≤
      fixedSpace d.representation ((f.actor false).map source.projection) := by
    intro v hv g
    let H : Subgroup SL := {
      carrier := {a | d.representation a v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change d.representation (a * b) v = v
        change d.representation a v = v at ha
        change d.representation b v = v at hb
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        change d.representation a⁻¹ v = v
        change d.representation a v = v at ha
        simpa only [d.representation.inv_self_apply] using
          (congrArg (d.representation a⁻¹) ha).symm }
    have hR : (f.residual false).map source.projection ≤ H := by
      intro a ha
      exact hres hv ⟨a, ha⟩
    have hK : (f.core true).map source.projection ≤ H := by
      intro a ha
      exact x.le_second_core_fixed (hline_seed hv) ⟨a, ha⟩
    exact (sup_le hR hK) ((actor_image_generation f) ▸ g.property)
  refine ⟨?_, hdim, hline, hfixed, ?_⟩
  · change x.space = d.subspace (conjugateSpanBy (Z R s.middle)
      ((f.parabolic true).map (embedM R)))
    rw [d.subspace_conjugateSpan _ (midpoint_Z_le_radius s) _
      ((f.ambient_le true).trans (DistanceEight.V_normalized R (alpha R)))]
    exact horbit.symm
  · rw [x.midpoint_commutator_image common s hbc, hactor, hmoved]

/-- The local seed plane and its fixed midpoint line in MS93 (4.6.12)(3),
from the source inputs and compatible seed. The earlier marked flag theorem
is supplied by (4.6.8), using the early facts contained in `radius`. -/
theorem localConsequences
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Frame source) (hf : Compatible f s)
    (x : Input (geometry := geometry) d f s.middle) : LocalConsequences d f s.middle x :=
  localConsequences_of_flagControl common radius hb s hs hbc d f hf x
    (Flags.RankOne.flagControl source geometry common hb radius.toEarlyFacts)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
