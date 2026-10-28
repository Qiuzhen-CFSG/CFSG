module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Geometry.Parabolics
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Geometry.Displacement

/-!
# The midpoint actor and the first residual on the local seed line

The actual midpoint actor is contained in the first intrinsic core and has
the same order four, hence equals that core image. Equal intrinsic first
cores align the supplied seed frame with the flag selected by FlagControl.
The earlier residual commutator bound therefore applies to this frame;
through the original LayerModule projection it fixes the midpoint layer.

Together with actor_image_generation, these are the three conditional
geometric inputs to the parent's local plane calculation. No seed, large
intersection, or module-recognition assumption is needed here. FlagControl
remains an explicit premise to be discharged by the source assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation on p.905, (4.6.9) on p.908 and (4.6.12)(3) on p.910.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The actual midpoint radius image exhausts the first intrinsic core. -/
theorem midpointActor_eq_first_core
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) (f : Frame source) (hf : Compatible f s)
    (control : Flags.RankOne.FlagControl source) :
    midpointActor (source := source) s.middle = (f.core false).map source.projection := by
  apply eq_of_le_of_card_ge (midpointActor_le_first_core common s hbc f hf)
  rw [f.core_image_card, midpoint_actor_card common radius hb s hbc control]

/-- The first ordered residual fixes the midpoint layer in the given radius quotient. -/
theorem midpoint_line_le_residual_fixed
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Frame source) (hf : Compatible f s)
    (control : Flags.RankOne.FlagControl source) :
    d.subspace (Z R s.middle) ≤
      fixedSpace d.representation ((f.residual false).map source.projection) := by
  obtain ⟨i, hi, ht⟩ := control
  let k : Sections.Frame source := ⟨i, hi, ht⟩
  have hc := Sections.residual_commutator_le_Z common radius k hbc
  change ⁅Z R s.middle, Flags.RankOne.flagResidual source i⁆ ≤ Z R (alpha R) at hc
  rw [← f.first_residual_eq_flag s hf i hi, commutator_comm] at hc
  intro v hv g
  obtain ⟨t, ht, rfl⟩ := (d.mem_subspace_iff _ v).mp hv
  obtain ⟨m, hm, he⟩ := g.property
  change d.representation (g : SL) (d.projection t).toAdd = (d.projection t).toAdd
  rw [← he]
  apply (d.fixed_iff_commutator_mem m ?_ t).mpr
  · exact hc (commutator_mem_commutator (mem_map_of_mem _ hm) ht)
  · apply DistanceEight.V_normalized R (alpha R)
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
