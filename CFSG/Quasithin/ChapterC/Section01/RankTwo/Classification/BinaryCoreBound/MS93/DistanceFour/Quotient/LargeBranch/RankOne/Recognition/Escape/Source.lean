module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.SeedConstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Pointwise

/-!
# Source second-star escape

The printed orbit-span displacement bound controls each involution on the
literal radius quotient. The two natural sections give a cubic whose fixed
kernel lies in Y, with codimension at least four. Saturation of the two
involution displacement ranks then makes Y fixed by the full first actor.
The proved edge-star and radius propagation gives the source contradiction.

The final theorem constructs the moved seed under contrary containment and
applies its conjugate-span recognition, discharging every input to that
contradiction. It needs no bound on the whole radius commutator with a neighbor.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(4), printed p.911, using clauses (1)--(3).
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The source orbit-span containment supplies full first-actor fixation
of Y through pointwise involution displacement and the two natural sections. -/
theorem fixedPreimage_le_first_actor_fixed_of_span_contained
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (hf : Seed.Compatible f s)
    (hspan : orbitSpan s.middle ≤ Q R s.middle) :
    d.subspace (Sections.fixedPreimage s.middle) ≤
      fixedSpace d.representation ((f.actor false).map source.projection) := by
  obtain ⟨c, hc, ho, _, hker, hcodim⟩ :=
    exists_first_cubic_displacement_and_fixed_kernel common radius hb s hs hbc d f hf
  rw [f.actor_eq false]
  exact ParabolicLinear.frame_fixedPreimage_of_pointwise_displacement d.representation
    f false (d.subspace (Sections.fixedPreimage s.middle))
    (fixedPreimage_le_first_core_fixed common s d f hf)
    (involution_displacement_rank_le_two_of_span_contained common radius hb s hbc hspan d)
    c hc ho hker hcodim

/-- The source radius-containment deduction under contrary second-star
containment, with all neighbor and fixed-space inputs discharged. -/
theorem radius_le_midpoint_of_contained_star
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (hf : Seed.Compatible f s)
    (hcontained : d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hspan : orbitSpan s.middle ≤ Q R s.middle)
    (hmoved : Seed.movedSpace d.representation ((f.residual true).map source.projection)
      (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ d.subspace (orbitSpan s.middle)) :
    V R (alpha R) ≤ Q R s.middle :=
  radius_le_midpoint_of_Y_fixed common radius hb s hbc d f hf hcontained hspan hmoved
    (fixedPreimage_le_first_actor_fixed_of_span_contained common radius hb s hs hbc d f hf hspan)

/-- Clause (4): the original second starred preimage escapes Q_c for an
actual compatible frame, with no seed or radius-containment premise remaining. -/
theorem source_second_star_escape
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R))) :
    ∃ f : Seed.Frame source, Seed.Compatible f s ∧
      ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle := by
  exact second_star_escape_of_moved_seed_and_radius_bound common radius hb s hs hbc d
    (fun f hf hcontained =>
      exists_moved_seed_of_containment common radius hb s hs hbc d f hf hcontained)
    (fun f hf hcontained hspan _hquot hmoved =>
      radius_le_midpoint_of_contained_star common radius hb s hs hbc d f hf
        hcontained hspan hmoved)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
