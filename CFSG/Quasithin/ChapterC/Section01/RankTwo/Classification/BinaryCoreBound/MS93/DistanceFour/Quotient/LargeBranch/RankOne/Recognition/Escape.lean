module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Frame

/-!
# Assembly of second-star escape from its two remaining source arguments

The incident frame is constructed by Escape.Frame. Under contrary
containment of the second starred preimage, the first explicit premise
constructs the moved seed for the second ordered residual. Applying the
proved conjugate-seed recognition places this moved space in the actual
midpoint orbit span and supplies its marked dual quotient.

The second explicit premise is the remaining moving-neighbor argument:
from these outputs and the contrary containment, it puts the entire radius
subgroup in the midpoint kernel. The checked midpoint escape contradicts
that conclusion. Both premises still require proofs; this conditional
assembly is not the unconditional source clause (4).

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(4), printed p.911, using (1)--(3) on pp.910--911.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Construct the compatible frame and reduce its escape to moved-seed
construction and the subsequent radius-containment contradiction. These two
explicit source arguments remain to be discharged by the escape assembly. -/
theorem second_star_escape_of_moved_seed_and_radius_bound
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R)))
    (hseed : ∀ (f : Seed.Frame source), Seed.Compatible f s →
      d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle →
      ∃ x : Seed.Input (geometry := geometry) d f s.middle,
        x.space = Seed.movedSpace d.representation ((f.residual true).map source.projection)
          (Seed.secondTildeStar (geometry := geometry) d f 1))
    (hclosure : ∀ (f : Seed.Frame source), Seed.Compatible f s →
      d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle →
      orbitSpan s.middle ≤ Q R s.middle →
      Nonempty (SpanQuotient source common s.middle) →
      Seed.movedSpace d.representation ((f.residual true).map source.projection)
        (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ d.subspace (orbitSpan s.middle) →
      V R (alpha R) ≤ Q R s.middle) :
    ∃ f : Seed.Frame source, Seed.Compatible f s ∧
      ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle := by
  obtain ⟨f, hf⟩ := exists_compatible_frame common radius hb s hbc
  refine ⟨f, hf, ?_⟩
  intro hcontained
  obtain ⟨x, hx⟩ := hseed f hf hcontained
  obtain ⟨hspace, hspan, hquot⟩ :=
    Seed.conjugate_seed_recognition common radius hb s hs hbc d f hf x
  have hmoved : Seed.movedSpace d.representation ((f.residual true).map source.projection)
      (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ d.subspace (orbitSpan s.middle) := by
    rw [← hx, hspace]
    exact d.subspace_mono (conjugateSpanBy_le (Z_le_orbitSpan s.middle)
      ((f.ambient_le true).trans (orbitSpan_normalized s.middle)))
  exact midpoint_escape source common hb s (hclosure f hf hcontained hspan hquot hmoved)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
