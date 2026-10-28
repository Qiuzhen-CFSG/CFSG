module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Requirements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Shift
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Second.Generation

/-!
# Conditional assembly of the second geometric factor

The published critical-shift argument supplies a segment with midpoint rho.
Once its large-intersection condition is proved, the uniform FirstStep
constructs a second factor with the original natural marking and exact
U_alpha kernel. The subgroup-index calculation then proves the literal
identity V_alpha^* = orbitSpan c sup orbitSpan rho.

The shifted large-intersection condition remains an explicit premise of
`secondStep_of_shifted_nonSmall`. This lemma does not construct SecondStep
from the source hypotheses alone: its source assembly must discharge that
premise. In particular, escape from Q_alpha alone is not used as a proof
of that condition.

Source: original Meierfrankenfeld--Stellmacher (1993), final paragraph of
(4.6.12), printed p.912, with (1)--(5) on pp.910--912.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- The remaining source obligation is the large-intersection condition at
rho. This conditional assembly retains that obligation explicitly. -/
theorem secondStep_of_shifted_nonSmall (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4)
    (hnonSmall : FirstStep source common →
      ∀ (s : CriticalSegment geometry), ¬ s.SmallIntersection →
        ∀ (_f : FirstFactor source common s.middle) (rho : Vertex R),
          nu R geometry (alpha R) rho → Adjacent R (beta R) rho →
          ⁅Z R rho, orbitSpan s.middle⁆ ≠ ⊥ →
          ¬ ⁅V R (alpha R) ⊓ Q R rho, V R rho⁆ ≤ Z R (alpha R)) :
    SecondStep source common := by
  intro first s hs f rho hrho hadj hne
  obtain ⟨t, ht⟩ := criticalSegment_through_of_noncommuting source common hb
    s.middle rho ((cosetGraph R).dist_comm.trans s.first_distance)
    ((cosetGraph R).dist_comm.trans hrho.1) hne
  have htnot : ¬ t.SmallIntersection := by
    simpa only [CriticalSegment.SmallIntersection, ht] using
      hnonSmall first s hs f rho hrho hadj hne
  obtain ⟨hg, _⟩ := first t htnot
  have hg' : Nonempty (FirstFactor source common rho) := ht ▸ hg
  obtain ⟨g⟩ := hg'
  exact ⟨⟨g⟩, f.star_generation radius g hne (first s hs).2⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
