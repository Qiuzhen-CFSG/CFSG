module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.Coordinates
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.Placement
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.AmbientNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.RootMarking

/-!
# Five-local pair constructions for the source J₂ graph

The genuine earlier-source geometry and five-local generation clause put
X in an actual five-local A₅ component. Inside it, two actual conjugates
of X have A₄ and A₅ joins, and the latter's intrinsic common normalizer
is explicitly C₂. `ComponentCoordinates.fiveFixerEquiv` computes the
full ambient fixer from compatible normalizer coordinates.

The two-central five-normalizer and separation conclusions of 47.2
identify the component's full ambient normalizer and the A₄ join's literal
two-core as a conjugate of the 47.1 root. Weak closure of the source cubic
line from 47.3 then aligns the join with the first root-normalizer factor;
the second is the actual component layer and meets the class of z.
`fiveLocalPairs_nonempty` assembles these constructions into `FiveLocalPairs`,
discharging both the component-coordinate and root-coordinate obligations.

Only the genuine earlier-source outputs remain explicit: `SelectedGeometry`
from `qt-i47-j2-source-involutions`, the two five-families from
`qt-i47-j2-five-local-calculation`, and `SylowThreeStructure` from
`qt-i47-j2-three-local-calculation`. The source assembly owner
`qt-i47-j2-pair-representatives` supplies these and the independent SL₂(3)
pair to `FiveLocalPairs.representatives` and `FiveLocalPairs.fourSuborbits`.
No pair, fixer, orbit or coverage conclusion of 47.5 is assumed here.

Source: Aschbacher, *Sporadic Groups* (1994), 47.5, printed p.263.
-/

@[expose] public section
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal
open EarlierFive PrimeNormalizers.FiveLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- Source placement followed by the actual internal construction. The
five-subgroup and its marked 47.2 witness are retained for the remaining
root and full-normalizer calculations. -/
theorem exists_source_internalPairs (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) :
    ∃ P : PlacedComponent D S.t, Nonempty (InternalPairs D (fiveComponent P.F)) := by
  obtain ⟨P⟩ := placedComponent_nonempty S hA
  exact ⟨P, internalPairs_nonempty D (fiveComponent P.F)
    (componentEquiv P.witness) P.X_le⟩

/-- The first two constructions on printed p.263, from only the genuine
47.1–47.3 outputs. Placement supplies the actual five-component, the internal
construction supplies two of its conjugates of X, and the normalizer and
root calculations supply their marked ambient fixers. -/
theorem fiveLocalPairs_nonempty (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) (hB : TwoCentralFiveFamily D S.t)
    (hSyl : ∀ Q : Sylow 3 G,
      Nonempty (PrimeNormalizers.ThreeLocal.SylowThreeStructure D Q)) :
    Nonempty (FiveLocalPairs D) := by
  obtain ⟨P⟩ := placedComponent_nonempty S hA
  obtain ⟨I, ⟨R⟩⟩ := internalPairs_with_root S P hB hSyl
  exact ⟨(P.coordinates hB).pairs I R⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal
