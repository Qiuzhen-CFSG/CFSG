module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Modules
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation

/-!
# Conditional conjugate-seed recognition

The finite incident frame uses actual parabolic preimages, intrinsic cores,
and distinct full and ordered-residual actors. Starred layers are defined
from the actual edgeStar and its adjacent core-fixed quotient subspaces.
The local seed theorem identifies the second-parabolic conjugate span of
the midpoint line. Full-parabolic factorization then propagates the seed
to the whole local orbit span inside Q_c. The resulting cyclic vector is
aligned with the dual twist of common.natural.marking; checked cyclic
recognition produces SpanQuotient with its exact kernel and ambient action.

This assembles all three conclusions of Meierfrankenfeld--Stellmacher,
Pushing up weak BN-pairs of rank two (1993), (4.6.12)(3), printed
pp.910--911, with the incident-frame conventions of p.905. Propagation uses
M = P₁ P₂ P₁ in place of the printed base-core generation formula: with
the literal incident cores, that formula remains in a proper parabolic,
as proved in Seed.Propagation.Actors. The full-span and marked quotient
conclusions are unchanged.

Only the source inputs, compatible incident frame and seed remain as
hypotheses. LocalConsequences and MarkedCyclicSeed are constructed in the
proof. The parent Recognition owner retains the frame-selection and seed
construction obligations, clauses (4)--(5), and the starred index 64.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- MS93 (4.6.12)(3), conditional on precisely the compatible incident frame
and its source seed. The quotient is by the actual relative Z_alpha subgroup,
and its conjugation equation uses the dual of `common.natural.marking`.
The radius realization `d` is supplied by `exists_radiusModule`; it contains
no recognition hypothesis. -/
theorem conjugate_seed_recognition
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Frame source) (hf : Compatible f s)
    (x : Input (geometry := geometry) d f s.middle) :
    x.space = d.subspace (conjugateSpanBy (Z R s.middle) (f.ambient true)) ∧
      orbitSpan s.middle ≤ Q R s.middle ∧
      Nonempty (SpanQuotient source common s.middle) := by
  have hlocal := localConsequences common radius hb s hs hbc d f hf x
  obtain ⟨hQ, dO, ⟨v⟩⟩ := propagation_of_local common radius hb s hs hbc d f hf x hlocal
  exact ⟨hlocal.conjugate_span, hQ, v.quotient⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
