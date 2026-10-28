module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Algebra

/-!
# Assembly of the preliminary D estimates on the supplied source path

The natural decomposition gives both commutator bounds by the edge identity
and local generation. The two independent kernel containments then complete
every forward and reflected configuration requested by PreliminaryEstimatesOnPath.
Both source producers remain explicit: this module does not assert the
unconditional preliminary estimates or the final hat identity.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.897.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- All four indexed configurations, with both source calculations explicit.
Final assembly must construct the two records from the earlier hypotheses. -/
theorem estimatesOnPath_of_calculations [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a)
    (split : DecompositionsOnPath R p) (kernels : KernelContainmentsOnPath R p) :
    PreliminaryEstimatesOnPath R p := by
  constructor
  · intro i hi hi4 hi6 hne
    have hb : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
    have hmove : p.walk.getVert i ∈
        Escape.movingNeighbors geometry (p.walk.getVert (i - 2)) := by
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
        (p.moving_neighbors source common earlier hb (by omega) (by omega)).2
    have seed : SeedEstimates R (p.walk.getVert i) (p.walk.getVert (i - 2))
        (p.walk.getVert (i - 1)) := by
      apply seedEstimates_of_product common earlier
        (p.even_color hi (by omega)) (p.even_color hb (by omega))
        _ _ hmove (split.forward i hi hi4 hi6 hne)
      · exact adjacent_symm R (by
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
            p.adjacent (i := i - 1) (by omega))
      · simpa only [show i - 2 + 1 = i - 1 by omega] using
          p.adjacent (i := i - 2) (by omega)
    have hk := kernels.forward i hi hi4 hi6 hne seed
    exact ⟨seed.decomposition_product, seed.seed_commutator, seed.span_commutator, hk.1, hk.2⟩
  · intro i hi hi8 hi10 hne
    have hb : Even (i + 2) := hi.add (by decide)
    have hmove : p.walk.getVert i ∈
        Escape.movingNeighbors geometry (p.walk.getVert (i + 2)) := by
      simpa only [Nat.add_sub_cancel] using
        (p.moving_neighbors source common earlier hb (by omega) (by omega)).1
    have seed : SeedEstimates R (p.walk.getVert i) (p.walk.getVert (i + 2))
        (p.walk.getVert (i + 1)) := by
      apply seedEstimates_of_product common earlier
        (p.even_color hi (by omega)) (p.even_color hb (by omega))
        (p.adjacent (by omega)) _ hmove (split.backward i hi hi8 hi10 hne)
      exact adjacent_symm R (by
        simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega))
    have hk := kernels.backward i hi hi8 hi10 hne seed
    exact ⟨seed.decomposition_product, seed.seed_commutator, seed.span_commutator, hk.1, hk.2⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary
