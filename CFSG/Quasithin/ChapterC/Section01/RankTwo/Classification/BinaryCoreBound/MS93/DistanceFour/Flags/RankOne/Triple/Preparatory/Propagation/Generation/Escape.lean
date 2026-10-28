module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Geometry

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.Trapping
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.Recognition

/-!
# Escape from the midpoint span

The geometric argument reduces a trapped transported span to a nontrivial
binary SL3(2) quotient action with one displacement subgroup of order at
most two. Small-displacement recognition makes the entire marked
section split natural, contradicting the given failure of SingleSection.
Selection from the actual conjugate span then produces one amalgam
element transporting both entries of the ordered pair.

The conditional assembly is retained, and `escapingTransport` discharges
its representation premise. The escape step uses only the common and early
facts, the critical configuration and membership in nu(alpha); the seed
commutator bound and naturality are needed elsewhere in claim (2).

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (2), p.906.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- Once the independent small-displacement recognition is supplied, a single
amalgam element transports the ordered pair to an escaping generator.
This conditional assembly does not assert the representation theorem. -/
theorem escapingTransport_of_recognition [Finite M]
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i) (hs : ¬ SingleSection p)
    (t : Vertex R) (ht : nu R geometry (alpha R) t)
    (recognize : ∀ H N : Subgroup M, SmallDisplacementData source.projection H N →
      Nonempty (Escape.SingleNaturalSection source.projection source.projection.ker
        (pResidual 2 M) H N)) :
    ∃ g : FreeAmalgam R, act R g (alpha R) = t ∧
      ¬ Z R (act R g p.middle) ≤ Q R (alpha R) := by
  obtain ⟨g, hg⟩ := exists_base_transport t ht
  apply escapingTransport_of_span p g t hg
  intro htrap
  apply hs
  exact recognize _ _ (smallDisplacementData_of_trappedSpan common early p g t hg ht htrap)

/-- In the non-single-section branch, one actual amalgam element sends alpha
to the chosen moving vertex and the midpoint to a Z-layer escaping Q_alpha.
The full marked natural-section recognition is proved, with no additional
representation premise. This is the escaping-conjugate step of (4.6.8)(2). -/
theorem escapingTransport [Finite M]
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i) (hs : ¬ SingleSection p)
    (t : Vertex R) (ht : nu R geometry (alpha R) t) :
    ∃ g : FreeAmalgam R, act R g (alpha R) = t ∧
      ¬ Z R (act R g p.middle) ≤ Q R (alpha R) := by
  exact escapingTransport_of_recognition common early p hs t ht
    (fun _ _ d => singleNaturalSection_of_smallDisplacement d)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
