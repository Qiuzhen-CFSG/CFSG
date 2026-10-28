module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.PairedSpans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.Representation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.SpanAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.SelfDualFF

/-!
# Paired-span inputs to the radius-offender construction

The first paragraph of MS93 (4.6.4), printed p.902, compares two actual
conjugate-generated spans. `PairedSpans` constructs the common-edge geometry,
both kernel escapes, central displacements of order two, and the two crossing
commutator bounds. The central quotient of a nonabelian span is the literal
carrier fixed in `SpanQuotientAction`.

The paired-span action and the binary SL₃(2) exclusion show that the
nonabelian-span branch is impossible. Final assembly exposes the requested
radius-fixed offender interface by this contradiction, without importing the
downstream abelianness module, which consumes that offender.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-! The nonabelian-span branch is impossible after passing to the actual
central quotient.  The resulting contradiction is discharged into the
radius-offender interface used by the preceding source argument. -/

theorem exists_radius_offender_of_noncommutative_neighborSpan
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (hnon : ¬ IsMulCommutative (neighborSpan a d)) :
    ∃ t : Vertex R, ∃ A : Subgroup (FreeAmalgam R),
      Adjacent R a t ∧ A ≤ Q R t ∧ ¬ A ≤ Q R a ∧
        (frattini A).map A.subtype ≤ Q R a ∧
          (radiusFixed geometry a A).relIndex (V R a) ≤ (Q R a).relIndex A := by
  obtain ⟨p, hactions⟩ :=
    SpanOffender.escaping_neighbor_spanQuotientAction_nonempty
      common initial hb a b d ha hab hdb hbad hnon
  exfalso
  rcases hactions with hleft | hright
  · obtain ⟨hleft⟩ := hleft
    let := hleft.finite
    let := hleft.elementary
    let : Module.Finite (ZMod 2)
        (Additive (neighborSpan a d ⧸ center (neighborSpan a d))) :=
      Module.Finite.of_finite
    exact SpanOffender.not_isFFModule_of_faithful_selfDual
      (Offenders.linearize hleft.action)
      (Offenders.linearize_injective hleft.action hleft.faithful)
      hleft.selfDual hleft.offending
  · obtain ⟨hright⟩ := hright
    let := hright.finite
    let := hright.elementary
    let : Module.Finite (ZMod 2)
        (Additive (neighborSpan p.e p.r ⧸ center (neighborSpan p.e p.r))) :=
      Module.Finite.of_finite
    exact SpanOffender.not_isFFModule_of_faithful_selfDual
      (Offenders.linearize hright.action)
      (Offenders.linearize_injective hright.action hright.faithful)
      hright.selfDual hright.offending

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment

end
