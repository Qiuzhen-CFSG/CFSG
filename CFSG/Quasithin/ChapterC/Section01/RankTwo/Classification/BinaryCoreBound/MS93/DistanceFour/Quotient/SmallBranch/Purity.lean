module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.Criteria
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.Square
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.ParabolicGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.ParabolicMultiplicity
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple

/-!
# One copy and no fixed vectors in the small-intersection branch

The starred-intersection and binary square arguments remove the fixed kernel
of every supplied core module with homogeneous FF coordinates. The source flag
argument supplies an actual parabolic with the edge-kernel equality and the
central triple commutator. Its edge star is centralized modulo Z, and the
identity VStar intersection B = Z transfers a nonzero residual-fixed vector
to core/U. The small-intersection midpoint index bounds the fixed codimension
of this same parabolic's intrinsic two-core by two.

The marked model calculation therefore leaves at most one copy. Faithfulness
excludes zero copies, giving the requested conjunction with the original
coordinate marking unchanged. In particular, (1.4) alone permits two copies;
the parabolic bounds supply the additional inference in (4.6.11).

`one_copy_and_no_fixed` is conditional on the supplied CoreModule and
ModuleQuotient, whose construction remains with the source recognition owner.
Source: original Meierfrankenfeld--Stellmacher (1993), (1.4), printed p.842,
and (4.6.8)--(4.6.11), printed pp.905--909.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The source small-intersection geometry selects one homogeneous natural
factor and removes the full fixed space, for the supplied quotient coordinates. -/
theorem one_copy_and_no_fixed
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : s.SmallIntersection)
    (d : CoreModule source) (m : ℕ)
    (q : AbelianCore.QuotientRecognition.ModuleQuotient d.representation m) :
    m = 1 ∧ Representation.BinaryOffender.fixedSpace d.representation ⊤ = ⊥ := by
  obtain ⟨i, hkernel, htriple⟩ :=
    Flags.RankOne.flagControl source geometry common hb radius.toEarlyFacts
  have hbounds := parabolicBounds_of_flag source geometry common radius hb s hs d m q
    i hkernel htriple
  have hle := multiplicity_le_one_of_parabolicBounds d.representation q source.flag i hbounds
  have hpos := q.multiplicity_pos d.faithful
  exact ⟨by omega, no_fixed source geometry common radius d m q⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
