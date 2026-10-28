module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Interface
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Candidate
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Splitting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction

/-!
# Splitting and coordinate assembly for the second starred layer

The source estimates and the two literal natural factors give homogeneous
SL3(2) splitting in Copies.Splitting. Copies.Restriction identifies the
literal second starred layer inside either homogeneous orientation and
constructs coordinates for its full descended SL2(2) action. The assembly
below converts these coordinates into NaturalCopies, using the intrinsic
parabolic quotient and its proved action equation through source.projection.

The factor witness and source estimates remain explicit intermediate
premises; their production belongs to the constituent assembly. No
splitting, orientation or additional coordinate premise is required here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(5), printed pp.911--912.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Coordinates intertwining the full descended action give exactly the
original parabolic action equation, with its actual intrinsic two-core kernel. -/
noncomputable def naturalCopiesOfRankOneCoordinates
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (e : (Seed.secondTildeStar (geometry := geometry) d f 1) ≃ₗ[ZMod 2]
      (Fin 2 → Fin 2 → ZMod 2))
    (he : ∀ (a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (v : Seed.secondTildeStar (geometry := geometry) d f 1) (j : Fin 2),
      e (secondRankOneAction d f a v) j = a.val.mulVec (e v j)) :
    NaturalCopies (geometry := geometry) d f where
  quotient := parabolicQuotient f true
  onto := parabolicQuotient_surjective f true
  kernel := parabolicQuotient_kernel f true
  coordinates := e
  action m v w hw := by
    have h : w = secondRankOneAction d f (parabolicQuotient f true m) v :=
      Subtype.ext (hw.trans (secondRankOneAction_apply d f m v).symm)
    rw [h]
    exact he _ _

/-- The supplied two natural-or-dual factors and source estimates give two
natural copies on the literal second star for the full parabolic quotient.
Homogeneous splitting and its restriction are both discharged here; the
constituent assembly retains production of the factors and estimates. -/
theorem naturalCopies_of_twoNaturalFactors
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤
      Q R s.middle)
    (hest : Estimates d f s) (n : TwoNaturalFactors (geometry := geometry) d) :
    Nonempty (NaturalCopies (geometry := geometry) d f) := by
  obtain ⟨e, he⟩ := secondStar_coordinates_of_split common radius hb s hs hbc d f hf
    hescape hest (TwoNaturalFactors.split_of_estimates common n f s hest)
  exact ⟨naturalCopiesOfRankOneCoordinates d f e he⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
