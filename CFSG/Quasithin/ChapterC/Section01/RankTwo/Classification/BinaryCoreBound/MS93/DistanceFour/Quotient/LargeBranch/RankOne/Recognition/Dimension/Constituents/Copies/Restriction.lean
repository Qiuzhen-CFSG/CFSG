module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Interface
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Candidate
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Splitting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction.ModelQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction.Model

/-!
# Full rank-one coordinates on the literal second star

The second star is identified with the adjacent parabolic orbit of the
actual edge space inside the starred module. This edge space is fixed by
the full first parabolic and its full SL3(2) orbit generates the star.
The equivalence below intertwines the full prescribed rank-one quotient,
through the original source projection and the intrinsic two-core kernel.

Under genuine homogeneous splitting, the model restriction calculation gives
two natural rank-one factors on this orbit. Composing the two equivalences
and lifting through the surjective prescribed quotient gives coordinates on
the literal second star, with the full SL2(2) action equation. Both natural
orientations are covered. The splitting premise is discharged upstream by
`TwoNaturalFactors.split_of_estimates`; the parent retains that assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(5), pp.911--912, with the fixed-space sums on pp.905 and 910.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The literal second-star module has precisely the geometric inputs to
the homogeneous restriction calculation, with the full prescribed SL2(2)
action retained on every matrix-parabolic element. -/
theorem secondStar_restriction
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s) :
    Restriction.edgeSpace (geometry := geometry) d ≤
      fixedSpace (starRepresentation (geometry := geometry) d).toRepresentation
        (modelParabolic f.flag f.first) ∧
    Seed.orbitSpace (starRepresentation (geometry := geometry) d).toRepresentation
      ⊤ (Restriction.edgeSpace (geometry := geometry) d) = ⊤ ∧
    ∃ e : (Seed.secondTildeStar (geometry := geometry) d f 1) ≃ₗ[ZMod 2]
      Restriction.secondOrbit (geometry := geometry) d f,
      ∀ (a : modelParabolic f.flag (!f.first))
        (v : Seed.secondTildeStar (geometry := geometry) d f 1),
        (e (secondRankOneAction d f (Restriction.modelQuotient f a) v) :
          (starRepresentation (geometry := geometry) d).toSubmodule) =
        (starRepresentation (geometry := geometry) d).toRepresentation a.val
          (e v : (starRepresentation (geometry := geometry) d).toSubmodule) := by
  refine ⟨Restriction.edgeSpace_le_fixed common radius hb s hbc d f hest,
    Restriction.edgeSpace_generates d,
    Restriction.secondStarEquivOrbit common radius hb s hbc d f hest, ?_⟩
  intro a v
  obtain ⟨m, rfl⟩ := Restriction.modelProjection_surjective f a
  rw [Restriction.modelQuotient_apply, Restriction.modelProjection_apply]
  exact Restriction.secondStarEquivOrbit_action common radius hb s hbc d f hest m v

/-- Homogeneous splitting identifies the literal second-star fixed-space sum
with two natural modules for the full prescribed SL2(2) action. The source
branch and escape hypotheses are retained for the original consumer; once
the splitting and estimates are supplied, the restriction uses only their
fixed-seed and generation consequences. -/
theorem secondStar_coordinates_of_split
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (_hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (_hf : Seed.Compatible f s)
    (_hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤
      Q R s.middle)
    (hest : Estimates d f s)
    (hsplit : Nonempty ((starRepresentation (geometry := geometry) d).toRepresentation.Equiv
        (BinaryLinearThree.W.prod BinaryLinearThree.W)) ∨
      Nonempty ((starRepresentation (geometry := geometry) d).toRepresentation.Equiv
        (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual))) :
    ∃ e : (Seed.secondTildeStar (geometry := geometry) d f 1) ≃ₗ[ZMod 2]
        (Fin 2 → Fin 2 → ZMod 2),
      ∀ (a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
        (v : Seed.secondTildeStar (geometry := geometry) d f 1) (j : Fin 2),
        e (secondRankOneAction d f a v) j = a.val.mulVec (e v j) := by
  obtain ⟨_, _, e, he⟩ := secondStar_restriction common radius hb s hbc d f hest
  obtain ⟨c, hc⟩ := Restriction.secondOrbit_coordinates
    common radius hb s hbc d f hest hsplit
  refine ⟨e.trans c, ?_⟩
  intro a v j
  obtain ⟨g, rfl⟩ := Restriction.modelQuotient_surjective f a
  exact hc g (e v) (e (secondRankOneAction d f (Restriction.modelQuotient f g) v))
    (he g v) j

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
