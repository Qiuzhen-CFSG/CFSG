module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeClassPlane
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCriticalGeometry

/-!
# Raw class planes from the original nonsolvable critical pair

The existing source construction supplies the paired full-Cartan profiles,
the r=3 or r=4 path alternative, and the r=3 faithful finite geometric
completion. Apply the raw-class geometry and incidence count to those same
profiles. This yields a projective plane of the original field order on the
very classes used to define that completion's action kernel.

The r=4 alternative and the original marked geometric completion are retained.
This theorem adds no plane, coordinate, exchange or Borel-image hypothesis.
The whole-Borel comparison, split BN structure and the remaining Chapter 14
branches still belong to the full source-theorem assembly.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(3.6), pp.77--78, (10.5), pp.156--157, and (14.13), pp.217--218.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam Configuration
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Subgroup.CosetGeometry.RankTwo hiding base
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original critical b=1 branch constructs the raw projective plane and
its order on the same relation as the marked finite geometric completion.
The original r=4 alternative is retained. No profile, exchange, plane or
Borel-image input is added. -/
theorem class_plane_of_critical_bOne
    (h : HypothesisF11 L S)
    (hns : ∀ j : Fin 2, ¬ Group.IsSolvable (parabolic L S j))
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1)
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} h c j,
      (HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4 ∧
        HasMarkedGeometricQuotient ds ∧
        ∃ plane : ProjectivePlane (fullCartanClassPoint ds) (fullCartanClassLine ds),
          letI := plane
          ProjectivePlane.order (fullCartanClassPoint ds) (fullCartanClassLine ds) =
            Nat.card (ds false).F) ∨
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 := by
  obtain ⟨ds, hds⟩ := marked_geometry_of_critical_bOne h hns hc hne hb c
  refine ⟨ds, ?_⟩
  rcases hds with ⟨hr, hgeo, _, _⟩ | hr
  · exact Or.inl ⟨hr, hgeo, fullCartanClassPlane ds hr, fullCartanClassPlane_order ds hr⟩
  · exact Or.inr hr

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
