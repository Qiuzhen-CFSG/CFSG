module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeSplitQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCriticalGeometry

/-!
# The marked split quotient from an original critical b=1 pair

The original nonsolvable critical-pair producer constructs both compatible
full-Cartan profiles and yields the source r=3 or r=4 alternative. In its
r=3 branch, the raw class-plane elation argument now supplies the finite
marked split quotient with the literal original maps. No extra coordinate,
exchange, root-sign or Borel-image premise is requested here.

The previously established geometric completion is retained alongside the
new standard-amalgam marking and split data. The original r=4 alternative
is preserved for its separate source argument; this theorem does not claim
the complete Chapter 14 family.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157,
and (3.6)--(3.7), pp.77--80.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange ReducedCartan
open Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

theorem marked_split_quotient_of_critical_bOne
    (h : HypothesisF11 L S)
    (hns : ∀ j : Fin 2, ¬ Group.IsSolvable (parabolic L S j))
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1)
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} h c j,
      (∃ hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4,
        HasMarkedGeometricQuotient ds ∧
        Nonempty (RankTwoAmalgam.Iso (reducedAmalgam L S)
          (fullCartanRThreeFiniteQuotient ds hr).standardAmalgam) ∧
        Nonempty (Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
          (fullCartanRThreeFiniteQuotient ds hr).tits)) ∨
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 := by
  obtain ⟨ds, hds⟩ := marked_geometry_of_critical_bOne h hns hc hne hb c
  refine ⟨ds, ?_⟩
  rcases hds with ⟨hr, hgeo, _, _⟩ | hr
  · exact Or.inl ⟨hr, hgeo, ⟨fullCartanRThreeFiniteMarkedIso ds hr⟩,
      ⟨fullCartanRThreeFiniteSplitData ds hr⟩⟩
  · exact Or.inr hr

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
