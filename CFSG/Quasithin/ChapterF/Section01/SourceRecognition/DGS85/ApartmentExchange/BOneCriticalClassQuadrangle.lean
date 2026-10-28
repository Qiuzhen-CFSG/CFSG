module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneClassQuadrangle
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneCriticalSplitQuotient

/-!
# Raw quadrangle geometry from the original critical pair

The original nonsolvable critical b=1 pair supplies both full-Cartan profiles.
Its r=3 branch retains the complete finite marked split quotient, including
the whole original Borel and both parabolic maps. In the central r=4 branch,
all generalized-quadrangle laws are now proved for the literal apartment
classes, together with local bijectivity and the original field's valence.
The earlier central-root and faithful marked-completion data are retained.

This theorem removes the missing raw graph geometry from the central source
branch. It does not assert r=4 Borel-image signs or a marked split quotient;
those and the other Chapter 14 alternatives remain to be established.
Source: DGS, Groups and Graphs (1985), (10.5), pp.155--157,
(3.6)--(3.7), pp.77--80, and the natural central case of (14.15), p.219.
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

theorem raw_class_geometry_of_critical_bOne
    (h : HypothesisF11 L S)
    (hns : ∀ j : Fin 2, ¬ Group.IsSolvable (parabolic L S j))
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1)
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} h c j,
      HasMarkedGeometricQuotient ds ∧
      ((∃ hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4,
        Nonempty (RankTwoAmalgam.Iso (reducedAmalgam L S)
          (fullCartanRThreeFiniteQuotient ds hr).standardAmalgam) ∧
        Nonempty (Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
          (fullCartanRThreeFiniteQuotient ds hr).tits)) ∨
      (HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 ∧
        HasCentralRootGeometry ds ∧ FullCartanClassQuadrangle ds)) := by
  obtain ⟨ds, hparams, hgeo, _, _⟩ := exchange_geometry_of_critical_bOne h hns hc hne hb c
  refine ⟨ds, hgeo, ?_⟩
  rcases hparams with hr | ⟨hr, hcentral⟩
  · exact Or.inl ⟨hr, ⟨fullCartanRThreeFiniteMarkedIso ds hr⟩,
      ⟨fullCartanRThreeFiniteSplitData ds hr⟩⟩
  · exact Or.inr ⟨hr, hcentral, fullProfileClassQuadrangle ds hr⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
