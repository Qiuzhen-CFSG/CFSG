module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCentralRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCriticalGeometry

/-!
# Original central b=1 root geometry

The original nonsolvable critical pair supplies both full-Cartan profiles.
In its r=4 alternative the literal long-path roots now supply opposite
cubic pairs, the full central natural quotient, and conjugacy of each
chosen reflection to a central translate of a long-root involution.
The centers have order q and every central correction is retained.

The r=3 marked geometric completion is reused unchanged. The r=4 exchange
argument and both branches' Borel-image root signs still require proof;
no finite split quotient or source classification is inferred from this
local central root geometry.

Source: DGS, Groups and Graphs (1985), (10.5), pp.156--157,
and the local algebra preceding (14.15), pp.217--220.
-/

open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Subgroup.CosetGeometry.RankTwo hiding base

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe u uF
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}

/-- The actual r=4 center, quotient coordinates, long-root fusion and cubic
pairs, keeping the central correction in each braid equation. -/
def HasCentralRootGeometry
    (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j) : Prop :=
  (∀ j, Nat.card (centerIn (universalBOneActor h j (ds j).data))=Nat.card (ds j).F) ∧
  (∀ j, ∃ d : NaturalCentralKernel (universalBOneQuotient h j (ds j).data),
    ∀ z : (universalBOneQuotient h j (ds j).data).ker,
      d.coordinates z=1 ↔ (z:universalBOneActor h j (ds j).data)∈
        center (universalBOneActor h j (ds j).data)) ∧
  (∀ j, ∃ x∈(fullCartanPathRoots ds j).root, orderOf x=2 ∧
    ∃ z∈centerIn (universalBOneActor h j (ds j).data),
      z∈(Universal.cosetFamily (reducedAmalgam L S) j).pCoreIn 2 ∧ z*z=1 ∧
      ∃ g∈universalBOneActor h j (ds j).data,
        g*(z*x)*g⁻¹=fullCartanReflections ds j) ∧
  ∀ j x, x∈(fullCartanPathRoots ds j).root → x≠1 →
    ∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (fullCartanOppositePath ds j),
      x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
      (∃ z∈centerIn (universalBOneActor h j (ds j).data),
        z∈(Universal.cosetFamily (reducedAmalgam L S) j).pCoreIn 2 ∧ z*z=1 ∧
        ∃ k∈cartan c, x*y*x=z*k*fullCartanReflections ds j) ∧
      ∀ z∈(Universal.cosetFamily (reducedAmalgam L S) j).pCoreIn 2,
        (Commute x z ∧ Commute y z ↔ z∈centerIn (universalBOneActor h j (ds j).data))

/-- The original critical pair gives either the previously constructed r=3
marked completion or the r=4 root geometry with its nontrivial center.
All coordinate, root-pair and central-fusion data are constructed. -/
theorem marked_geometry_of_critical_bOne_with_central_roots
    (h : HypothesisF11 L S)
    (hns : ∀ j : Fin 2, ¬ Group.IsSolvable (parabolic L S j))
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S)=1)
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} h c j,
      (HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4 ∧
        HasMarkedGeometricQuotient ds) ∨
      (HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 ∧
        HasCentralRootGeometry ds) := by
  obtain ⟨ds,hds⟩ := marked_geometry_of_critical_bOne h hns hc hne hb c
  refine ⟨ds,?_⟩
  rcases hds with he | hr
  · exact Or.inl ⟨he.1,he.2.1⟩
  · exact Or.inr ⟨hr,central_actor_card_of_r_four ds hr,central_kernel_coordinates ds,
      central_root_conjugacy ds,central_root_pairs ds⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
