module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootHalfActor

/-!
# The actual marked eight-root before and after reflection changes

Every supplied genuine reflection geometry has an order-eight root,
normalized by the same Cartan and disjoint from the full endpoint core.
The order follows the original valence nine and odd seven-path fixers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Subgroup.CosetGeometry Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReflectionRootProfile
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => Universal.cosetFamily A
local notation "P" => RankTwo.stabilizer F (base F true)

/-- Full-core disjointness and exact size of the literal chosen root. -/
@[expose] def HasEightReflectionRoots (c : CompatibleCartans L (reducedSylow L S)) : Prop :=
  ∀ d:SixPathSmallActorGeometry c,
    let p := reflectionPath c d.reflection d.fixes d.moves d.normalizes 6 (by decide) true
    let R := pathRoot (X := (A).Universal) p.walk
    R≤P ∧ Nat.card R=8 ∧ Disjoint R ((P).pCoreIn 2) ∧
      cartan c≤normalizer (R:Set (A).Universal)

private theorem reflection_roots_of_valence (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S))
    (hv:Nat.card ((sourceGraph A).neighborSet (base F true))=9) :
    HasEightReflectionRoots c := by
  intro d
  let p := reflectionPath c d.reflection d.fixes d.moves d.normalizes 6 (by decide) true
  let ρ := pathRoots h c 6 (by decide) d.reflection d.fixes d.moves d.squares d.normalizes
    d.transitive d.thick true
  have hc := pathRoots_card_add_one h c 6 (by decide) d.reflection d.fixes d.moves
    d.squares d.normalizes d.transitive d.thick d.odd true
  change Nat.card (pathRoot (X := (A).Universal) p.walk)+1=_ at hc
  rw [hv] at hc
  change pathRoot (X := (A).Universal) p.walk≤P ∧
    Nat.card (pathRoot (X := (A).Universal) p.walk)=8 ∧
    Disjoint (pathRoot (X := (A).Universal) p.walk) ((P).pCoreIn 2) ∧
    cartan c≤normalizer (pathRoot (X := (A).Universal) p.walk:Set (A).Universal)
  refine ⟨(pathRoot_fixes p.walk).trans inf_le_left,by omega,?_,?_⟩
  · apply disjoint_def.mpr
    intro x hx hxP
    have hz : x∈pathRoot (X := (A).Universal) p.walk ⊓
        MulAction.stabilizer (A).Universal ρ.c :=
      ⟨hx,universal_vertex_core_fixes_neighbors h (base F true) ρ.c ρ.adj_c hxP⟩
    have he := pathRoots_exit_free h c 6 (by decide) d.reflection d.fixes d.moves
      d.squares d.normalizes d.transitive d.thick d.odd true ρ.c ρ.adj_c ρ.distinct.symm
    change pathRoot (X := (A).Universal) p.walk ⊓
      MulAction.stabilizer (A).Universal ρ.c=⊥ at he
    rw [he] at hz
    exact hz
  · exact p.fixed.trans (pathFixer_le_normalizer_pathRoot p.walk)
end Geometry

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR


local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
set_option maxHeartbeats 800000 in
/-- The full original source supplies exact eight-root size, full-core
disjointness and whole-Cartan normalization for every actual reflection geometry. -/
theorem source_eight_reflection_roots
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) : HasEightReflectionRoots c := by
  exact reflection_roots_of_valence (L := Lₛ) (S := Sₛ)
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap c
    (SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR _)
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReflectionRootProfile
