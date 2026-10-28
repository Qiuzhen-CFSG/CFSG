module
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRootCover
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenFirstCoreIntersection
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenFirstCoreGeometry

/-!
# The original six-path root lies in the full binary core

The root fixes two distinct neighbors at the binary interior vertex. The
three-point action forces it to fix that entire star, and the original
kernel Sylow theorem places this actual two-group in the full binary core.
The original cover retains the two neighbors distinctly.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootBinaryCore
open ChapterF.Source ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "U" => Universal.cosetFamily A

/-- Every aligned original six-path root maps into the full binary core. -/
@[expose] def HasBinaryRootCore (h : HypothesisF11 L S) : Prop :=
  ∀ {a:SourceVertex A} (p:(sourceGraph A).Walk a (base U true)),
    p.IsPath → p.length=6 → p.penultimate=base U false →
    (pathRoot (X := (A).Universal) p).map (bOne_tree_map h)≤Q F (base F false)

private theorem root_binary_core (h : HypothesisF11 L S)
    (hthree : Nat.card ((graph F).neighborSet (base F false))=3) :
    HasBinaryRootCore h := by
  intro a p hp hl hprev
  let cov := bOne_tree_cover h
  let R := pathRoot (X := (A).Universal) p
  have hp5 : p.getVert 5=base U false := by
    have hh := hprev
    change p.getVert (p.length-1)=base U false at hh
    simpa only [hl] using hh
  have hp6 : p.getVert 6=base U true := by rw [←hl,p.getVert_length]
  have hfix (k:ℕ) (hk:k≤p.length) :
      R.map (bOne_tree_map h)≤stabilizer F (cov.vertex (p.getVert k)) := by
    rintro _ ⟨v,hv,rfl⟩
    change bOne_tree_map h v • cov.vertex (p.getVert k)=cov.vertex (p.getVert k)
    rw [←cov.vertex_smul]
    exact congrArg cov.vertex ((pCoreIn_le 2 _ hv) k hk)
  have hadj : (sourceGraph A).Adj (base U false) (p.getVert 4) := by
    have hh := (p.adj_getVert_succ (by omega : 4<p.length)).symm
    simpa only [hp5] using hh
  have hβadj : (sourceGraph A).Adj (base U false) (base U true) := by
    have hh := p.adj_getVert_succ (by omega : 5<p.length)
    simpa only [hp5,hp6] using hh
  have hne : base F true≠cov.vertex (p.getVert 4) := by
    intro he
    have he' : cov.vertex (base U true)=cov.vertex (p.getVert 4) := by
      simpa only [cov.vertex_base] using he
    have he'' := (cov.neighbor_bijective (base U false)).1
      (a₁ := ⟨_,hβadj⟩) (a₂ := ⟨_,hadj⟩) (Subtype.ext he')
    have hh := hp.getVert_injOn (by omega : 6≤p.length) (by omega : 4≤p.length)
      (hp6.trans (congrArg Subtype.val he''))
    omega
  apply SourceSevenFirstCoreGeometry.two_subgroup_le_cubic_core_of_two_fixed h
    (by simpa only [CoverData.hom_apply_vertex,cov.vertex_base] using cov.hom.map_adj hβadj)
    (by simpa only [CoverData.hom_apply_vertex,cov.vertex_base] using cov.hom.map_adj hadj) hne hthree
    (R.map (bOne_tree_map h)) ((isPGroup_pCoreIn 2 _).map (bOne_tree_map h))
  · simpa only [hp5,cov.vertex_base] using hfix 5 (by omega)
  · simpa only [hp6,cov.vertex_base] using hfix 6 (by omega)
  · exact hfix 4 (by omega)
private theorem root_binary_core_of_valence (h : HypothesisF11 L S)
    (hv : Nat.card ((sourceGraph A).neighborSet (base U false))=3) :
    HasBinaryRootCore h := by
  apply root_binary_core h
  let cov := bOne_tree_cover h
  have he := Nat.card_congr (Equiv.ofBijective (cov.hom.mapNeighborSet (base U false))
    (cov.neighbor_bijective (base U false)))
  rw [cov.hom_apply_vertex,cov.vertex_base] at he
  exact he.symm.trans hv
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
/-- The actual aligned eight-root lies in the full original adjacent binary
core; its original center plane therefore centralizes this root. -/
theorem source_root_binary_core :
    HasBinaryRootCore
      (show HypothesisF11 Lₛ Sₛ from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) := by
  exact root_binary_core_of_valence (L := Lₛ) (S := Sₛ)
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
    (SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR _)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootBinaryCore
