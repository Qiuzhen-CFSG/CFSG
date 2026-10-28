module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootBinaryCore
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenFirstCoreGeometry
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreePathElations

/-!
# Seven-fixed root conjugators fixing the second vertex

The original core intersection identifies a seven-fixed core element fixing
the second vertex with the binary center plane. The actual root lies in the
full binary core, so this element centralizes the root. Faithfulness of the
same covering on the endpoint lifts that centralization to the original tree.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootFixedConjugator
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "U" => Universal.cosetFamily A

/-- Fixing the second reverse-path vertex forces the actual conjugator to
centralize the entire original root. -/
@[expose] def HasRootFixedConjugators (c:CompatibleCartans L (reducedSylow L S)) : Prop :=
  ∀ {a:SourceVertex A} (p:(sourceGraph A).Walk a (base U true)),
    p.IsPath → p.length=6 → p.penultimate=base U false →
    ∀ u∈Q U (base U true)⊓centralizer (cartan c:Set (A).Universal),
      u • p.reverse.getVert 2=p.reverse.getVert 2 →
      u∈centralizer (pathRoot (X := (A).Universal) p:Set (A).Universal)

private theorem assemble (h:HypothesisF11 L S) (c:CompatibleCartans L (reducedSylow L S))
    (hroot:SourceRootBinaryCore.HasBinaryRootCore h)
    (hfixed:∀ γ:Vertex F,(graph F).Adj (base F false) γ → base F true≠γ →
      ∀ v:G₀ L S,v∈Q F (base F true)⊓centralizer ((cartan c).map (bOne_tree_map h):Set (G₀ L S)) →
      v • γ=γ → v∈centralizer (Q F (base F false):Set (G₀ L S))) :
    HasRootFixedConjugators c := by
  intro a p hp hl hprev u hu hfix
  let cov := bOne_tree_cover h
  let f := bOne_tree_map h
  let P := stabilizer U (base U true)
  let R := pathRoot (X := (A).Universal) p
  have hp5 : p.getVert 5=base U false := by
    have hh := hprev
    change p.getVert (p.length-1)=base U false at hh
    simpa only [hl] using hh
  have hp6 : p.getVert 6=base U true := by rw [←hl,p.getVert_length]
  have hadj : (sourceGraph A).Adj (base U false) (p.getVert 4) := by
    simpa only [hp5] using (p.adj_getVert_succ (by omega : 4<p.length)).symm
  have hβadj : (sourceGraph A).Adj (base U false) (base U true) := by
    simpa only [hp5,hp6] using p.adj_getVert_succ (by omega : 5<p.length)
  have hne : base F true≠cov.vertex (p.getVert 4) := by
    intro he
    have he' : cov.vertex (base U true)=cov.vertex (p.getVert 4) := by
      simpa only [cov.vertex_base] using he
    have he'' := (cov.neighbor_bijective (base U false)).1
      (a₁ := ⟨_,hβadj⟩) (a₂ := ⟨_,hadj⟩) (Subtype.ext he')
    have hh := hp.getVert_injOn (by omega : 6≤p.length) (by omega : 4≤p.length)
      (hp6.trans (congrArg Subtype.val he''))
    omega
  have hfu : f u∈Q F (base F true)⊓centralizer ((cartan c).map f:Set (G₀ L S)) := by
    refine ⟨?_,?_⟩
    · have hh := mem_map_of_mem f hu.1
      rw [cover_core_map cov,cov.vertex_base] at hh
      exact hh
    · rintro _ ⟨x,hx,rfl⟩
      exact (map_mul f x u).symm.trans ((congrArg f (hu.2 x hx)).trans (map_mul f u x))
  have hfγ : f u • cov.vertex (p.getVert 4)=cov.vertex (p.getVert 4) := by
    rw [←cov.vertex_smul]
    have hh : u • p.getVert 4=p.getVert 4 := by
      simpa only [Walk.getVert_reverse,hl] using hfix
    exact congrArg cov.vertex hh
  have hfc := hfixed (cov.vertex (p.getVert 4))
    (by simpa only [cov.hom_apply_vertex,cov.vertex_base] using cov.hom.map_adj hadj) hne (f u) hfu hfγ
  have huP : u∈P := Q_le_stabilizer U (base U true) hu.1
  have hRP : R≤P := (pathRoot_fixes p).trans inf_le_left
  intro x hx
  have he : f x*f u=f u*f x := hfc (f x) (hroot p hp hl hprev (mem_map_of_mem f hx))
  have hj := (cov.stabilizerHom_bijective (base U true)).1
    (a₁ := ⟨x*u,P.mul_mem (hRP hx) huP⟩)
    (a₂ := ⟨u*x,P.mul_mem huP (hRP hx)⟩)
    (Subtype.ext (by change f (x*u)=f (u*x);rw [map_mul,map_mul];exact he))
  exact congrArg Subtype.val hj
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
/-- The original seven-fixed core element centralizes the root whenever
it fixes the actual second reverse-path vertex. -/
theorem source_root_fixed_conjugators
    (c:CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) : HasRootFixedConjugators c := by
  exact assemble (L := Lₛ) (S := Sₛ)
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap c
    (SourceRootBinaryCore.source_root_binary_core hG T hempty hM hu hmany hcard e H hH eR)
    (SourceSevenFirstCoreGeometry.source_seven_core_fixed_neighbor_centralizes
      hG T hempty hM hu hmany hcard e H hH eR c)
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootFixedConjugator
