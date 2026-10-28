module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoreGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.MarkedQuotient
public import Theory.GroupTheory.WeakBNPair.RegularTree.BallKernelCover

/-!
# Interior stars of the source four-path roots

Transport both literal endpoint quotient catalogues along the original
cover and vertex conjugation. A two-subgroup fixing a path fixes two
distinct neighbors at each interior vertex; the rank-one Sylow-intersection
argument puts its image in that vertex's two-core. Local injectivity of the
cover lifts fixation of the entire star to the original universal tree.

The unitary application uses both possible beta markings, PSU3 and SU3,
and supplies the interior-star premise for the same apartment quotient.
Source: DGS, Groups and Graphs (1985), (11.8), pp.175--177,
(14.1)--(14.2), pp.210--211, and (3.6)--(3.7), pp.77--80.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (models : ∀ i : Bool, IsRankOneModel
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).map
        (Reduction.G₀ L S).subtype ⧸ pCore 2
          ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).map
            (Reduction.G₀ L S).subtype)))
include h models

private theorem source_model_at (v : Vertex F) :
    IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) := by
  let d := reducedFullEarlierLocalTheorems h
  have hbase (i : Bool) : IsRankOneModel
      (d.localGroup (base F i) ⧸ pCore 2 (d.localGroup (base F i))) := by
    let j := (d.localGroup (base F i)).equivMapOfInjective
      (G₀).subtype (G₀).subtype_injective
    let e := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
    exact (models i).of_equiv e
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [←hg]
  let j := (MulEquiv.subgroupCongr (d.conjugate g (base F v.type))).trans
    ((d.localGroup (base F v.type)).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  exact (hbase v.type).of_equiv (QuotientGroup.congr _ _ j (pCore_map_iso 2 j))

/-- The literal source path radical fixes every interior star. -/
theorem original_pathRoot_fixes_interior_stars_of_models
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b) (hp : p.IsPath)
    (u : (A).Universal) (hu : u ∈ pathRoot (X := (A).Universal) p) :
    ∀ j, 0 < j → j < p.length →
      ∀ z, (sourceGraph A).Adj (p.getVert j) z → u • z = z := by
  let cov := bOne_tree_cover h
  let f := bOne_tree_map h
  let R := pathRoot (X := (A).Universal) p
  have hfix (j : ℕ) (hj : j ≤ p.length) :
      R.map f ≤ stabilizer F (cov.vertex (p.getVert j)) := by
    rintro _ ⟨v, hv, rfl⟩
    change f v • cov.vertex (p.getVert j) = cov.vertex (p.getVert j)
    rw [← cov.vertex_smul]
    exact congrArg cov.vertex ((pCoreIn_le 2 _ hv) j hj)
  intro j hj hjl z hz
  have hprev := p.adj_getVert_succ (by omega : j - 1 < p.length)
  rw [show j - 1 + 1 = j by omega] at hprev
  have hnext := p.adj_getVert_succ hjl
  have hne : cov.vertex (p.getVert (j - 1)) ≠ cov.vertex (p.getVert (j + 1)) := by
    intro he
    have he' := (cov.neighbor_bijective (p.getVert j)).1
      (a₁ := ⟨_, hprev.symm⟩) (a₂ := ⟨_, hnext⟩) (Subtype.ext he)
    have hh := hp.getVert_injOn (by omega : j - 1 ≤ p.length)
      (by omega : j + 1 ≤ p.length) (congrArg Subtype.val he')
    omega
  have hcore := source_two_neighbor_two_group_le_core (reduced_triple h)
    (reduced_borel_core_sylow h) (reducedFullEarlierLocalTheorems h)
    (cov.hom.map_adj hprev) (cov.hom.map_adj hnext) hne
    (source_model_at h models _) (R.map f)
    ((isPGroup_pCoreIn 2 (pathFixer (X := (A).Universal) p)).map f)
    (hfix (j-1) (by omega)) (hfix j (by omega)) (hfix (j+1) (by omega))
  have hU := (source_Z_Q_U (reduced_triple h) _).2 (hcore (mem_map_of_mem f hu))
  exact cov.fixes_neighbor_of_image hz u ((pCoreIn_le 2 _ hu) j (by omega))
    (hU _ ((mem_ball_one _ _ _).mpr (Or.inl (cov.hom.map_adj hz))))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
