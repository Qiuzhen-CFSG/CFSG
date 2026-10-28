module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneMidpoint
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneFullCartanPaths
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRootCover

/-!
# Actual universal roots as midpoint symmetries

The original covering maps every four-edge path to a simple source path.
Its literal path-fixer isomorphism maps the root onto the full original
actor center at the midpoint. Local injectivity then lifts fixation of the
entire radius-two ball. Roots on any two paths with the same actual midpoint
are equal, and this applies to the chosen r=4 full-Cartan path roots.

The original covering map remains distinct from the finite geometric
quotient map. Equality of midpoint vertex classes alone has not been shown
to identify these root groups. That descent and Borel-image root signs remain
necessary. BOneMidpointConsumers supplies the original critical-pair and
Chapter 12 applications, retaining both full-Cartan profiles and the centers.
Source: DGS, Groups and Graphs (1985), (10.5), p.156, and (14.1)--(14.2),
pp.210--211; Aschbacher--Smith F.3.3--4, p.270.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S

private theorem midpoint_actor_normalized (j : Bool) :
    (B₀ L S).subgroupOf (G₀ L S)≤normalizer ((ds j).data.actor : Set (G₀ L S)) := by
  rw [(ds j).actor_eq]
  exact reduced_borel_normalizes_source_actor h _

include ds in
private theorem four_path_image_isPath {a b : SourceVertex A}
    (p : (sourceGraph A).Walk a b) (hp : p.IsPath) (hlen : p.length=4) :
    (p.map (bOne_tree_cover h).hom).IsPath := by
  have hg := bOne_cycle_length_gt_five (reduced_triple h) (ds false).data (ds true).data
    (midpoint_actor_normalized ds false) (midpoint_actor_normalized ds true)
    (ds false).dimension (ds true).dimension
  have hnb := (SimpleGraph.BasedWalk.nonbacktracking_map_iff (bOne_tree_cover h).hom
    (fun v => ((bOne_tree_cover h).neighbor_bijective v).1) (SimpleGraph.BasedWalk.ofWalk p)).mpr
      (SimpleGraph.BasedWalk.nonbacktracking_ofWalk_of_isPath p hp)
  have ht := SimpleGraph.PathTransitivePolygon.isPath_of_nonbacktracking_of_cycle_bound hg
    ((SimpleGraph.BasedWalk.ofWalk p).map (bOne_tree_cover h).hom) hnb (by simp [hlen])
  rw [SimpleGraph.Walk.isPath_def,SimpleGraph.BasedWalk.support_toWalk,
    SimpleGraph.BasedWalk.vertices_map,SimpleGraph.BasedWalk.vertices_ofWalk] at ht
  simpa only [SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_map,
    reducedFamily,RankTwo.Vertex] using ht

/-- The same universal covering maps the root onto the full original midpoint center. -/
theorem four_path_root_original_center {a b : SourceVertex A}
    (p : (sourceGraph A).Walk a b) (hp : p.IsPath) (hlen : p.length=4)
    (i : Bool) (g : G₀ L S)
    (hm : g • base (reducedFamily L S) i=(bOne_tree_cover h).vertex (p.getVert 2)) :
    (pathRoot (X := (reducedAmalgam L S).Universal) p).map (bOne_tree_map h) =
      (centerIn (BOneMidpoint.actor (ds false).data (ds true).data i)).map
        (MulAut.conj g).toMonoidHom := by
  rw [(bOne_tree_cover h).pathRoot_map]
  exact BOneMidpoint.four_path_root_translate (reduced_triple h) (ds false).data (ds true).data
    (midpoint_actor_normalized ds false) (midpoint_actor_normalized ds true) i g
    (p.map (bOne_tree_cover h).hom) (four_path_image_isPath ds p hp hlen)
    (by simpa only [SimpleGraph.Walk.length_map] using hlen)
    (by simpa only [SimpleGraph.Walk.getVert_map,reducedFamily,RankTwo.Vertex,
      RankTwo.base,RankTwo.CoverData.hom_apply_vertex] using hm)

include ds in
/-- Every universal four-edge root fixes the whole radius-two ball at its actual midpoint. -/
theorem four_path_root_fixes_ball_two {a b : SourceVertex A}
    (p : (sourceGraph A).Walk a b) (hp : p.IsPath) (hlen : p.length=4) :
    pathRoot (X := (reducedAmalgam L S).Universal) p ≤ RankTwo.ballKernel (Universal.cosetFamily A) (p.getVert 2) 2 := by
  intro x hx
  have him : bOne_tree_map h x∈pathRoot (X := G₀ L S) (p.map (bOne_tree_cover h).hom) := by
    rw [←(bOne_tree_cover h).pathRoot_map p]
    exact mem_map_of_mem _ hx
  have hf := BOneMidpoint.four_path_root_fixes_ball_two (reduced_triple h)
    (ds false).data (ds true).data
    (midpoint_actor_normalized ds false) (midpoint_actor_normalized ds true)
    (p.map (bOne_tree_cover h).hom) (four_path_image_isPath ds p hp hlen)
    (by simpa only [SimpleGraph.Walk.length_map] using hlen) him
  apply (bOne_tree_cover h).ballKernel_lift (p.getVert 2) 2 x
  · exact (Subgroup.pCoreIn_le 2 (pathFixer (X := (reducedAmalgam L S).Universal) p) hx) 2 (by omega)
  · simpa only [SimpleGraph.Walk.getVert_map,reducedFamily,RankTwo.CoverData.hom_apply_vertex] using hf

include ds in
/-- Equality of actual midpoints gives equality of the roots in the universal completion. -/
theorem four_path_roots_eq_of_midpoint {a b a' b' : SourceVertex A}
    (p : (sourceGraph A).Walk a b) (p' : (sourceGraph A).Walk a' b')
    (hp : p.IsPath) (hp' : p'.IsPath) (hlen : p.length=4) (hlen' : p'.length=4)
    (hm : p.getVert 2=p'.getVert 2) :
    pathRoot (X := (reducedAmalgam L S).Universal) p=pathRoot (X := (reducedAmalgam L S).Universal) p' := by
  have him : (pathRoot (X := (reducedAmalgam L S).Universal) p).map (bOne_tree_map h)=
      (pathRoot (X := (reducedAmalgam L S).Universal) p').map (bOne_tree_map h) := by
    rw [(bOne_tree_cover h).pathRoot_map,(bOne_tree_cover h).pathRoot_map]
    exact BOneMidpoint.four_path_roots_eq_of_midpoint (reduced_triple h)
      (ds false).data (ds true).data
      (midpoint_actor_normalized ds false) (midpoint_actor_normalized ds true)
      (p.map (bOne_tree_cover h).hom) (p'.map (bOne_tree_cover h).hom)
      (four_path_image_isPath ds p hp hlen) (four_path_image_isPath ds p' hp' hlen')
      (by simpa using hlen) (by simpa using hlen')
      (by simpa only [SimpleGraph.Walk.getVert_map,reducedFamily,RankTwo.Vertex,
        RankTwo.CoverData.hom_apply_vertex] using congrArg (bOne_tree_cover h).vertex hm)
  have hfix {a b : SourceVertex A} (p : (sourceGraph A).Walk a b) (hl : p.length=4)
      {x : (reducedAmalgam L S).Universal} (hx : x∈pathRoot (X := (reducedAmalgam L S).Universal) p) :
      x∈RankTwo.stabilizer (Universal.cosetFamily A) (p.getVert 2) :=
    (Subgroup.pCoreIn_le 2 (pathFixer (X := (reducedAmalgam L S).Universal) p) hx) 2 (by omega)
  apply le_antisymm
  · intro x hx
    have hx' := mem_map_of_mem (bOne_tree_map h) hx
    rw [him] at hx'
    obtain ⟨y,hy,he⟩ := hx'
    have hyfix := hfix p' hlen' hy
    rw [←hm] at hyfix
    have heq := ((bOne_tree_cover h).stabilizerHom_bijective (p.getVert 2)).1
      (a₁ := ⟨y,hyfix⟩) (a₂ := ⟨x,hfix p hlen hx⟩) (Subtype.ext he)
    have hyx : y=x := congrArg (fun z : RankTwo.stabilizer (Universal.cosetFamily A) (p.getVert 2) => (z:(reducedAmalgam L S).Universal)) heq
    exact hyx ▸ hy
  · intro x hx
    have hx' := mem_map_of_mem (bOne_tree_map h) hx
    rw [←him] at hx'
    obtain ⟨y,hy,he⟩ := hx'
    have hyfix := hfix p hlen hy
    rw [hm] at hyfix
    have heq := ((bOne_tree_cover h).stabilizerHom_bijective (p'.getVert 2)).1
      (a₁ := ⟨y,hyfix⟩) (a₂ := ⟨x,hfix p' hlen' hx⟩) (Subtype.ext he)
    have hyx : y=x := congrArg (fun z : RankTwo.stabilizer (Universal.cosetFamily A) (p'.getVert 2) => (z:(reducedAmalgam L S).Universal)) heq
    exact hyx ▸ hy

/-- Full midpoint-center images and radius-two fixation for the actual universal paths. -/
def HasMidpointRootGeometry : Prop :=
  ∀ {a b : SourceVertex A} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=4 →
    pathRoot (X := (reducedAmalgam L S).Universal) p ≤ RankTwo.ballKernel (Universal.cosetFamily A) (p.getVert 2) 2 ∧
    ∀ (i : Bool) (g : G₀ L S), g • base (reducedFamily L S) i=(bOne_tree_cover h).vertex (p.getVert 2) →
      (pathRoot (X := (reducedAmalgam L S).Universal) p).map (bOne_tree_map h)=
        (centerIn (BOneMidpoint.actor (ds false).data (ds true).data i)).map (MulAut.conj g).toMonoidHom

/-- Both original profiles construct all the midpoint geometry. -/
theorem full_profile_midpoint_geometry : HasMidpointRootGeometry ds := by
  intro a b p hp hl
  exact ⟨four_path_root_fixes_ball_two ds p hp hl,four_path_root_original_center ds p hp hl⟩

theorem full_profile_root_fixes_midpoint_ball
    (hr : fullCartanPathLength ds=4) (j : Bool) :
    let p := reflectionPath c (fullCartanReflections ds) (fullCartanReflections_fix ds)
      (fullCartanReflections_move ds) (fullCartanReflections_normalize ds)
      (fullCartanPathLength ds) (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds)) j
    (fullCartanPathRoots ds j).root ≤
      RankTwo.ballKernel (Universal.cosetFamily A) (p.walk.getVert 2) 2 := by
  let p := reflectionPath c (fullCartanReflections ds) (fullCartanReflections_fix ds)
      (fullCartanReflections_move ds) (fullCartanReflections_normalize ds)
      (fullCartanPathLength ds) (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds)) j
  change (fullCartanPathRoots ds j).root ≤ _
  rw [fullCartanRoots_root]
  exact four_path_root_fixes_ball_two ds p.walk p.isPath (p.length_eq.trans hr)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
