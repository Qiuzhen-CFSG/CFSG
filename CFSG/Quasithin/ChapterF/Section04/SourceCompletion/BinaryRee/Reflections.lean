module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.OctagonGeometry
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths
public import Theory.Combinatorics.SimpleGraph.TwoNeighborWalks
/-!
# Apartment reflections in a small full binary Ree completion

Nine-path transitivity produces an element reversing nine edges of any
sixteen-cycle. Girth sixteen forces the remaining seven-edge path into that
cycle. An element preserving the cycle and fixing an oriented edge fixes its
nine-path, hence is trivial. Therefore the reversing element is a nonidentity
involution. All elements act on the original completion graph, and the only
source hypothesis is its literal smallness witness.

Source: Aschbacher--Smith F.4.15--16, printed pp.281--282.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (c : Completion G)

private def firstNine {x y : c.Vertex} (p : c.graph.Walk x y) (hl : 9 ≤ p.length) :
    BasedWalk c.graph 9 x :=
  (show (p.take 9).length = 9 by rw [Walk.take_length, Nat.min_eq_left hl]) ▸
    BasedWalk.ofWalk (p.take 9)

private theorem firstNine_vertices {x y : c.Vertex} (p : c.graph.Walk x y)
    (hl : 9 ≤ p.length) : (firstNine c p hl).vertices = (p.take 9).support :=
  (BasedWalk.vertices_cast _ _).trans (BasedWalk.vertices_ofWalk _)

private theorem firstNine_nb {v : c.Vertex} (p : c.graph.Walk v v)
    (hp : p.IsCycle) (hl : 9 < p.length) :
    (firstNine c p hl.le).Nonbacktracking :=
  (BasedWalk.nonbacktracking_cast _ _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hp.isPath_take hl))

/-- A local element reverses the first nine vertices along either orientation
of an actual sixteen-cycle. -/
theorem exists_mirror_prefix {v : c.Vertex} (p : c.graph.Walk v v)
    (hp : p.IsCycle) (hl : p.length = 16) :
    ∃ g : G, g • v = v ∧
      (p.take 9).support.map (g • ·) = (p.reverse.take 9).support := by
  have h9 : 9 < p.length := by omega
  have hr9 : 9 < p.reverse.length := by rw [Walk.length_reverse]; omega
  obtain ⟨g, hgv, hg⟩ := nine_transitive c v (firstNine c p h9.le)
    (firstNine c p.reverse hr9.le) (firstNine_nb c p hp h9)
    (firstNine_nb c p.reverse hp.reverse hr9)
  exact ⟨g, hgv, by rwa [firstNine_vertices, firstNine_vertices] at hg⟩

/-- Under girth sixteen, a map which reverses the first nine cycle vertices
preserves the whole cycle support. -/
theorem mirror_prefix_preserves_support
    (hgirth : ∀ v (q : c.graph.Walk v v), q.IsCycle → 16 ≤ q.length)
    {v : c.Vertex} (p : c.graph.Walk v v) (hp : p.IsCycle) (hl : p.length = 16)
    (g : G) (hgv : g • v = v)
    (hm : (p.take 9).support.map (g • ·) = (p.reverse.take 9).support) :
    ∀ w ∈ p.support, g • w ∈ p.support := by
  have hprefix : ∀ w ∈ (p.take 9).support, g • w ∈ p.support := by
    intro w hw
    have h : g • w ∈ (p.reverse.take 9).support := by
      rw [← hm]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    rw [Walk.support_take] at h
    have hh := List.mem_of_mem_take h
    simpa only [Walk.support_reverse, List.mem_reverse] using hh
  let f := (graphAction c).hom g
  have hd : ((p.drop 9).map f).support ⊆ p.support :=
    OctagonShortPaths.short_path_support_subset hgirth p hl
      ((hp.isPath_drop (by decide : 0 < 9)).map (MulAction.injective g))
      (by simp only [Walk.length_map, Walk.drop_length, hl]; norm_num)
      (hprefix _ (p.take 9).end_mem_support)
      (by change g • v ∈ p.support; rw [hgv]; exact p.start_mem_support)
  intro w hw
  have hh : w ∈ ((p.take 9).append (p.drop 9)).support := by
    rw [Walk.append_take_drop_eq]
    exact hw
  rcases (Walk.mem_support_append_iff _ _).mp hh with hh | hh
  · exact hprefix w hh
  · apply hd
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨w, hh, rfl⟩
private theorem prefix_first {x y : c.Vertex} (p : c.graph.Walk x y)
    (hl : 9 ≤ p.length) : ((firstNine c p hl).1 : c.Vertex) = p.getVert 1 := by
  have he := congrArg (fun l : List c.Vertex => l[1]?) (firstNine_vertices c p hl)
  have ht : (p.take 9).support[1]? = some (p.getVert 1) := by
    rw [Walk.support_take, List.getElem?_take_of_lt (by decide : 1 < 9 + 1)]
    exact (p.getVert_eq_support_getElem? (by omega)).symm
  exact Option.some.inj ((show some ((firstNine c p hl).1 : c.Vertex) =
    (firstNine c p hl).vertices[1]? from rfl).trans (he.trans ht))

private theorem mirror_first {v : c.Vertex} (p : c.graph.Walk v v)
    (hl : p.length = 16) (g : G)
    (hm : (p.take 9).support.map (g • ·) = (p.reverse.take 9).support) :
    g • p.getVert 1 = p.getVert 15 := by
  have h := congrArg (fun l : List c.Vertex => l[1]?) hm
  rw [List.getElem?_map, Walk.support_take, Walk.support_take,
    List.getElem?_take_of_lt (by decide : 1 < 9 + 1),
    List.getElem?_take_of_lt (by decide : 1 < 9 + 1),
    ← p.getVert_eq_support_getElem? (by omega),
    ← p.reverse.getVert_eq_support_getElem? (by rw [Walk.length_reverse]; omega)] at h
  simpa only [Option.map_some, Option.some.injEq, Walk.getVert_reverse, hl] using h

/-- An apartment-preserving element fixing its first oriented edge is trivial. -/
theorem cycle_edge_fixer_eq_one
    (hgirth : ∀ v (q : c.graph.Walk v v), q.IsCycle → 16 ≤ q.length)
    {v : c.Vertex} (p : c.graph.Walk v v) (hp : p.IsCycle) (hl : p.length = 16)
    (g : G) (hgv : g • v = v) (hfirst : g • p.getVert 1 = p.getVert 1)
    (hs : ∀ w ∈ p.support, g • w ∈ p.support) : g = 1 := by
  let q := firstNine c p (by omega)
  have hq : q.Nonbacktracking := firstNine_nb c p hp (by omega)
  have hqA : ∀ w ∈ q.vertices, w ∈ p.support := by
    intro w hw
    rw [firstNine_vertices, Walk.support_take] at hw
    exact List.mem_of_mem_take hw
  have he := BasedWalk.vertices_eq_of_first_of_two_neighbors
    {w | w ∈ p.support} (OctagonShortPaths.cycle_neighbors_two hgirth p hp hl)
    (q.map ((graphAction c).hom g)) q hgv
    (((graphAction c).nonbacktracking_map_iff g q).mpr hq) hq
    (by
      intro w hw
      rw [BasedWalk.vertices_map] at hw
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
      exact hs z (hqA z hz)) hqA
    (by
      change g • (q.1 : c.Vertex) = (q.1 : c.Vertex)
      rw [prefix_first]
      exact hfirst)
  rw [BasedWalk.vertices_map] at he
  have hg : g ∈ pathStabilizer c.family q := by
    intro w hw
    exact List.map_inj_left.mp (he.trans (List.map_id _).symm) w hw
  rw [nine_fixer_eq_bot c v q hq] at hg
  exact hg

/-- The element reversing an apartment prefix is an involution. -/
theorem mirror_prefix_sq_eq_one
    (hgirth : ∀ v (q : c.graph.Walk v v), q.IsCycle → 16 ≤ q.length)
    {v : c.Vertex} (p : c.graph.Walk v v) (hp : p.IsCycle) (hl : p.length = 16)
    (g : G) (hgv : g • v = v)
    (hm : (p.take 9).support.map (g • ·) = (p.reverse.take 9).support) :
    g ^ 2 = 1 := by
  have hs := mirror_prefix_preserves_support c hgirth p hp hl g hgv hm
  have h1 := mirror_first c p hl g hm
  have hne : p.getVert 1 ≠ p.getVert 15 := by
    intro he
    have := hp.getVert_injOn' (by change 1 ≤ p.length - 1; omega)
      (by change 15 ≤ p.length - 1; omega) he
    omega
  have hv1 : c.graph.Adj v (p.getVert 1) := by
    simpa only [Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
  have hv15 : c.graph.Adj v (p.getVert 15) := by
    have h := (p.adj_getVert_succ (i := 15) (by omega)).symm
    have h16 : p.getVert (15 + 1) = v := by
      change p.getVert 16 = v
      rw [← hl, Walk.getVert_length]
    rwa [h16] at h
  have h15 : g • p.getVert 15 = p.getVert 1 := by
    obtain ⟨a, b, _, hab⟩ := Set.ncard_eq_two.mp
      (OctagonShortPaths.cycle_neighbors_two hgirth p hp hl v p.start_mem_support)
    have hx : p.getVert 1 ∈ ({w | w ∈ p.support ∧ c.graph.Adj v w} : Set c.Vertex) :=
      ⟨p.getVert_mem_support _, hv1⟩
    have hy : p.getVert 15 ∈ ({w | w ∈ p.support ∧ c.graph.Adj v w} : Set c.Vertex) :=
      ⟨p.getVert_mem_support _, hv15⟩
    have hz : g • p.getVert 15 ∈ ({w | w ∈ p.support ∧ c.graph.Adj v w} : Set c.Vertex) := by
      refine ⟨hs _ (p.getVert_mem_support _), ?_⟩
      have hh := ((graphAction c).hom g).map_adj hv15
      change c.graph.Adj (g • v) (g • p.getVert 15) at hh
      rwa [hgv] at hh
    simp only [hab, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
    have hneq : g • p.getVert 15 ≠ p.getVert 15 := by
      intro he
      exact hne ((MulAction.injective g) (h1.trans he.symm))
    aesop
  apply cycle_edge_fixer_eq_one c hgirth p hp hl (g ^ 2)
  · rw [pow_two, mul_smul, hgv, hgv]
  · rw [pow_two, mul_smul, h1, h15]
  · intro w hw
    rw [pow_two, mul_smul]
    exact hs _ (hs w hw)

/-- Each vertex of an actual source apartment has its reversing involution. -/
theorem exists_cycle_reflection (hsmall : c.Small)
    {v : c.Vertex} (p : c.graph.Walk v v) (hp : p.IsCycle) (hl : p.length = 16) :
    ∃ g : G, g • v = v ∧ g ^ 2 = 1 ∧ g ≠ 1 ∧
      g • p.getVert 1 = p.getVert 15 ∧
      (∀ w ∈ p.support, g • w ∈ p.support) ∧
      (p.take 9).support.map (g • ·) = (p.reverse.take 9).support := by
  obtain ⟨g, hgv, hm⟩ := exists_mirror_prefix c p hp hl
  have h1 := mirror_first c p hl g hm
  refine ⟨g, hgv, mirror_prefix_sq_eq_one c (cycle_bound_of_small c hsmall)
    p hp hl g hgv hm, ?_, h1,
    mirror_prefix_preserves_support c (cycle_bound_of_small c hsmall) p hp hl g hgv hm, hm⟩
  intro he
  rw [he, one_smul] at h1
  have := hp.getVert_injOn' (by change 1 ≤ p.length - 1; omega)
    (by change 15 ≤ p.length - 1; omega) h1
  omega

end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
