module

public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.OctagonRootPath.ApartmentAction
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.Girth
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths
public import Theory.Combinatorics.SimpleGraph.TwoNeighborWalks

/-!
# Both-type nine-path transitivity of an octagonal Tits system

Bruhat decomposition places the first and last edges of a nonbacktracking
nine-walk in one normalizer apartment. The intervening seven-walk is a path;
girth sixteen forces it to coincide with an apartment arc of length at most
eight. Thus the whole walk lies in that apartment. The marked dihedral action
normalizes its first oriented edge, and two neighbors at each apartment
vertex determine every subsequent step. This proves literal rooted
vertex-list transitivity at every vertex and for both types.

Source: the BN-pair polygon construction, GLS3 §§2.3 and 2.6;
Aschbacher–Smith F.3.5 and F.4.8. No path-transitivity or recognition hypothesis
is part of the input datum.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped Pointwise
variable {X I : Type*} [Group X] {T : TitsSystem (X := X)} {F : I → Subgroup X}
namespace OctagonalDatum
variable (D : OctagonalDatum T F)
include D

private theorem translated_cycle (g : X) :
    ∃ a, ∃ c : (graph F).Walk a a, c.IsCycle ∧ c.length = 16 ∧
      {w | w ∈ c.support} = g • apartment T F := by
  obtain ⟨a, c, hc, hl, hs⟩ := D.standardApartmentCycle
  refine ⟨(smulHom F g) a, c.map (smulHom F g), hc.map (MulAction.injective g), ?_, ?_⟩
  · simpa only [Walk.length_map] using hl
  · rw [← hs]
    ext w
    change w ∈ (c.map (smulHom F g)).support ↔ _
    rw [Walk.support_map]
    simp only [List.mem_map, Set.mem_smul_set, Set.mem_ofPred_eq, smulHom_apply]

/-- Every translated apartment has two induced neighbors at each vertex. -/
theorem apartment_neighbors_two (g : X) (v : CosetGeometry.Vertex F)
    (hv : v ∈ g • apartment T F) :
    {w | w ∈ g • apartment T F ∧ (graph F).Adj v w}.ncard = 2 := by
  obtain ⟨a, c, hc, hl, hs⟩ := D.translated_cycle g
  have hvc : v ∈ c.support := by change v ∈ {w | w ∈ c.support}; rwa [hs]
  have hh := OctagonShortPaths.cycle_neighbors_two D.cycle_bound c hc hl v hvc
  have he : {w | w ∈ c.support ∧ (graph F).Adj v w} =
      {w | w ∈ g • apartment T F ∧ (graph F).Adj v w} := by
    ext w
    change (w ∈ {w | w ∈ c.support} ∧ (graph F).Adj v w) ↔
      (w ∈ g • apartment T F ∧ (graph F).Adj v w)
    rw [hs]
  rwa [he] at hh

/-- The first and last edges force the whole nonbacktracking nine-walk into one apartment. -/
theorem nine_walk_in_apartment {u : CosetGeometry.Vertex F}
    (p : BasedWalk (graph F) 9 u) (hp : p.Nonbacktracking) :
    ∃ g : X, ∀ v ∈ p.vertices, v ∈ g • apartment T F := by
  obtain ⟨g, hu, hfirst, hlast, hend⟩ := exists_apartment_for_edges F T D.borel_le
    p.1.property p.adj_penultimate_endpoint
  let r := p.2.take 7 (by decide)
  have hr : r.Nonbacktracking := BasedWalk.nonbacktracking_take (by decide) p.2 hp.2
  have hrpath := OctagonShortPaths.isPath_of_nonbacktracking D.cycle_bound r hr (by decide)
  have hrend : r.endpoint = p.penultimate := BasedWalk.endpoint_take_penultimate p.2
  obtain ⟨a, c, hc, hl, hs⟩ := D.translated_cycle g
  have hsub : r.toWalk.support ⊆ c.support :=
    OctagonShortPaths.short_path_support_subset D.cycle_bound c hl hrpath
      (by rw [BasedWalk.length_toWalk])
      (by change (p.1 : CosetGeometry.Vertex F) ∈ {w | w ∈ c.support}; rwa [hs])
      (by
        change r.endpoint ∈ {w | w ∈ c.support}
        rw [hs, hrend]
        exact hlast)
  have hmiddle : ∀ v ∈ r.vertices, v ∈ g • apartment T F := by
    intro v hv
    have hvc : v ∈ c.support := hsub (by rwa [BasedWalk.support_toWalk])
    change v ∈ g • apartment T F
    rw [← hs]
    exact hvc
  have hvertices : p.vertices = u :: (r.vertices ++ [p.endpoint]) :=
    congrArg (List.cons u) (BasedWalk.vertices_eq_prefix_append_endpoint p.2)
  refine ⟨g, ?_⟩
  intro v hv
  rw [hvertices] at hv
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | hv | rfl
  · exact hu
  · exact hmiddle v hv
  · exact hend

/-- Normalize the first edge while keeping every original walk vertex in the apartment. -/
theorem normalize_nine_walk {u : CosetGeometry.Vertex F}
    (p : BasedWalk (graph F) 9 u) (hp : p.Nonbacktracking) :
    ∃ g : X, g • CosetGeometry.base F u.type = u ∧
      g • CosetGeometry.base F (p.1 : CosetGeometry.Vertex F).type = p.1 ∧
      ∀ v ∈ p.vertices, g⁻¹ • v ∈ apartment T F := by
  obtain ⟨a, ha⟩ := D.nine_walk_in_apartment p hp
  have ha' : ∀ v ∈ p.vertices, a⁻¹ • v ∈ apartment T F := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp (ha v hv)
    simpa only [inv_smul_smul] using hw
  have hu : a⁻¹ • u ∈ apartment T F := ha' u (by simp only [BasedWalk.vertices, List.mem_cons, true_or])
  have hfirst : a⁻¹ • (p.1 : CosetGeometry.Vertex F) ∈ apartment T F := ha' p.1 (by
    change (p.1 : CosetGeometry.Vertex F) ∈ u :: p.1.val :: _
    simp only [List.mem_cons, true_or, or_true])
  have hadj := (smulHom F a⁻¹).map_rel p.1.property
  have hdegree : ∀ v ∈ apartment T F,
      {w | w ∈ apartment T F ∧ (graph F).Adj v w}.ncard = 2 := by
    simpa only [one_smul] using D.apartment_neighbors_two (1 : X)
  obtain ⟨n, hnu, hnp⟩ := D.normalizer_edge_representative hdegree hu hfirst hadj
  simp only [CosetGeometry.smul_type] at hnu hnp
  refine ⟨a * (n : X), ?_, ?_, ?_⟩
  · rw [mul_smul, hnu, smul_inv_smul]
  · rw [mul_smul, hnp, smul_inv_smul]
  · intro v hv
    simpa only [mul_inv_rev, mul_smul, Subgroup.coe_inv] using
      normalizer_mem_apartment n⁻¹ (ha' v hv)

private theorem opposite_types_eq {i j k : I} (hi : i ≠ j) (hk : i ≠ k) : j = k := by
  apply D.typeEquiv.injective
  have h1 := D.typeEquiv.injective.ne hi
  have h2 := D.typeEquiv.injective.ne hk
  cases he : D.typeEquiv i <;> cases hj : D.typeEquiv j <;>
    cases hk' : D.typeEquiv k <;> simp_all

/-- The original action is rooted nine-path transitive at every vertex, of either type. -/
theorem rootPathTransitive_nine (u : CosetGeometry.Vertex F) :
    RootPathTransitive (graph F) X u 9 := by
  intro p q hp hq
  obtain ⟨a, ha0, ha1, ha⟩ := D.normalize_nine_walk p hp
  obtain ⟨b, hb0, hb1, hb⟩ := D.normalize_nine_walk q hq
  let g := b * a⁻¹
  have hgu : g • u = u := by
    have hi := congrArg (fun v => a⁻¹ • v) ha0
    rw [inv_smul_smul] at hi
    change (b * a⁻¹) • u = u
    rw [mul_smul, ← hi, hb0]
  have ht : (p.1 : CosetGeometry.Vertex F).type = (q.1 : CosetGeometry.Vertex F).type :=
    D.opposite_types_eq p.1.property.1 q.1.property.1
  have hgfirst : g • (p.1 : CosetGeometry.Vertex F) = q.1 := by
    have hi := congrArg (fun v => a⁻¹ • v) ha1
    rw [inv_smul_smul] at hi
    change (b * a⁻¹) • (p.1 : CosetGeometry.Vertex F) = q.1
    rw [mul_smul, ← hi, ht, hb1]
  have hgraph : GraphAction (graph F) X := ⟨by
    intro a x y h
    exact ⟨h.1, h.2.smul F a⟩⟩
  have hmap : (p.map (smulHom F g)).Nonbacktracking :=
    (hgraph.nonbacktracking_map_iff g p).mpr hp
  have hpA : ∀ v ∈ (p.map (smulHom F g)).vertices, v ∈ b • apartment T F := by
    intro v hv
    rw [BasedWalk.vertices_map, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨a⁻¹ • w, ha w hw, (mul_smul b a⁻¹ w).symm⟩
  have hqA : ∀ v ∈ q.vertices, v ∈ b • apartment T F := by
    intro v hv
    exact ⟨b⁻¹ • v, hb v hv, smul_inv_smul b v⟩
  have he := BasedWalk.vertices_eq_of_first_of_two_neighbors (b • apartment T F)
    (D.apartment_neighbors_two b) (p.map (smulHom F g)) q hgu hmap hq hpA hqA hgfirst
  exact ⟨g, hgu, he⟩

end OctagonalDatum
end Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
