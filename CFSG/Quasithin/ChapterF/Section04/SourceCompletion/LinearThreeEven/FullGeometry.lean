module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.Basic
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.NativeGeometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Counts
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupAction.RankTwoCosetGeometry.ProjectivePlane

/-!
# Full-extension geometry and order from the source apartment witness

The whole middle supplements the native group, so the full extension has
exactly the native typed flag graph. The native four-path action transfers
to every faithful completion with whole overlap, retaining all outer factors.
The source cube-in-middle relation constructs a hexagon and forces diameter
three. Counting the literal point and line cosets gives q² + q + 1 of each;
cancelling the unchanged endpoint order proves equality of FULL carrier orders.

This proves the metric and order parts of the source recognition route.
Identification of the resulting group with an automorphism extension remains
a separate obligation; plane order alone is not used as recognition.
Source: Aschbacher–Smith F.4.3–8 and F.4.49, pp.274–278,298–299
(`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Matrix Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.SmallCompletion
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
variable (F : Type*) [Field F] [Finite F]

omit [Finite F] in
theorem native_conj_injective : Function.Injective (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)) := by
  let _ : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let _ : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  apply Theory.GroupTheory.conj_injective_of_center_eq_bot
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center PSL(3,F)) inferInstance).resolve_right
    (fun h => Group.IsPerfect.not_isMulCommutative PSL(3,F) (center_eq_top_iff.mp h))

variable [CharP F 2]
private theorem native_diameter {n : ℕ} (hF : Nat.card F=2^n) :
    ∀ v w : NativeCompletion.Vertex (modelCompletion F),
      (NativeCompletion.graph (modelCompletion F)).dist v w ≤ 3 := by
  let c := modelCompletion F
  let x : pointParabolic F := ⟨reflection F false,reflection_mem F false⟩
  let y : lineParabolic F := ⟨reflection F true,reflection_mem F true⟩
  have hsout : c.left x ∉ c.middle.range := by
    rintro ⟨b,hb⟩
    have he : b.val = reflection F false := hb
    exact reflection_not_mem_borel F false (he ▸ b.property)
  have htout : c.right y ∉ c.middle.range := by
    rintro ⟨b,hb⟩
    have he : b.val = reflection F true := hb
    exact reflection_not_mem_borel F true (he ▸ b.property)
  have hcube : (c.left x*c.right y)^3 ∈ c.middle.range := by
    have h : (c.left x*c.right y)^3=1 := by
      change (reflection F false * reflection F true)^3=1
      simpa only [map_one,one_mul,Bool.not_false] using twisted_reflections_cube F false 1 1
    rw [h]
    exact one_mem _
  have hex := NativeCompletion.exists_six_cycle_of_involutions c (model_overlap F) hF
    (c.left x) (c.right y) ⟨x,rfl⟩ ⟨y,rfl⟩ hsout htout
    (reflection_sq F false) (reflection_sq F true) hcube
  exact NativeCompletion.diameter_le_three_of_six_cycle c (model_overlap F) hF hex

/-- The actual native inclusion completion has triangle diameter. -/
theorem native_model_diameter {n : ℕ} (hF : Nat.card F=2^n) :
    ∀ v w : NativeCompletion.Vertex (modelCompletion F),
      (NativeCompletion.graph (modelCompletion F)).dist v w ≤ 3 :=
  native_diameter F hF

/-- Each native point or line orbit has the projective-plane cardinality. -/
theorem native_coset_card {n : ℕ} (hF : Nat.card F=2^n) (i : Bool) :
    Nat.card (PSL(3,F) ⧸ parabolic F i) = Nat.card F^2+Nat.card F+1 := by
  let c := modelCompletion F
  have h := card_fiber_of_plane_geometry c.cosetFamily c.generated
    (NativeCompletion.uniqueGeodesicsBelow_three c (model_overlap F) hF)
    (native_diameter F hF) (Nat.card F)
    (NativeCompletion.card_neighbors c (model_overlap F) hF) i
  rw [Nat.card_congr (fiberEquivQuotient c.cosetFamily i)] at h
  change Nat.card (PSL(3,F) ⧸ (modelCompletion F).cosetFamily i) = _ at h
  rwa [model_family] at h

namespace Completion
variable {F} {E : SourceExtension F} {G : Type*} [Group G]
variable (c : Completion E G)
abbrev family := c.cosetFamily
abbrev Vertex := RankTwo.Vertex c.family
abbrev graph := RankTwo.graph c.family
omit [Finite F] [CharP F 2] in
@[simp] theorem family_false : c.family false = c.left.range := rfl
omit [Finite F] [CharP F 2] in
@[simp] theorem family_true : c.family true = c.right.range := rfl
omit [Finite F] [CharP F 2] in
theorem connected : c.graph.Connected := RankTwo.connected c.family c.generated
omit [Finite F] [CharP F 2] in
theorem graphAction : GraphAction c.graph G where
  map_adj g := (translationGraphIso c.family g).toHom.map_adj

omit [CharP F 2] in
theorem card_neighbors (ho : c.left.range ⊓ c.right.range = c.middle.range)
    {n : ℕ} (_hF : Nat.card F=2^n) (v : c.Vertex) :
    Nat.card (c.graph.neighborSet v) = Nat.card F+1 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.family v
  have hb := E.completion_card_neighbors_eq_native (native_conj_injective F)
    (parabolics_sup_eq_top F) c ho v.type
  have hv : Nat.card (c.graph.neighborSet (RankTwo.base c.family v.type)) = Nat.card F+1 :=
    hb.trans (NativePaths.card_neighbors F _)
  have hh := Nat.card_congr ((translationGraphIso c.family g).mapNeighborSet
    (RankTwo.base c.family v.type))
  change Nat.card (c.graph.neighborSet (RankTwo.base c.family v.type)) =
    Nat.card (c.graph.neighborSet (g • RankTwo.base c.family v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans hv

theorem four_transitive (ho : c.left.range ⊓ c.right.range = c.middle.range)
    {n : ℕ} (hF : Nat.card F=2^n) (v : c.Vertex) : RootPathTransitive c.graph G v 4 := by
  have hb := E.completion_rootPathTransitive_of_native (native_conj_injective F)
    (parabolics_sup_eq_top F) c ho v.type 4 (NativePaths.four_path_transitive F hF v.type)
  obtain ⟨g,hg⟩ := exists_smul_base c.family v
  simpa only [hg] using RootPathTransitive.smul c.graphAction hb g

omit [CharP F 2] in
theorem thick (ho : c.left.range ⊓ c.right.range = c.middle.range) {n : ℕ} (hF : Nat.card F=2^n) (v a b : c.Vertex) : ∃ z, c.graph.Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hc : 2 < Nat.card (c.graph.neighborSet v) := by
    rw [c.card_neighbors ho hF v]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    omega
  have : Finite (c.graph.neighborSet v) := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite (c.graph.neighborSet v)
  rw [Nat.card_eq_fintype_card] at hc
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hc
  by_contra hh
  push Not at hh
  have hx : x.val = a ∨ x.val = b := by
    by_cases ha : x.val = a
    · exact Or.inl ha
    · exact Or.inr (hh x.val x.property ha)
  have hy : y.val = a ∨ y.val = b := by
    by_cases ha : y.val = a
    · exact Or.inl ha
    · exact Or.inr (hh y.val y.property ha)
  have hz : z.val = a ∨ z.val = b := by
    by_cases ha : z.val = a
    · exact Or.inl ha
    · exact Or.inr (hh z.val z.property ha)
  have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val ≠ z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    rcases hz with hz | hz <;> simp_all



omit [CharP F 2] in
theorem hasTwoNeighbors (ho : c.left.range ⊓ c.right.range = c.middle.range) {n : ℕ} (hF : Nat.card F=2^n) : BasedWalk.HasTwoNeighbors c.graph := by
  intro v a
  obtain ⟨z,hz,hza,_⟩ := c.thick ho hF v a a
  exact ⟨z,hz,hza⟩


theorem cycle_length_gt_four (ho : c.left.range ⊓ c.right.range = c.middle.range) {n : ℕ} (hF : Nat.card F=2^n) (v : c.Vertex) (p : c.graph.Walk v v) (hp : p.IsCycle) :
    4 < p.length :=
  cycle_bound_of_root_transitivity c.graphAction (c.thick ho hF) (c.four_transitive ho hF) v p hp

theorem uniqueGeodesicsBelow_three (ho : c.left.range ⊓ c.right.range = c.middle.range) {n : ℕ} (hF : Nat.card F=2^n) : c.graph.UniqueGeodesicsBelow 3 := by
  intro x y p q hp hq hd
  by_contra hh
  obtain ⟨v,_,_,r,hr,hlen⟩ := (p.isPath_of_length_eq_dist hp).exists_isCycle_length_le_add_of_ne
    (q.isPath_of_length_eq_dist hq) hh
  have hb := c.cycle_length_gt_four ho hF v r hr
  omega

def bipartiteAction : GroupAction.DihedralPolygon.BipartiteAction G c.graph where
  color := (·.type)
  adjacent_color h := h.1
  smul_adj := c.graphAction.map_adj
  smul_color _ _ := rfl

theorem exists_six_cycle_of_involutions (ho : c.left.range ⊓ c.right.range = c.middle.range) {n : ℕ} (hF : Nat.card F=2^n) (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^3 ∈ c.middle.range) :
    ∃v,∃p : c.graph.Walk v v,p.IsCycle ∧ p.length=6 := by
  have hsx : s • RankTwo.base c.family false=RankTwo.base c.family false := by
    change s∈stabilizer c.family (RankTwo.base c.family false)
    simpa only [stabilizer,RankTwo.base,stabilizer_base,family_false] using hs
  have htl : t • RankTwo.base c.family true=RankTwo.base c.family true := by
    change t∈stabilizer c.family (RankTwo.base c.family true)
    simpa only [stabilizer,RankTwo.base,stabilizer_base,family_true] using ht
  have hsl : s • RankTwo.base c.family true≠RankTwo.base c.family true := by
    intro hh
    have hh' : s∈c.right.range := by
      change s∈stabilizer c.family (RankTwo.base c.family true) at hh
      simpa only [stabilizer,RankTwo.base,stabilizer_base,family_true] using hh
    exact hsout (ho ▸ show s∈c.left.range⊓c.right.range from ⟨hs,hh'⟩)
  have htx : t • RankTwo.base c.family false≠RankTwo.base c.family false := by
    intro hh
    have hh' : t∈c.left.range := by
      change t∈stabilizer c.family (RankTwo.base c.family false) at hh
      simpa only [stabilizer,RankTwo.base,stabilizer_base,family_false] using hh
    exact htout (ho ▸ show t∈c.left.range⊓c.right.range from ⟨hh',ht⟩)
  let e : cycleGraph 6 ↪g c.graph := GroupAction.DihedralPolygon.edgeEmbedding c.bipartiteAction
    (by decide : 1<3) (c.uniqueGeodesicsBelow_three ho hF) (by decide : 0<3) le_rfl
    ⟨Bool.false_ne_true,incident_base c.family false true⟩ hs2 ht2 hsx hsl htl htx
    (by
      change (s*t)^3 ∈ stabilizer c.family (RankTwo.base c.family false)
      simpa only [stabilizer,RankTwo.base,stabilizer_base,family_false] using c.middle_le_left hst)
    (by
      change (s*t)^3 ∈ stabilizer c.family (RankTwo.base c.family true)
      simpa only [stabilizer,RankTwo.base,stabilizer_base,family_true] using c.middle_le_right hst)
  exact (cycleGraph_isContained_iff (by decide : 2<6)).mp ⟨e.toCopy⟩

omit [CharP F 2] [Finite F] in
private theorem four_prefix_of_cycle {v : c.Vertex} (r : c.graph.Walk v v)
    (hr : r.IsCycle) (hlen : r.length = 6) :
    ∃ p : BasedWalk c.graph 4 v, p.Nonbacktracking ∧ c.graph.dist v p.endpoint ≤ 2 := by
  have hl : (r.take 4).length = 4 := by rw [Walk.take_length, hlen]; rfl
  let p : BasedWalk c.graph 4 v := hl ▸ BasedWalk.ofWalk (r.take 4)
  refine ⟨p, (BasedWalk.nonbacktracking_cast hl _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hr.isPath_take (by omega))), ?_⟩
  have hd := SimpleGraph.dist_le (r.drop 4).reverse
  rw [Walk.length_reverse, Walk.drop_length, hlen] at hd
  simpa only [p, BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk] using hd

omit [CharP F 2] [Finite F] in
private theorem short_four_walk
    (hex : ∃ v, ∃ r : c.graph.Walk v v, r.IsCycle ∧ r.length = 6) (u : c.Vertex) :
    ∃ p : BasedWalk c.graph 4 u, p.Nonbacktracking ∧ c.graph.dist u p.endpoint ≤ 2 := by
  classical
  obtain ⟨v,r,hr,hl⟩ := hex
  have hsame : ∃ w : c.Vertex, w.type = u.type ∧
      ∃ d : c.graph.Walk w w, d.IsCycle ∧ d.length = 6 := by
    by_cases hv : v.type = u.type
    · exact ⟨v,hv,r,hr,hl⟩
    · have hn := (r.adj_snd hr.not_nil).1
      have hs : r.snd.type = u.type := by
        cases h1 : v.type <;> cases h2 : r.snd.type <;> cases h3 : u.type <;> simp_all
      have hm : r.snd ∈ r.support := r.getVert_mem_support 1
      exact ⟨r.snd,hs,r.rotate r.snd hm,hr.rotate hm,by simpa using hl⟩
  obtain ⟨w,hw,d,hd,hdl⟩ := hsame
  obtain ⟨p,hp,hpd⟩ := four_prefix_of_cycle c d hd hdl
  obtain ⟨a,rfl⟩ := (same_orbit_iff c.family w u).mpr hw
  refine ⟨p.map (c.graphAction.hom a), (c.graphAction.nonbacktracking_map_iff a p).mpr hp, ?_⟩
  have he : (p.map (c.graphAction.hom a)).endpoint = a • p.endpoint :=
    BasedWalk.endpoint_map (c.graphAction.hom a) p
  exact (congrArg (c.graph.dist (a • w)) he).le.trans
    ((c.graphAction.dist_smul a w p.endpoint).le.trans hpd)

theorem diameter_le_three_of_six_cycle (ho : c.left.range ⊓ c.right.range = c.middle.range) {n : ℕ} (hF : Nat.card F=2^n)
    (hex : ∃ v, ∃ r : c.graph.Walk v v, r.IsCycle ∧ r.length = 6)
    (v w : c.Vertex) : c.graph.dist v w ≤ 3 := by
  have hshort (u : c.Vertex) (p : BasedWalk c.graph 4 u) (hp : p.Nonbacktracking) :
      c.graph.dist u p.endpoint ≤ 2 := by
    obtain ⟨q,hq,hqd⟩ := short_four_walk c hex u
    exact ((c.four_transitive ho hF u).distance_eq c.graphAction p q hp hq).le.trans hqd
  by_contra hn
  obtain ⟨p,hp,hl⟩ := c.connected.exists_path_of_dist v w
  have hlen : (p.take 4).length = 4 := by
    rw [Walk.take_length,hl,Nat.min_eq_left (by omega)]
  let q : BasedWalk c.graph 4 v := hlen ▸ BasedWalk.ofWalk (p.take 4)
  have hq : q.Nonbacktracking := (BasedWalk.nonbacktracking_cast hlen _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hp.take 4))
  have hd := hshort v q hq
  have hgeo := length_eq_dist_of_subwalk hl (p.isSubwalk_take 4)
  have hqend : q.endpoint = p.getVert 4 := by
    simp only [q,BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]
  rw [hqend,←hgeo,hlen] at hd
  omega


/-- The actual source cube-in-middle witness gives the full triangle geometry. -/
theorem smallness_of_cube_mem_middle
    (ho : c.left.range ⊓ c.right.range = c.middle.range)
    {n : ℕ} (hF : Nat.card F=2^n) (s t : G)
    (hs : s ∈ c.left.range) (ht : t ∈ c.right.range)
    (hsout : s ∉ c.middle.range) (htout : t ∉ c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hcube : (s*t)^3 ∈ c.middle.range) :
    c.graph.UniqueGeodesicsBelow 3 ∧ (∀ v w, c.graph.dist v w ≤ 3) ∧
      (∀ v, Nat.card (c.graph.neighborSet v) = Nat.card F+1) := by
  have hex := c.exists_six_cycle_of_involutions ho hF s t hs ht hsout htout hs2 ht2 hcube
  exact ⟨c.uniqueGeodesicsBelow_three ho hF,c.diameter_le_three_of_six_cycle ho hF hex,
    c.card_neighbors ho hF⟩

variable [Finite G]

/-- The source apartment forces the FULL carrier order, including all outer factors. -/
theorem card_eq_extension_of_cube_mem_middle
    (ho : c.left.range ⊓ c.right.range = c.middle.range)
    {n : ℕ} (hF : Nat.card F=2^n) (s t : G)
    (hs : s ∈ c.left.range) (ht : t ∈ c.right.range)
    (hsout : s ∉ c.middle.range) (htout : t ∉ c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hcube : (s*t)^3 ∈ c.middle.range) :
    Nat.card G = Nat.card E.carrier := by
  obtain ⟨hu,hd,hv⟩ := c.smallness_of_cube_mem_middle ho hF s t hs ht hsout htout hs2 ht2 hcube
  have hc := card_fiber_of_plane_geometry c.family c.generated hu hd (Nat.card F) hv false
  rw [Nat.card_congr (fiberEquivQuotient c.family false)] at hc
  have he : Nat.card (E.carrier ⧸ E.family false) = Nat.card F^2+Nat.card F+1 :=
    (E.card_coset_eq_native (native_conj_injective F) false).trans (native_coset_card F hF false)
  have hl : Nat.card (c.family false) = Nat.card (E.family false) :=
    c.left_card.trans (Nat.card_congr (subgroupOfEquivOfLe E.left_le).toEquiv).symm
  rw [←(c.family false).index_mul_card,←(E.family false).index_mul_card,
    index_eq_card,index_eq_card,hc,he,hl]

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
