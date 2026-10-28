module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.NativeCubic
public import Theory.SpecificGroups.PSL3.SmallCompletion.NativePaths
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth
public import Theory.GroupAction.DihedralPolygon
public import Theory.GroupAction.RankTwoCosetCover.SmallCover

/-!
# Geometry of faithful native linear-three completions

The paired completion transfers rooted four-path transitivity from the
concrete flag graph to every faithful completion with whole overlap.
Thickness then excludes short cycles. Two endpoint involutions whose product
has cube in the whole middle give an actual hexagon: the cube fixes both
base vertices, which is exactly the dihedral polygon construction's premise.
Four-path transitivity makes every four-path have a two-edge shortcut and
therefore bounds the diameter by three.

This supplies the small-cover argument for the exact native lift. It does
not identify a general completion with a projective matrix group.
Source: Aschbacher–Smith F.3.3–6, F.4.5–8, F.4.49, printed pp.270–278,
298–299 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Matrix Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.SmallCompletion
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
variable (F : Type*) [Field F] [Finite F]
local notation "α" => GreenBook.LieModels.LinearThree.amalgam F
abbrev NativeCompletion (G : Type*) [Group G] := RankTwoAmalgam.FaithfulCompletion α (G := G)

theorem model_family : (modelCompletion F).cosetFamily = parabolic F := by
  funext i
  cases i
  · exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range _ _ _ _ _ _
  · exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range _ _ _ _ _ _

namespace NativeCompletion
variable {F} {G H : Type*} [Group G] [Group H]
variable (c : NativeCompletion F G) (d : NativeCompletion F H)
abbrev family := c.cosetFamily
abbrev Vertex := RankTwo.Vertex c.family
abbrev graph := RankTwo.graph c.family
omit [Finite F] in
@[simp] theorem family_false : c.family false = c.left.range := rfl
omit [Finite F] in
@[simp] theorem family_true : c.family true = c.right.range := rfl

omit [Finite F] in
theorem connected : c.graph.Connected := RankTwo.connected c.family c.generated

omit [Finite F] in
theorem pair_overlap (ho : c.left.range ⊓ c.right.range = c.middle.range) :
    (c.pairCompletion d).left.range ⊓ (c.pairCompletion d).right.range =
      (c.pairCompletion d).middle.range := by
  let z := c.pairCompletion d
  apply le_antisymm _ (le_inf z.middle_le_left z.middle_le_right)
  rintro a ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  have hxy : c.left x=c.right y := by
    have he := congrArg (c.pairFst d) (hx.trans hy.symm)
    simpa only [z,RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using he
  obtain ⟨b,hb⟩ := ho.le
    (show c.left x ∈ c.left.range ⊓ c.right.range from ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩)
  have hbx : (GreenBook.LieModels.LinearThree.amalgam F).left b = x := c.left_injective hb
  refine ⟨b,?_⟩
  change z.left _ = a
  rw [hbx]
  exact hx

omit [Finite F] in
theorem rootPathTransitive_transfer
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hd : d.left.range ⊓ d.right.range = d.middle.range) (i : Bool) (n : ℕ)
    (h : RootPathTransitive c.graph G (RankTwo.base c.family i) n) :
    RootPathTransitive d.graph H (RankTwo.base d.family i) n := by
  have hpair := c.pair_overlap d hc
  have c₁ : CoverData (c.pairCompletion d).cosetFamily c.cosetFamily (c.pairFst d) := by
    apply RankTwoAmalgam.FaithfulCompletion.coverData_of_hom
    · ext x; exact c.pairFst_left d x
    · ext x; exact c.pairFst_right d x
    · exact hpair
    · exact hc
  have c₂ : CoverData (c.pairCompletion d).cosetFamily d.cosetFamily (c.pairSnd d) := by
    apply RankTwoAmalgam.FaithfulCompletion.coverData_of_hom
    · ext x; exact c.pairSnd_left d x
    · ext x; exact c.pairSnd_right d x
    · exact hpair
    · exact hd
  have h' : RootPathTransitive c.graph G (c₁.vertex (RankTwo.base (c.pairCompletion d).cosetFamily i)) n := by
    simpa only [CoverData.vertex_base] using h
  simpa only [CoverData.vertex_base] using
    c₁.transport_rootPathTransitive c₂ n (RankTwo.base (c.pairCompletion d).cosetFamily i) h'


theorem endpoint_card {n : ℕ} (hF : Nat.card F=2^n) (i : Bool) :
    Nat.card (c.family i) = (Nat.card F+1)*Nat.card F^3 * Nat.card (CartanActions.torus F) := by
  have h := card_parabolic F hF i
  cases i
  · exact c.left_card.trans h
  · exact c.right_card.trans h

theorem middle_relIndex {n : ℕ} (hF : Nat.card F=2^n) (i : Bool) :
    c.middle.range.relIndex (c.family i) = Nat.card F+1 := by
  have hle : c.middle.range ≤ c.family i := by
    cases i
    · exact c.middle_le_left
    · exact c.middle_le_right
  have h := (c.middle.range.subgroupOf (c.family i)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,c.middle_card,
    card_borel F hF,c.endpoint_card hF] at h
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F^3 * Nat.card (CartanActions.torus F) from Nat.mul_pos (pow_pos Nat.card_pos _) Nat.card_pos)
  change _ * (c.middle.range.subgroupOf (c.family i)).index = _
  rw [h]
  ring

theorem neighbor_index (ho : c.left.range ⊓ c.right.range = c.middle.range) {n : ℕ} (hF : Nat.card F=2^n) (i : Bool) :
    ((c.family (!i)).subgroupOf (c.family i)).index = Nat.card F+1 := by
  have hi : c.family (!i) ⊓ c.family i = c.middle.range := by
    cases i
    · exact (inf_comm _ _).trans ho
    · exact ho
  have hh : (c.family (!i)).subgroupOf (c.family i) =
      c.middle.range.subgroupOf (c.family i) := by
    rw [←hi]
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h,g.property⟩,fun h => h.1⟩
  rw [hh]
  exact c.middle_relIndex hF i

theorem card_neighbors (ho : c.left.range ⊓ c.right.range = c.middle.range) {n : ℕ} (hF : Nat.card F=2^n) (v : c.Vertex) :
    Nat.card (c.graph.neighborSet v) = Nat.card F+1 :=
  card_neighbors_of_indices c.family (fun _ => Nat.card F+1) (c.neighbor_index ho hF) v

omit [Finite F] in
theorem graphAction : GraphAction c.graph G where
  map_adj g := (translationGraphIso c.family g).toHom.map_adj

variable [CharP F 2]

theorem four_transitive (ho : c.left.range ⊓ c.right.range = c.middle.range) {n : ℕ} (hF : Nat.card F=2^n) (v : c.Vertex) :
    RootPathTransitive c.graph G v 4 := by
  have ht : RootPathTransitive (RankTwo.graph (modelCompletion F).cosetFamily) PSL(3,F)
      (RankTwo.base (modelCompletion F).cosetFamily v.type) 4 := by
    rw [model_family]
    exact NativePaths.four_path_transitive F hF v.type
  have hb := rootPathTransitive_transfer (modelCompletion F) c (model_overlap F) ho v.type 4 ht
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


end NativeCompletion
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
