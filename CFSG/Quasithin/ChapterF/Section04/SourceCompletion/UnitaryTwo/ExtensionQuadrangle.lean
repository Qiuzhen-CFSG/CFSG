module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ExtensionShortPaths
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.QuadrangleRecognition
public import Theory.GroupAction.DihedralPolygon
/-!
# The order-four criterion for the doubled unitary coset quadrangle

The local two-path census gives eleven distinct plane cosets. The endpoint
orders force their number to be a multiple of three, so a distance-four
witness exists. Five-path transitivity then excludes cycles below eight.
The two specified endpoint involutions construct an actual eight-cycle;
its complementary three-arcs force diameter four.

This is the finite binary unitary specialization of Aschbacher--Smith F.4.26,
printed p.288, retaining the literal endpoint and overlap images.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Extension.Completion
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open QuadrangleRecognition
variable {G : Type*} [Group G] (c : Completion G)

private theorem two_endpoint_injective (x : c.Point)
    (p q : BasedWalk c.graph 2 x.val) (hp : p.Nonbacktracking) (hq : q.Nonbacktracking)
    (he : p.endpoint=q.endpoint) : p=q := by
  have hpp := isPath_of_nonbacktracking_of_cycle_bound c.cycle_length_gt_five p hp (by decide : 2≤5)
  have hqp := isPath_of_nonbacktracking_of_cycle_bound c.cycle_length_gt_five q hq (by decide : 2≤5)
  let r := q.toWalk.copy rfl he.symm
  have hrp : r.IsPath := by simpa only [r,Walk.isPath_copy] using hqp
  have hw : p.toWalk=r := by
    by_contra hh
    obtain ⟨v,_,_,s,hs,hlen⟩ := hpp.exists_isCycle_length_le_add_of_ne hrp hh
    have hb := c.cycle_length_gt_five v s hs
    simp only [r,Walk.length_copy,BasedWalk.length_toWalk] at hlen
    omega
  apply BasedWalk.vertices_injective 2 x.val
  have hh := congrArg Walk.support hw
  simpa only [r,Walk.support_copy,BasedWalk.support_toWalk] using hh

private theorem eleven_le_card_point [Finite G] : 11≤Nat.card c.Point := by
  let x : c.Point := ⟨RankTwo.base c.family true,rfl⟩
  let W := {p : BasedWalk c.graph 2 x.val // p.Nonbacktracking}
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [c.card_two_paths x]; decide)
  let f : Option W → c.Point := fun w => match w with
    | none => x
    | some p => ⟨p.val.endpoint,by
        have hcolor : ∀ {u v : c.Vertex}, c.graph.Adj u v → u.type≠v.type := fun h => h.1
        have hh := even_length_iff (fun v : c.Vertex => v.type) hcolor p.val.toWalk
        exact ((hh.mp (by simp only [BasedWalk.length_toWalk]; decide)).symm).trans x.property⟩
  have hf : Function.Injective f := by
    intro a b he
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some q => exact (q.property.1 (congrArg Subtype.val he).symm).elim
    | some p =>
      cases b with
      | none => exact (p.property.1 (congrArg Subtype.val he)).elim
      | some q =>
        exact congrArg some (Subtype.ext (two_endpoint_injective c x p.val q.val
          p.property q.property (congrArg Subtype.val he)))
  have hh := Nat.card_le_card_of_injective f hf
  have hw : Nat.card (Option W)=11 := by
    let := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card,Fintype.card_option,←Nat.card_eq_fintype_card]
    change Nat.card {p : BasedWalk c.graph 2 x.val // p.Nonbacktracking}+1=11
    rw [c.card_two_paths x]
  exact hw ▸ hh

theorem twelve_le_card_point [Finite G] : 12≤Nat.card c.Point := by
  have hpoint : Nat.card c.Point=c.right.range.index := by
    rw [Nat.card_congr (c.fiberEquiv true),←Subgroup.index_eq_card]
    rfl
  have hc := c.right.range.card_mul_index
  rw [c.right_card,←hpoint] at hc
  obtain ⟨k,hk⟩ := c.order_multiple
  have hlo := eleven_le_card_point c
  omega

theorem exists_distance_four [Finite G] :
    ∃ y,c.graph.dist (RankTwo.base c.family true) y=4 := by
  let x : c.Point := ⟨RankTwo.base c.family true,rfl⟩
  have : Finite {p : BasedWalk c.graph 2 x.val // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [c.card_two_paths x]; decide)
  exact exists_distance_four_of_card c.connected (·.type) (fun h => h.1) x.val (by
    change 1+Nat.card {p : BasedWalk c.graph 2 x.val // p.Nonbacktracking}<Nat.card c.Point
    rw [c.card_two_paths x]
    have hh := c.twelve_le_card_point
    omega)

theorem cycle_length_ge_eight [Finite G] (v : c.Vertex) (p : c.graph.Walk v v)
    (hp : p.IsCycle) : 8≤p.length := by
  obtain ⟨y,hy⟩ := c.exists_distance_four
  exact cycle_bound_of_distance_four c.graphAction c.connected c.hasTwoNeighbors c.five_transitive
    (·.type) (fun h => h.1) (fun h => (same_orbit_iff c.family _ _).mpr h) hy v p hp

theorem uniqueGeodesicsBelow_four [Finite G] : c.graph.UniqueGeodesicsBelow 4 := by
  intro x y p q hp hq hd
  by_contra hh
  obtain ⟨v,_,_,r,hr,hlen⟩ := (p.isPath_of_length_eq_dist hp).exists_isCycle_length_le_add_of_ne
    (q.isPath_of_length_eq_dist hq) hh
  have hb := c.cycle_length_ge_eight v r hr
  omega

def bipartiteAction : GroupAction.DihedralPolygon.BipartiteAction G c.graph where
  color := (·.type)
  adjacent_color h := h.1
  smul_adj := c.graphAction.map_adj
  smul_color _ _ := rfl

theorem exists_eight_cycle_of_involutions [Finite G] (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^4=1) :
    ∃v,∃p : c.graph.Walk v v,p.IsCycle ∧ p.length=8 := by
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
    exact hsout (c.overlap ▸ show s∈c.left.range⊓c.right.range from ⟨hs,hh'⟩)
  have htx : t • RankTwo.base c.family false≠RankTwo.base c.family false := by
    intro hh
    have hh' : t∈c.left.range := by
      change t∈stabilizer c.family (RankTwo.base c.family false) at hh
      simpa only [stabilizer,RankTwo.base,stabilizer_base,family_false] using hh
    exact htout (c.overlap ▸ show t∈c.left.range⊓c.right.range from ⟨hh',ht⟩)
  let e : cycleGraph 8 ↪g c.graph := GroupAction.DihedralPolygon.edgeEmbedding c.bipartiteAction
    (by decide : 1<4) c.uniqueGeodesicsBelow_four (by decide : 0<4) le_rfl
    ⟨Bool.false_ne_true,incident_base c.family false true⟩ hs2 ht2 hsx hsl htl htx
    (by rw [hst,one_smul]) (by rw [hst,one_smul])
  exact (cycleGraph_isContained_iff (by decide : 2<8)).mp ⟨e.toCopy⟩

theorem quadrangle_metric_of_involutions [Finite G] (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^4=1) :
    (∀v (p : c.graph.Walk v v),p.IsCycle → 8≤p.length) ∧
    (∀v w,c.graph.dist v w≤4) ∧
    (∃v,∃p : c.graph.Walk v v,p.IsCycle ∧ p.length=8) := by
  have hex := c.exists_eight_cycle_of_involutions s t hs ht hsout htout hs2 ht2 hst
  refine ⟨c.cycle_length_ge_eight,diameter_bound_of_five_endpoint_bound c.connected ?_,hex⟩
  intro v p hp
  exact five_endpoint_bound c.graphAction c.five_transitive (·.type) (fun h => h.1)
    (fun h => (same_orbit_iff c.family _ _).mpr h) hex p hp
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Extension.Completion
