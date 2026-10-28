module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Hexagon
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Order comparison forces a hexagon in the binary triality completion

The 4,608 nonbacktracking six-paths from an arms vertex have endpoints among
819 vertices of that type when the completion has at most the native order.
If there were no twelve-cycle, girth at least twelve would make this endpoint
map injective. Seven-path transitivity then gives diameter at most six.
Source: Aschbacher--Smith F.4.12--13,24,43, pp.280,287,296.
-/
public noncomputable section
open Subgroup
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
variable {G : Type*} [Group G] (c : Completion G)

private theorem six_endpoint_injective {V : Type*} {Γ : SimpleGraph V}
    (hg : ∀ v (p : Γ.Walk v v), p.IsCycle → 12 < p.length) (x : V) :
    Function.Injective (fun p : {p : BasedWalk Γ 6 x // p.Nonbacktracking} => p.val.endpoint) := by
  intro p q he
  have hp := isPath_of_nonbacktracking_of_cycle_bound hg p.val p.property (by decide : 6≤12)
  have hq := isPath_of_nonbacktracking_of_cycle_bound hg q.val q.property (by decide : 6≤12)
  have hw : p.val.toWalk = q.val.toWalk.copy rfl he.symm := by
    by_contra hne
    obtain ⟨v,_,_,r,hr,hlen⟩ := hp.exists_isCycle_length_le_add_of_ne
      ((Walk.isPath_copy _ rfl he.symm).mpr hq) hne
    have hh := hg v r hr
    simp only [Walk.length_copy,BasedWalk.length_toWalk] at hlen
    omega
  apply Subtype.ext
  apply BasedWalk.vertices_injective
  simpa only [Walk.support_copy,BasedWalk.support_toWalk] using congrArg Walk.support hw

private def typedEquiv (i : Bool) :
    {v : c.Vertex // v.type=i} ≃ (G ⧸ c.family i) where
  toFun v := v.property ▸ v.val.coset
  invFun a := ⟨⟨i,a⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,a⟩,h⟩; dsimp at h; subst j; rfl
  right_inv := by intro a; rfl

theorem six_path_card (x : c.Vertex) :
    Nat.card {p : BasedWalk c.graph 6 x // p.Nonbacktracking} =
      if x.type then 6144 else 4608 := by
  have hf : ∀ {x y : c.Vertex}, c.graph.Adj x y → y.type = !x.type := by
    intro x y h
    have hxy := h.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  have hh := BasedWalk.card_nonbacktracking_succ c.graph (fun x : c.Vertex => x.type)
    NativeSeven.degree hf c.card_neighbors 5 x
  cases hx : x.type <;>
    simpa only [hx,Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,
      BasedWalk.forwardCount,NativeSeven.degree] using hh

theorem exists_twelve_cycle_of_order_bound [Finite G]
    (horder : Nat.card G ≤ Nat.card Model) :
    ∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=12 := by
  classical
  by_contra hno
  have hg (v : c.Vertex) (p : c.graph.Walk v v) (hp : p.IsCycle) : 12<p.length := by
    have hle := c.cycle_length_ge_twelve v p hp
    have hne : p.length≠12 := fun hh => hno ⟨v,p,hp,hh⟩
    omega
  let x := RankTwo.base c.family false
  let f : {p : BasedWalk c.graph 6 x // p.Nonbacktracking} →
      {v : c.Vertex // v.type=false} := fun p =>
    ⟨p.val.endpoint, ((QuadrangleRecognition.even_length_iff (G := c.graph) (·.type)
      (fun h => h.1) p.val.toWalk).mp
        (by simp only [BasedWalk.length_toWalk]; decide)).symm⟩
  let : Finite {v : c.Vertex // v.type=false} := Finite.of_equiv
    (G ⧸ c.family false) (typedEquiv c false).symm
  have hi : Function.Injective f := fun p r h =>
    six_endpoint_injective hg x (congrArg Subtype.val h)
  have hcount := Nat.card_le_card_of_injective f hi
  rw [c.six_path_card,Nat.card_congr (typedEquiv c false)] at hcount
  change 4608 ≤ c.left.range.index at hcount
  have hmodel : Nat.card Model = 211341312 := by
    rw [_root_.Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier 1 Nat.zero_lt_one]
    change Nat.card (_root_.Triality.Standard.Parabolics.borel parameters) * _ = _
    rw [borel_card]
    norm_num [parameters,_root_.Triality.Standard.Parameters.q,_root_.Triality.Standard.binaryParameters]
  rw [hmodel] at horder
  have hh := c.left.range.card_mul_index
  rw [c.left_card] at hh
  omega

theorem hexagon_metric_of_order_bound [Finite G]
    (horder : Nat.card G ≤ Nat.card Model) :
    (∀ v (p : c.graph.Walk v v), p.IsCycle → 12 ≤ p.length) ∧
    (∀ v w, c.graph.dist v w ≤ 6) ∧
    (∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=12) := by
  have hex := c.exists_twelve_cycle_of_order_bound horder
  refine ⟨c.cycle_length_ge_twelve,
    HexagonRecognition.diameter_bound_of_seven_endpoint_bound c.connected ?_,hex⟩
  intro v p hp
  exact HexagonRecognition.seven_endpoint_bound c.graphAction c.seven_transitive
    (·.type) (fun h => h.1) (fun h => (same_orbit_iff c.family _ _).mpr h) hex p hp
end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
