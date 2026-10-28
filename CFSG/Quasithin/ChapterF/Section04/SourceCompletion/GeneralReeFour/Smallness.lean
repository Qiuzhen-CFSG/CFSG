module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour
public import Theory.SpecificGroups.ReeF4.SourceCompletion.Orders
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.OctagonRecognition

/-!
# A field-factor order bound forces a small general Ree completion

At a Suzuki-type vertex the eight-path census is (q²+1)q^10, while the
native number of vertices of that type is (q+1)(q³+1)(q⁶+1). For any k<q,
the former exceeds k times the latter. Girth at least sixteen makes the
eight-path endpoint map injective unless there is a sixteen-cycle.
Consequently |C| ≤ k|ReeF4.Model m| forces such a cycle. Nine-path
transitivity propagates its complementary seven-arcs and gives diameter eight.

This allows the source bound |G| ≤ |Mbar| to be used after bounding the
extension factor; it does not replace that bound by |G| ≤ |ReeF4.Model m|.
The Chapter6 and Chapter12 companions apply this to the literal original
factor join and the original degree n=2m+1. Construction of the ambient
order bound and recognition of the resulting group remain separate duties
of the same source-theorem owner. Octagon geometry alone is not recognition.

Source: Aschbacher–Smith F.4.12–13,24 and F.4.43–44,
printed pp.280,287,296 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup ReeF4 ReeF4.Parabolics

namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo

private theorem eight_endpoint_injective {V : Type*} {Γ : SimpleGraph V}
    (hg : ∀ v (p : Γ.Walk v v), p.IsCycle → 16 < p.length) (x : V) :
    Function.Injective (fun p : {p : BasedWalk Γ 8 x // p.Nonbacktracking} => p.val.endpoint) := by
  intro p q he
  have hp := isPath_of_nonbacktracking_of_cycle_bound hg p.val p.property (by decide : 8≤16)
  have hq := isPath_of_nonbacktracking_of_cycle_bound hg q.val q.property (by decide : 8≤16)
  have hw : p.val.toWalk = q.val.toWalk.copy rfl he.symm := by
    by_contra hne
    obtain ⟨v,_,_,c,hc,hlen⟩ := hp.exists_isCycle_length_le_add_of_ne
      ((Walk.isPath_copy _ rfl he.symm).mpr hq) hne
    have hh := hg v c hc
    simp only [Walk.length_copy,BasedWalk.length_toWalk] at hlen
    omega
  apply Subtype.ext
  apply BasedWalk.vertices_injective
  simpa only [Walk.support_copy,BasedWalk.support_toWalk] using congrArg Walk.support hw

private def typedEquiv {G : Type*} [Group G] (P : Bool → Subgroup G) (i : Bool) :
    {v : RankTwo.Vertex P // v.type=i} ≃ (G ⧸ P i) where
  toFun v := v.property ▸ v.val.coset
  invFun a := ⟨⟨i,a⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,a⟩,h⟩; dsimp at h; subst j; rfl
  right_inv := by intro a; rfl

private theorem field_factor_inequality {q k : ℕ} (hq : 1<q) (hk : k<q) :
    k*((q+1)*(q^3+1)*(q^6+1)) < (q^2+1)*q^10 := by
  have h36 : q^3+1 ≤ q^4 := by
    have hp : 1 ≤ q^3 := Nat.one_le_pow 3 q (by omega)
    calc
      q^3+1 ≤ 2*q^3 := by omega
      _ ≤ q*q^3 := Nat.mul_le_mul_right _ (by omega : 2 ≤ q)
      _ = q^4 := by ring
  have h46 : q^4 ≤ q^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have h79 : q^7 ≤ q^9 := Nat.pow_le_pow_right (by omega) (by decide)
  have h6 : 2*q^6 ≤ q^7 := by
    calc
      2*q^6 ≤ q*q^6 := Nat.mul_le_mul_right _ (by omega : 2 ≤ q)
      _ = q^7 := by ring
  have h9 : 2*q^9 ≤ q^10 := by
    calc
      2*q^9 ≤ q*q^9 := Nat.mul_le_mul_right _ (by omega : 2 ≤ q)
      _ = q^10 := by ring
  have hs : (q^3+1)*(q^6+1) ≤ q^10 := by nlinarith
  have hf : k*(q+1) < q^2+1 := by
    have hh := Nat.mul_le_mul_right (q+1) (show k+1≤q by omega)
    nlinarith
  calc
    k*((q+1)*(q^3+1)*(q^6+1)) = (k*(q+1))*((q^3+1)*(q^6+1)) := by ring
    _ ≤ (k*(q+1))*q^10 := Nat.mul_le_mul_left _ hs
    _ < (q^2+1)*q^10 := Nat.mul_lt_mul_of_pos_right hf (by positivity)

namespace Completion
variable {m : ℕ} {G : Type*} [Group G] (c : Completion m G)
local notation "q" => 2^(2*m+1)

/-- Exact eight-path census in both marked vertex types. -/
theorem eight_path_card (hm : 0 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range) (x : c.Vertex) :
    Nat.card {p : BasedWalk c.graph 8 x // p.Nonbacktracking} =
      if x.type then (q^2+1)*q^10 else (q+1)*q^11 := by
  have (x : c.Vertex) : Finite (c.graph.neighborSet x) :=
    Nat.finite_of_card_ne_zero (by rw [c.card_neighbors hm hc]; split <;> positivity)
  have hf : ∀ {x y : c.Vertex}, c.graph.Adj x y → y.type = !x.type := by
    intro x y h
    have hxy := h.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  have hh := BasedWalk.card_nonbacktracking_succ c.graph (fun x : c.Vertex => x.type)
    (fun b => (if b then q^2 else q)+1) hf (c.card_neighbors hm hc) 7 x
  cases hx : x.type <;>
    simp only [hx,Bool.not_false,Bool.not_true, Bool.false_eq_true,↓reduceIte,
      BasedWalk.forwardCount,Nat.add_sub_cancel] at hh ⊢ <;>
    rw [hh] <;> ring

/-- A factor smaller than q in the order bound already forces a sixteen-cycle. -/
theorem exists_sixteen_cycle_of_order_bound [Finite G] (hm : 0 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    {k : ℕ} (hk : k < q) (horder : Nat.card G ≤ k*Nat.card (Model m)) :
    ∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=16 := by
  classical
  by_contra hno
  have hg (v : c.Vertex) (p : c.graph.Walk v v) (hp : p.IsCycle) : 16<p.length := by
    have hle := c.cycle_length_ge_sixteen hm hc v p hp
    have hne : p.length≠16 := fun hh => hno ⟨v,p,hp,hh⟩
    omega
  let x := RankTwo.base c.cosetFamily true
  let f : {p : BasedWalk c.graph 8 x // p.Nonbacktracking} →
      {v : c.Vertex // v.type=true} := fun p =>
    ⟨p.val.endpoint, ((QuadrangleRecognition.even_length_iff (G := c.graph) (·.type)
      (fun h => h.1) p.val.toWalk).mp
        (by simp only [BasedWalk.length_toWalk]; decide)).symm⟩
  let : Finite {v : c.Vertex // v.type=true} := Finite.of_equiv
    (G ⧸ c.cosetFamily true) (typedEquiv c.cosetFamily true).symm
  have hi : Function.Injective f := fun p r h =>
    eight_endpoint_injective hg x (congrArg Subtype.val h)
  have hcount := Nat.card_le_card_of_injective f hi
  rw [c.eight_path_card hm hc,Nat.card_congr (typedEquiv c.cosetFamily true)] at hcount
  change (q^2+1)*q^10 ≤ c.right.range.index at hcount
  have hpar : Nat.card c.right.range = Nat.card (parabolic m .suzuki) :=
    (Nat.card_congr (MonoidHom.ofInjective c.right_injective).toEquiv).symm
  have hidx : c.right.range.index ≤ k*((q+1)*(q^3+1)*(q^6+1)) := by
    rw [ReeF4.SourceCompletion.order_factor_suzuki m hm] at horder
    have hh := c.right.range.card_mul_index
    rw [hpar] at hh
    rw [←hh] at horder
    have he : k*(Nat.card (parabolic m .suzuki)*((q+1)*(q^3+1)*(q^6+1))) =
        Nat.card (parabolic m .suzuki)*(k*((q+1)*(q^3+1)*(q^6+1))) := by ring
    rw [he] at horder
    exact Nat.le_of_mul_le_mul_left horder Nat.card_pos
  have hq : 1<q := Nat.one_lt_pow (by omega) (by decide)
  exact (not_lt_of_ge (hcount.trans hidx)) (field_factor_inequality hq hk)

/-- Full octagon metric from the order comparison, with no cycle or diameter input. -/
theorem octagon_metric_of_order_bound [Finite G] (hm : 0 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    {k : ℕ} (hk : k < q) (horder : Nat.card G ≤ k*Nat.card (Model m)) :
    (∀ v (p : c.graph.Walk v v), p.IsCycle → 16 ≤ p.length) ∧
    (∀ v w, c.graph.dist v w ≤ 8) ∧
    (∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=16) := by
  have hex := c.exists_sixteen_cycle_of_order_bound hm hc hk horder
  refine ⟨c.cycle_length_ge_sixteen hm hc,
    OctagonRecognition.diameter_bound_of_nine_endpoint_bound c.connected ?_,hex⟩
  intro v p hp
  exact OctagonRecognition.nine_endpoint_bound c.graphAction (c.nine_transitive hm hc)
    (·.type) (fun h => h.1) (fun h => (same_orbit_iff c.cosetFamily _ _).mpr h) hex p hp
end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
