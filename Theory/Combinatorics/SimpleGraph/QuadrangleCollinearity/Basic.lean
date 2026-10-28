module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.QuadrangleRecognition

/-!
# Lines and collinearity in a graph of girth eight

Nonbacktracking paths of length at most three are uniquely determined by their
endpoints. Hence two distinct points determine at most one common line, and a
triangle of collinear points lies on one line. The collinearity neighbors of a
point are precisely its nonbacktracking two-walks.

Source: the generalized quadrangle step in Aschbacher–Smith F.4.8, printed p.278.
-/
@[expose] public noncomputable section
namespace SimpleGraph.QuadrangleCollinearity
open SimpleGraph.PathTransitivePolygon
variable {V : Type*} (Γ : SimpleGraph V) (color : V → Bool)

abbrev Point := {x : V // color x = true}

def graph : SimpleGraph (Point color) where
  Adj x y := x ≠ y ∧ ∃ l : V, Γ.Adj x.val l ∧ Γ.Adj y.val l
  symm := ⟨by rintro x y ⟨h,l,hx,hy⟩; exact ⟨h.symm,l,hy,hx⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

variable {Γ color}
variable (hg : ∀ v (p : Γ.Walk v v),p.IsCycle → 8 ≤ p.length)

include hg in
/-- Girth eight makes every rooted nonbacktracking path of length at most three
uniquely determined by its endpoint. -/
theorem short_endpoint_injective {x : V} {n : ℕ} (hn : n ≤ 3)
    (p q : BasedWalk Γ n x) (hp : p.Nonbacktracking) (hq : q.Nonbacktracking)
    (he : p.endpoint = q.endpoint) : p = q := by
  have hg' : ∀ v (r : Γ.Walk v v),r.IsCycle → 7 < r.length := by
    intro v r hr
    have := hg v r hr
    omega
  have hpp := isPath_of_nonbacktracking_of_cycle_bound hg' p hp (by omega)
  have hqp := isPath_of_nonbacktracking_of_cycle_bound hg' q hq (by omega)
  let r := q.toWalk.copy rfl he.symm
  have hrp : r.IsPath := by simpa only [r,Walk.isPath_copy] using hqp
  have hwalk : p.toWalk = r := by
    by_contra hh
    obtain ⟨v,_,_,s,hs,hlen⟩ := hpp.exists_isCycle_length_le_add_of_ne hrp hh
    have hb := hg v s hs
    simp only [r,Walk.length_copy,BasedWalk.length_toWalk] at hlen
    omega
  apply BasedWalk.vertices_injective n x
  have hh := congrArg Walk.support hwalk
  simpa only [r,Walk.support_copy,BasedWalk.support_toWalk] using hh

include hg in
theorem common_vertex_unique {x y a b : V} (hxy : x ≠ y)
    (hxa : Γ.Adj x a) (hya : Γ.Adj y a) (hxb : Γ.Adj x b) (hyb : Γ.Adj y b) : a = b := by
  let p : BasedWalk Γ 2 x := ⟨⟨a,hxa⟩,⟨⟨y,hya.symm⟩,PUnit.unit⟩⟩
  let q : BasedWalk Γ 2 x := ⟨⟨b,hxb⟩,⟨⟨y,hyb.symm⟩,PUnit.unit⟩⟩
  have he := short_endpoint_injective hg (by decide : 2 ≤ 3) p q
    ⟨hxy.symm,trivial⟩ ⟨hxy.symm,trivial⟩ rfl
  exact congrArg (fun r : BasedWalk Γ 2 x => (r.1 : V)) he

include hg in
theorem triangle_on_line {x y z a b d : V}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hxa : Γ.Adj x a) (hya : Γ.Adj y a)
    (hxb : Γ.Adj x b) (hzb : Γ.Adj z b)
    (hyd : Γ.Adj y d) (hzd : Γ.Adj z d) : Γ.Adj z a := by
  by_cases had : a = d
  · exact had ▸ hzd
  by_cases hbd : b = d
  · have hab := common_vertex_unique hg hxy hxa hya hxb (hbd ▸ hyd)
    exact hab ▸ hzb
  let p : BasedWalk Γ 3 x := ⟨⟨a,hxa⟩,⟨⟨y,hya.symm⟩,⟨⟨d,hyd⟩,PUnit.unit⟩⟩⟩
  let q : BasedWalk Γ 3 x := ⟨⟨b,hxb⟩,⟨⟨z,hzb.symm⟩,⟨⟨d,hzd⟩,PUnit.unit⟩⟩⟩
  have he := short_endpoint_injective hg (by decide : 3 ≤ 3) p q
    ⟨hxy.symm,Ne.symm had,trivial⟩ ⟨hzx,Ne.symm hbd,trivial⟩ rfl
  exact (hyz (congrArg (fun r : BasedWalk Γ 3 x => (r.2.1 : V)) he)).elim

variable (hcolor : ∀ {u v},Γ.Adj u v → color u ≠ color v)

include hcolor in
theorem color_eq_of_common {x y l : V} (hx : Γ.Adj x l) (hy : Γ.Adj y l) :
    color x = color y := by
  have h₁ := hcolor hx
  have h₂ := hcolor hy
  cases hx : color x <;> cases hy : color y <;> cases hl : color l <;> simp_all

def twoNeighborMap (x : Point color)
    (p : {p : BasedWalk Γ 2 x.val // p.Nonbacktracking}) : (graph Γ color).neighborSet x :=
  ⟨⟨p.val.endpoint,(color_eq_of_common hcolor p.val.2.1.property.symm p.val.1.property).trans x.property⟩,
    ⟨fun h => p.property.1 (congrArg Subtype.val h).symm,
      p.val.1,p.val.1.property,p.val.2.1.property.symm⟩⟩

include hg in
theorem twoNeighborMap_bijective (x : Point color) : Function.Bijective (twoNeighborMap hcolor x) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply short_endpoint_injective hg (by decide : 2 ≤ 3) p.val q.val p.property q.property
    exact congrArg (fun y : (graph Γ color).neighborSet x => y.val.val) hpq
  · rintro ⟨y,hxy,l,hxl,hyl⟩
    let p : BasedWalk Γ 2 x.val := ⟨⟨l,hxl⟩,⟨⟨y.val,hyl.symm⟩,PUnit.unit⟩⟩
    refine ⟨⟨p,⟨fun h => hxy (Subtype.ext h.symm),trivial⟩⟩,?_⟩
    rfl

def twoNeighborEquiv (x : Point color) :
    {p : BasedWalk Γ 2 x.val // p.Nonbacktracking} ≃ (graph Γ color).neighborSet x :=
  Equiv.ofBijective (twoNeighborMap hcolor x) (twoNeighborMap_bijective hg hcolor x)

end SimpleGraph.QuadrangleCollinearity
