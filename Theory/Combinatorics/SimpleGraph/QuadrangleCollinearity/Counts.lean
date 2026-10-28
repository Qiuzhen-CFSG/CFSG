module
public import Theory.Combinatorics.SimpleGraph.QuadrangleCollinearity.Basic
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.Data.Set.Card

/-!
# Common-neighbor counts in a finite generalized quadrangle

For adjacent points, common collinearity neighbors are the other points on
their unique line. For nonadjacent points, every incident line at the second
point has a unique common collinearity neighbor, obtained from its three-edge
geodesic from the first point. These actual equivalences give the parameters
one and five when line and point valencies are three and five.

Source: the generalized quadrangle argument in Aschbacher–Smith F.4.8,
printed p.278, specialized later to the U₄(2) completion in F.4.24.
-/
@[expose] public noncomputable section
namespace SimpleGraph.QuadrangleCollinearity
open SimpleGraph.PathTransitivePolygon
variable {V : Type*} {Γ : SimpleGraph V} {color : V → Bool}
variable (hg : ∀ v (p : Γ.Walk v v),p.IsCycle → 8 ≤ p.length)
variable (hcolor : ∀ {u v},Γ.Adj u v → color u ≠ color v)

def adjacentCommonEquiv {x y : Point color} (hxy : x ≠ y) {l : V}
    (hxl : Γ.Adj x.val l) (hyl : Γ.Adj y.val l) :
    (graph Γ color).commonNeighbors x y ≃
      {z : Γ.neighborSet l // z.val ≠ x.val ∧ z.val ≠ y.val} where
  toFun z := ⟨⟨z.val.val,by
    obtain ⟨hxz,m,hxm,hzm⟩ := z.property.1
    obtain ⟨hyz,n,hyn,hzn⟩ := z.property.2
    exact (triangle_on_line hg (fun h => hxy (Subtype.ext h))
      (fun h => hyz (Subtype.ext h)) (fun h => hxz (Subtype.ext h.symm))
      hxl hyl hxm hzm hyn hzn).symm⟩,
    fun h => z.property.1.1 (Subtype.ext h.symm),
    fun h => z.property.2.1 (Subtype.ext h.symm)⟩
  invFun z := ⟨⟨z.val.val,(color_eq_of_common hcolor z.val.property.symm hxl).trans x.property⟩,
    ⟨fun h => z.property.1 (congrArg Subtype.val h).symm,l,hxl,z.val.property.symm⟩,
    ⟨fun h => z.property.2 (congrArg Subtype.val h).symm,l,hyl,z.val.property.symm⟩⟩
  left_inv z := rfl
  right_inv z := rfl

theorem card_avoid_two {W : Type*} [Finite W] (a b : W) (hne : a ≠ b) :
    Nat.card {z : W // z ≠ a ∧ z ≠ b} = Nat.card W - 2 := by
  classical
  have e : {z : W // z ≠ a ∧ z ≠ b} ≃ {z : W // z ∈ ({a,b} : Set W)ᶜ} :=
    Equiv.subtypeEquivRight (by intro z; simp only [Set.mem_compl_iff,Set.mem_insert_iff,
      Set.mem_singleton_iff,not_or])
  rw [Nat.card_congr e,Nat.card_coe_set_eq,Set.ncard_compl,Set.ncard_pair hne]

include hg hcolor in
lemma card_adjacent_common [Finite V]
    (hdegree : ∀ l, color l = false → Nat.card (Γ.neighborSet l) = 3)
    {x y : Point color} (hxy : (graph Γ color).Adj x y) :
    Nat.card ((graph Γ color).commonNeighbors x y) = 1 := by
  obtain ⟨hne,l,hxl,hyl⟩ := hxy
  let a : Γ.neighborSet l := ⟨x.val,hxl.symm⟩
  let b : Γ.neighborSet l := ⟨y.val,hyl.symm⟩
  have hab : a ≠ b := fun h => hne (Subtype.ext (congrArg (fun z : Γ.neighborSet l => z.val) h))
  have he : {z : Γ.neighborSet l // z.val ≠ x.val ∧ z.val ≠ y.val} ≃
      {z : Γ.neighborSet l // z ≠ a ∧ z ≠ b} :=
    Equiv.subtypeEquivRight (by
      intro z
      constructor
      · rintro ⟨hx,hy⟩; exact ⟨fun h => hx (congrArg Subtype.val h),fun h => hy (congrArg Subtype.val h)⟩
      · rintro ⟨hx,hy⟩; exact ⟨fun h => hx (Subtype.ext h),fun h => hy (Subtype.ext h)⟩)
  have hlfalse : color l = false := by
    have ht := hcolor hxl
    rw [x.property] at ht
    cases hl : color l <;> simp_all
  rw [Nat.card_congr (adjacentCommonEquiv hg hcolor hne hxl hyl),Nat.card_congr he,
    card_avoid_two a b hab,hdegree l hlfalse]


def commonLineMap {x y : Point color} (z : (graph Γ color).commonNeighbors x y) :
    Γ.neighborSet y.val := ⟨Classical.choose z.property.2.2,
      (Classical.choose_spec z.property.2.2).1⟩

theorem commonLineMap_adj {x y : Point color} (z : (graph Γ color).commonNeighbors x y) :
    Γ.Adj z.val.val (commonLineMap z).val := (Classical.choose_spec z.property.2.2).2

include hg in
theorem common_neighbor_on_line_unique {x y : Point color} (hxy : x ≠ y)
    (hnot : ¬ (graph Γ color).Adj x y) {l : V} (hyl : Γ.Adj y.val l)
    (z w : (graph Γ color).commonNeighbors x y)
    (hzl : Γ.Adj z.val.val l) (hwl : Γ.Adj w.val.val l) : z = w := by
  obtain ⟨hxz,a,hxa,hza⟩ := z.property.1
  obtain ⟨hxw,b,hxb,hwb⟩ := w.property.1
  have hla : l ≠ a := fun h => hnot ⟨hxy,a,hxa,h ▸ hyl⟩
  have hlb : l ≠ b := fun h => hnot ⟨hxy,b,hxb,h ▸ hyl⟩
  let p : BasedWalk Γ 3 x.val := ⟨⟨a,hxa⟩,⟨⟨z.val.val,hza.symm⟩,⟨⟨l,hzl⟩,PUnit.unit⟩⟩⟩
  let q : BasedWalk Γ 3 x.val := ⟨⟨b,hxb⟩,⟨⟨w.val.val,hwb.symm⟩,⟨⟨l,hwl⟩,PUnit.unit⟩⟩⟩
  have he := short_endpoint_injective hg (by decide : 3 ≤ 3) p q
    ⟨fun h => hxz (Subtype.ext h.symm),hla,trivial⟩
    ⟨fun h => hxw (Subtype.ext h.symm),hlb,trivial⟩ rfl
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun r : BasedWalk Γ 3 x.val => (r.2.1 : V)) he

variable (hconn : Γ.Connected) (hdiam : ∀ v w,Γ.dist v w ≤ 4)
include hcolor hconn hdiam in
theorem exists_three_to_line {x y : Point color} (hxy : x ≠ y)
    (hnot : ¬ (graph Γ color).Adj x y) {l : V} (hyl : Γ.Adj y.val l) :
    ∃ p : BasedWalk Γ 3 x.val,p.Nonbacktracking ∧ p.endpoint = l := by
  obtain ⟨p,hp,hlen⟩ := hconn.exists_path_of_dist x.val l
  have hc : color x.val ≠ color l := by
    rw [x.property,← y.property]
    exact hcolor hyl
  have hodd : Odd (Γ.dist x.val l) := by
    apply Nat.not_even_iff_odd.mp
    rw [← hlen]
    intro h
    exact hc ((QuadrangleRecognition.even_length_iff color hcolor p).mp h)
  obtain ⟨k,hk⟩ := hodd
  have hd := hdiam x.val l
  have hne : Γ.dist x.val l ≠ 1 := by
    intro h
    exact hnot ⟨hxy,l,SimpleGraph.dist_eq_one_iff_adj.mp h,hyl⟩
  have hd3 : Γ.dist x.val l = 3 := by omega
  have hl3 : p.length = 3 := hlen.trans hd3
  refine ⟨hl3 ▸ BasedWalk.ofWalk p,?_,?_⟩
  · exact (BasedWalk.nonbacktracking_cast hl3 _).mpr
      (BasedWalk.nonbacktracking_ofWalk_of_isPath p hp)
  · simp only [BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]

include hcolor hconn hdiam in
theorem exists_common_neighbor_on_line {x y : Point color} (hxy : x ≠ y)
    (hnot : ¬ (graph Γ color).Adj x y) {l : V} (hyl : Γ.Adj y.val l) :
    ∃ z : (graph Γ color).commonNeighbors x y,Γ.Adj z.val.val l := by
  obtain ⟨p,hp,he⟩ := exists_three_to_line hcolor hconn hdiam hxy hnot hyl
  let z : Point color := ⟨p.2.1,(color_eq_of_common hcolor p.2.1.property.symm p.1.property).trans x.property⟩
  have hxz : x ≠ z := fun h => hp.1 (congrArg Subtype.val h).symm
  have hzl : Γ.Adj z.val l := by
    change Γ.Adj (p.2.1 : V) l
    exact he ▸ p.2.2.1.property
  have hyz : y ≠ z := by
    intro h
    exact hnot ⟨hxy,p.1,p.1.property,h ▸ p.2.1.property.symm⟩
  exact ⟨⟨z,⟨hxz,p.1,p.1.property,p.2.1.property.symm⟩,⟨hyz,l,hyl,hzl⟩⟩,hzl⟩

include hg hcolor hconn hdiam in
theorem commonLineMap_bijective {x y : Point color} (hxy : x ≠ y)
    (hnot : ¬ (graph Γ color).Adj x y) :
    Function.Bijective (commonLineMap (Γ := Γ) (color := color) (x := x) (y := y)) := by
  constructor
  · intro z w h
    apply common_neighbor_on_line_unique hg hxy hnot (commonLineMap z).property z w
      (commonLineMap_adj z)
    exact (congrArg Subtype.val h).symm ▸ commonLineMap_adj w
  · intro l
    obtain ⟨z,hzl⟩ := exists_common_neighbor_on_line hcolor hconn hdiam hxy hnot l.property
    refine ⟨z,Subtype.ext ?_⟩
    exact common_vertex_unique hg (fun h => z.property.2.1 (Subtype.ext h))
      (commonLineMap z).property (commonLineMap_adj z) l.property hzl

def nonadjacentCommonEquiv {x y : Point color} (hxy : x ≠ y)
    (hnot : ¬ (graph Γ color).Adj x y) :
    (graph Γ color).commonNeighbors x y ≃ Γ.neighborSet y.val :=
  Equiv.ofBijective commonLineMap (commonLineMap_bijective hg hcolor hconn hdiam hxy hnot)

end SimpleGraph.QuadrangleCollinearity
