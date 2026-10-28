module
public import Theory.GroupTheory.DisjointCommutingProduct.Projections
public import Mathlib.GroupTheory.Index

/-! A subgroup of index two in P × <t> which omits t is the graph of
a homomorphism P → <t>.  The retained projection is an isomorphism, and
the difference between a graph element and its projection is a power of t.
This is the source S₀ in 2.5.19, printed p.564. -/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {G : Type*} [Group G] [Finite G]

private theorem graph_mem_zpowers_two {t x : G} (ht : orderOf t = 2)
    (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,ht] at hx
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

/-- The actual index-two graph subgroup is isomorphic to the first factor,
with its central displacement retained in the original ambient group. -/
theorem index_two_graph_equiv (P : Subgroup G) (t : G)
    (ht : orderOf t = 2) (htC : t ∈ centralizer (P : Set G)) (htP : t ∉ P)
    (D : Subgroup (P ⊔ zpowers t : Subgroup G)) (hi : D.index = 2)
    (htD : (⟨t,mem_sup_right (mem_zpowers t)⟩ : (P ⊔ zpowers t : Subgroup G)) ∉ D) :
    ∃ e : D ≃* P, ∀ d : D, (((d : (P ⊔ zpowers t : Subgroup G)) : G) *
      ((e d : P) : G)⁻¹) ∈ zpowers t := by
  let W := P ⊔ zpowers t
  have hd : Disjoint P (zpowers t) := by
    apply disjoint_def.mpr
    intro x hxP hxt
    rcases graph_mem_zpowers_two ht hxt with he | he
    · exact he
    · exact (htP (he ▸ hxP)).elim
  have hc : P ≤ centralizer (zpowers t : Set G) :=
    le_centralizer_iff.mp (zpowers_le.mpr htC)
  obtain ⟨π,hπ,hker,hleft,_⟩ := exists_left_projection_of_disjoint_of_commuting
    P (zpowers t) hd hc
  let f : D →* P := π.comp D.subtype
  have hfi : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro d hd1
    have hk : (d : W) ∈ π.ker := hd1
    rw [hker] at hk
    rcases graph_mem_zpowers_two ht hk with he | he
    · exact Subtype.ext (Subtype.ext he)
    · have het : (d : W) = ⟨t,mem_sup_right (mem_zpowers t)⟩ := Subtype.ext he
      exact (htD (het ▸ d.property)).elim
  have hcard : Nat.card D = Nat.card P := by
    obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting P (zpowers t) hd hc
    have hw : Nat.card W = Nat.card P * 2 := by
      rw [← Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_zpowers,ht]
    have hdcard := D.card_mul_index
    rw [hi,hw] at hdcard
    omega
  have hfb : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr ⟨hfi,hcard⟩
  refine ⟨MulEquiv.ofBijective f hfb,?_⟩
  intro d
  have hk : (d : W) * (inclusion (show P ≤ W from le_sup_left) (f d))⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,hleft]
    exact mul_inv_cancel _
  rw [hker] at hk
  exact hk
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
