module
public import Stellmacher.ElementaryAbelianMaxPair.MarkedGeneration
public import Theory.GroupTheory.CrossingDerivedKernel
/-! # A moved maximum plane and its crossing derived subgroup
When two marked planes generate the factor, an element moving either maximum
plane interchanges the two. If this element is the square of a crossing actor,
the two crossing commutation identities put the conjugate derived subgroup
in the actual marked kernel. Source: Aschbacher--Smith 2.5.7, printed p.556.
-/
public section
open Subgroup
namespace Stellmacher
variable {G Q:Type*} [Group G] [Group Q]
theorem maxFamily_moved_plane_generates
    (K P₀ P₁ V:Subgroup G)
    (hpair:elementaryAbelianMaxSubgroups K={P₀,P₁})
    (hgen:P₀⊔P₁=K) (hV:V∈elementaryAbelianMaxSubgroups K)
    (y:G) (hy:y∈normalizer (K:Set G)) (hmove:y∉normalizer (V:Set G)) :
    K=V⊔V.conjBy y := by
  have hm:=maxFamily_conj_mem hV hy
  have hne:V.conjBy y≠V:=fun he=>hmove (mem_normalizer_iff_map_conj_eq.mpr he)
  simp only [hpair,Set.mem_insert_iff,Set.mem_singleton_iff] at hV hm
  rcases hV with rfl|rfl <;> rcases hm with he|he
  · exact (hne he).elim
  · rw [he,hgen]
  · rw [he,sup_comm,hgen]
  · exact (hne he).elim

theorem marked_maxFamily_moved_plane_generates
    {E:Type*} [Group E] [Finite E]
    (f:E→*Q) (hf:Function.Surjective f) (i:E→*G) (hi:Function.Injective i)
    (P₀ P₁:Subgroup Q)
    [IsElementaryAbelian 2 (P₀.comap f)] [IsElementaryAbelian 2 (P₁.comap f)]
    (hcard:Nat.card P₀=Nat.card P₁) (hne:P₀≠P₁)
    (hcover:∀A:Subgroup Q,IsElementaryAbelian 2 A→A≤P₀∨A≤P₁)
    (hgen:P₀⊔P₁=⊤) (V:Subgroup G)
    (hV:V∈elementaryAbelianMaxSubgroups i.range)
    (y:G) (hy:y∈normalizer (i.range:Set G)) (hmove:y∉normalizer (V:Set G)) :
    i.range=V⊔V.conjBy y := by
  have hp:=(maxFamily_pair_of_marked_image f hf i hi P₀ P₁ hcard hne hcover).1
  apply maxFamily_moved_plane_generates i.range _ _ V hp ?_ hV y hy hmove
  rw [←Subgroup.map_sup,Subgroup.TwoPlaneCover.comap_sup_eq_top f hf P₀ P₁ hgen,
    ←MonoidHom.range_eq_map]
end Stellmacher
