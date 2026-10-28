module
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Tactic.Group

/-!
# Fixed elements of an exchanged elementary direct product

An involution swapping two disjoint commuting elementary factors has a
full diagonal as its fixed subgroup. Its order is the order of either factor,
and each fixed element is a displacement. The multiplication equivalence
retains the original subgroup embeddings.

Application: the center calculation in Aschbacher–Smith, 2.4.14(3), p.533.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem elementary_swapped_pair_fixed
    (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (α : MulAut G) (hα : ∀ x, α (α x)=x) (hAB : A.map α.toMonoidHom=B) :
    Nat.card ((A ⊔ B) ⊓ α.toMonoidHom.eqLocus (MonoidHom.id G) : Subgroup G)=Nat.card A ∧
    ∀ z ∈ A ⊔ B, α z=z → ∃ w ∈ A ⊔ B, z=w*(α w)⁻¹ := by
  let F := (A ⊔ B) ⊓ α.toMonoidHom.eqLocus (MonoidHom.id G)
  have hA {x : G} (hx : x∈A) : α x∈B := hAB ▸ mem_map_of_mem _ hx
  have hB {x : G} (hx : x∈B) : α x∈A := by
    obtain ⟨a,ha,he⟩ := (show x∈A.map α.toMonoidHom from hAB.symm ▸ hx)
    change α a=x at he
    rw [←he,hα]
    exact ha
  let f : A → F := fun a => ⟨a.val*α a.val,
    mul_mem (mem_sup_left a.property) (mem_sup_right (hA a.property)),by
      change α (a.val*α a.val)=a.val*α a.val
      rw [map_mul,hα]
      exact hc a.property (α a.val) (hA a.property)⟩
  have hf : Function.Injective f := by
    intro a b he
    have hh : (a,(⟨α a.val,hA a.property⟩:B)) = (b,(⟨α b.val,hA b.property⟩:B)) :=
      mul_injective_of_disjoint hd (congrArg Subtype.val he)
    exact congrArg Prod.fst hh
  have hs : Function.Surjective f := by
    intro z
    obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
    obtain ⟨⟨u,v⟩,huv⟩ := e.surjective ⟨z.val,z.property.1⟩
    have hz : (u:G)*(v:G)=z.val := (he u v).symm.trans (congrArg Subtype.val huv)
    have hfix : α z.val=z.val := z.property.2
    rw [←hz,map_mul] at hfix
    have hswap : α (v:G)*α (u:G)=(u:G)*(v:G) :=
      (hc (hB v.property) (α (u:G)) (hA u.property)).symm.trans hfix
    have hp : ((⟨α (v:G),hB v.property⟩:A),(⟨α (u:G),hA u.property⟩:B)) = (u,v) :=
      mul_injective_of_disjoint hd hswap
    have heq : α (u:G)=(v:G) := congrArg (fun p : A × B => (p.2:G)) hp
    exact ⟨u,Subtype.ext (by change u.val*α u.val=z.val;rw [heq,hz])⟩
  refine ⟨Nat.card_congr (Equiv.ofBijective f ⟨hf,hs⟩).symm,?_⟩
  intro z hz hzfix
  obtain ⟨u,hu⟩ := hs ⟨z,hz,hzfix⟩
  have hui : (u:G)⁻¹=(u:G) := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) (u:G) u.property)
  refine ⟨u,mem_sup_left u.property,?_⟩
  rw [←map_inv,hui]
  exact (congrArg Subtype.val hu).symm
end Theory.GroupTheory

