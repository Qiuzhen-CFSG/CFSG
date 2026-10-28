module
public import Theory.SpecificGroups.PSL2.AmbientDihedralFixedGeneration

/-! The actual index-two centralizer kernel cuts out the graph subgroup
used to generate the companion component. No graph choice or generation
premise remains. Source 2.5.19, printed p.564. -/
public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {G : Type*} [Group G] [Finite G]

theorem prime_component_normalizes_of_index_two_kernel
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hpower : ∃ k, p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    (C R X : Subgroup G) (eC : C ≃* PSL(2,ZMod p)) (P : Sylow 2 C)
    (t : G) (ht : orderOf t = 2) (htC : t ∈ centralizer (C : Set G)) (htnot : t ∉ C)
    (hWR : (P : Subgroup C).map C.subtype ⊔ zpowers t ≤ R)
    (hindex : ((R ⊓ centralizer (X : Set G)).subgroupOf R).index = 2)
    (htX : t ∉ centralizer (X : Set G))
    (hcentralizers : ∀ j ∈ R ⊓ centralizer (X : Set G), orderOf j = 2 →
      centralizer ({j} : Set G) ≤ normalizer (X : Set G)) :
    C ≤ normalizer (X : Set G) := by
  let W := (P : Subgroup C).map C.subtype ⊔ zpowers t
  let R₀ := R ⊓ centralizer (X : Set G)
  let D := R₀.subgroupOf W
  have htW : t ∈ W := mem_sup_right (mem_zpowers t)
  have htR : t ∈ R := hWR htW
  have htD : (⟨t,htW⟩ : W) ∉ D := fun h => htX h.2
  have htR₀ : (⟨t,htR⟩ : R) ∉ R₀.subgroupOf R := fun h => htX h.2
  have hDindex : D.index = 2 := by
    apply index_eq_two_iff_exists_notMem_and.mpr
    refine ⟨⟨t,htW⟩,htD,?_⟩
    intro w
    by_cases hw : w ∈ D
    · exact Or.inr hw
    · apply Or.inl
      have hwR : (⟨(w:G),hWR w.property⟩ : R) ∉ R₀.subgroupOf R := hw
      have hwt : (⟨(w:G),hWR w.property⟩ : R) * (⟨t,htR⟩ : R) ∈ R₀.subgroupOf R :=
        (mul_mem_iff_of_index_two hindex).mpr (iff_of_false hwR htR₀)
      exact hwt
  apply prime_component_le_of_graph_involution_centralizers hp hpower C eC P t ht htC htnot
    D hDindex htD
  intro j hj hj2
  obtain ⟨x,hx,rfl⟩ := hj
  exact inf_le_right.trans (hcentralizers x hx hj2)
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
