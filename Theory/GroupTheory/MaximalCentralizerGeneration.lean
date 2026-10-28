module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Order.Atoms

/-!
# Generation from a maximal point centralizer

If `C_Y(z)` is maximal in `Y`, adjoining any subgroup of `Y` which moves
`z` generates `Y`. In particular, an ambient subgroup containing that
moving subgroup and `C_Y(z)` contains all of `Y`.

This elementary maximal-subgroup argument is useful when a natural
permutation module identifies the point centralizer with a maximal
intransitive subgroup. It avoids making any claim about the perfect
residual of the moving subgroup.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A maximal point centralizer and a subgroup moving the point force
containment of their whole overgroup. -/
theorem le_of_maximal_pointCentralizer
    {A Y M : Subgroup G} {z : G}
    (hmax : IsCoatom ((centralizer ({z} : Set G)).subgroupOf Y))
    (hAY : A ≤ Y) (hAM : A ≤ M)
    (hCM : Y ⊓ centralizer ({z} : Set G) ≤ M)
    (hmove : ¬ A ≤ centralizer ({z} : Set G)) : Y ≤ M := by
  have hc : (centralizer ({z} : Set G)).subgroupOf Y ≤ M.subgroupOf Y :=
    fun x hx => hCM ⟨x.property, hx⟩
  have hlt : (centralizer ({z} : Set G)).subgroupOf Y < M.subgroupOf Y := by
    refine lt_of_le_of_ne hc ?_
    intro he
    apply hmove
    intro a ha
    have hm : (⟨a, hAY ha⟩ : Y) ∈ M.subgroupOf Y := hAM ha
    rw [← he] at hm
    exact hm
  have ht : M.subgroupOf Y = ⊤ := hmax.lt_iff.mp hlt
  intro y hy
  have hm : (⟨y, hy⟩ : Y) ∈ M.subgroupOf Y := by rw [ht]; trivial
  exact hm

end Theory.GroupTheory
