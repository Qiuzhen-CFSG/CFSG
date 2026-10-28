module
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Movement cannot cancel between independent supports

Let K normalize W and W', with W normalizing W' and W intersect W' contained
in Z. If [u,k] is outside Z for some k in K, then K cannot centralize uv
for u in W and v in W'. The commutator product identity would otherwise
put [u,k] in both supports.

This elementary support argument supplies the product-movement condition
in Aschbacher--Smith 14.6.17 and 14.6.24, retaining the actual conjugate
support rather than an unrelated model module.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem product_not_centralized_of_disjoint_modulo
    (K W W' Z : Subgroup G)
    (hKW : K ≤ normalizer (W : Set G)) (hKW' : K ≤ normalizer (W' : Set G))
    (hWW' : W ≤ normalizer (W' : Set G)) (hdis : W ⊓ W' ≤ Z)
    (u v : G) (hu : u ∈ W) (hv : v ∈ W')
    (hmove : ∃ k ∈ K, ⁅u,k⁆ ∉ Z) :
    ¬ K ≤ centralizer ({u*v} : Set G) := by
  intro hc
  obtain ⟨k,hk,hkz⟩ := hmove
  have hmW : ⁅u,k⁆ ∈ W :=
    (le_normalizer_iff_commutator_le_left.mp hKW) (commutator_mem_commutator hu hk)
  have hmW' : ⁅v,k⁆ ∈ W' :=
    (le_normalizer_iff_commutator_le_left.mp hKW') (commutator_mem_commutator hv hk)
  have he : ⁅u*v,k⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_centralizer_singleton_iff.mp (hc hk)).symm
  rw [commutatorElement_mul_left_eq_conj_mul] at he
  have he' : ⁅u,k⁆ = (u * ⁅v,k⁆ * u⁻¹)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact he
  apply hkz (hdis ⟨hmW,?_⟩)
  rw [he']
  exact W'.inv_mem ((hWW' hu _).mp hmW')

end Theory.GroupTheory
