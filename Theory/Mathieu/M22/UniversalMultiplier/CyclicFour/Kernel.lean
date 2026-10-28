module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.Model
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Exact kernel from the order certificate

The paired model already maps onto native M₂₂. An upper bound of 4·443520
on its order bounds the kernel by four. If the distinguished kernel word
has order four, its powers exhaust the kernel and identify it with Z/4.
Commutation with the two actual generators proves centrality by generation.

These reductions separate the finite order certificate from the short word
certificates; neither is inferred from the ATLAS label of the representation.
They are used by the cyclic-four-cover assembly for Aschbacher–Smith I.1.3(4).
-/

namespace Sporadic.Mathieu.M22CyclicFour

public theorem kernel_card_le_four (hbound : Nat.card Model ≤ 1774080) :
    Nat.card projection.ker ≤ 4 := by
  have hc := projection.ker.card_mul_index
  rw [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective projection
      projection_surjective).toEquiv, m22_order] at hc
  omega

/-- The literal kernel, rather than an abstract isomorphic subgroup, is generated
by the specified word once the independent finite certificates are supplied. -/
public theorem kernel_eq_zpowers_of_order_bound
    (hz : orderOf centralWord = 4) (hbound : Nat.card Model ≤ 1774080) :
    projection.ker = Subgroup.zpowers centralWord := by
  symm
  apply Subgroup.eq_of_le_of_card_ge centralWord_zpowers_le_kernel
  rw [Nat.card_zpowers, hz]
  exact kernel_card_le_four hbound

public theorem kernel_equiv_four_of_order_bound
    (hz : orderOf centralWord = 4) (hbound : Nat.card Model ≤ 1774080) :
    Nonempty (projection.ker ≃* Multiplicative (ZMod 4)) := by
  have hker := kernel_eq_zpowers_of_order_bound hz hbound
  have hc : Nat.card projection.ker = 4 := by rw [hker, Nat.card_zpowers, hz]
  let : IsCyclic projection.ker := by rw [hker]; infer_instance
  exact ⟨mulEquivOfCyclicCardEq (hc.trans (Nat.card_zmod 4).symm)⟩

/-- Only two literal commutation identities are needed for the central word. -/
public theorem centralWord_mem_center_of_commutes
    (ha : Commute centralWord generatorA) (hb : Commute centralWord generatorB) :
    centralWord ∈ Subgroup.center Model := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top,
    ← generators_closure, Subgroup.centralizer_closure]
  intro x hx
  rcases hx with rfl | rfl
  · exact ha.eq.symm
  · exact hb.eq.symm

public theorem kernel_le_center_of_order_bound
    (hz : orderOf centralWord = 4) (hbound : Nat.card Model ≤ 1774080)
    (hc : centralWord ∈ Subgroup.center Model) :
    projection.ker ≤ Subgroup.center Model := by
  rw [kernel_eq_zpowers_of_order_bound hz hbound]
  exact Subgroup.zpowers_le.mpr hc

end Sporadic.Mathieu.M22CyclicFour
