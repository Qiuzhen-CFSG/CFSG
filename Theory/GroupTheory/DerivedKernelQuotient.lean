module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Derived kernels under a central quotient

For a surjective quotient by a subgroup N of the kernel of q, restrict the
quotient map to ker(q) intersected with the derived subgroup. Its kernel
embeds in N and its image lies in the derived kernel of the induced map.
The kernel–image cardinality formula therefore gives the multiplicative
bound, without assuming that the original group is perfect.

The induced kernel remains central whenever the original kernel is central.
These general facts supply the quotient step in the relative hexad calculation
for Aschbacher–Smith I.1.3(4), printed p.407.
-/

public section

open Subgroup

namespace CentralDerivedKernel

variable {D G : Type*} [Group D] [Group G]

/-- Quotienting by a subgroup of the kernel bounds the original derived kernel
by the product of the quotient subgroup and the new derived kernel. -/
theorem card_le_quotient [Finite D] (q : D →* G)
    (N : Subgroup D) [N.Normal] (hN : N ≤ q.ker) :
    Nat.card (q.ker ⊓ commutator D : Subgroup D) ≤
      Nat.card N * Nat.card ((QuotientGroup.lift N q hN).ker ⊓
        commutator (D ⧸ N) : Subgroup (D ⧸ N)) := by
  let π := QuotientGroup.mk' N
  let qN := QuotientGroup.lift N q hN
  let K := q.ker ⊓ commutator D
  let L := qN.ker ⊓ commutator (D ⧸ N)
  have hcomm : (commutator D).map π ≤ commutator (D ⧸ N) := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  let t : K →* L := (π.comp K.subtype).codRestrict L (fun x =>
    ⟨show qN (π x) = 1 from x.property.1,
      hcomm (mem_map_of_mem π x.property.2)⟩)
  let i : t.ker → N := fun x => ⟨((x : K) : D), by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg (fun y : L => (y : D ⧸ N)) x.property⟩
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : D)) h))
  have hk : Nat.card t.ker ≤ Nat.card N := Nat.card_le_card_of_injective i hi
  have hl : Nat.card t.range ≤ Nat.card L :=
    Nat.card_le_card_of_injective t.range.subtype t.range.subtype_injective
  calc
    Nat.card K = Nat.card t.ker * Nat.card t.range := by
      rw [← index_ker t]
      exact t.ker.card_mul_index.symm
    _ ≤ Nat.card N * Nat.card L := Nat.mul_le_mul hk hl

/-- Centrality of the kernel survives quotienting by any of its subgroups. -/
theorem quotient_ker_le_center (q : D →* G) (hc : q.ker ≤ center D)
    (N : Subgroup D) [N.Normal] (hN : N ≤ q.ker) :
    (QuotientGroup.lift N q hN).ker ≤ center (D ⧸ N) := by
  intro x hx
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective N x
  apply mem_center_iff.mpr
  intro y
  obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective N y
  exact congrArg (QuotientGroup.mk' N) (mem_center_iff.mp (hc hx) e)

end CentralDerivedKernel
