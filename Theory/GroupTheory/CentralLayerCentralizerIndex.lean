module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# A centralizer index bound from a central layer of index two

Let Z≤U be subgroups of a finite group P, with Z central in P, U/Z of
order two, and [P,U]≤Z. Then the index of C_P(U) is at most |Z|.
The supplied subgroup U is retained; no elementary or Sylow hypothesis is
required.

Choose u∈U outside Z. Centrality of [u,p] makes p↦[u,p] a homomorphism
from P to Z. Its kernel is C_P(U): an element centralizing u already
centralizes Z, and the two cosets of Z cover U. The kernel-index formula
therefore identifies the required index with an image of cardinality at
most |Z|.

This is the centralizer count for W*=C_Qmiddle(W₀) in Stellmacher
(10.1)(a3), printed p.61 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup
open scoped commutatorElement

public theorem centralizer_index_le_card_of_central_index_two_layer
    {P : Type*} [Group P] [Finite P]
    (U Z : Subgroup P) (_hZU : Z ≤ U) (hZ : Z ≤ center P)
    (hindex : (Z.subgroupOf U).index = 2) (hcomm : ⁅(⊤ : Subgroup P),U⁆ ≤ Z) :
    (centralizer (U : Set P)).index ≤ Nat.card Z := by
  classical
  have hnot : ¬ U ≤ Z := by
    intro hle
    have heq : Z.subgroupOf U = ⊤ := (subgroupOf_eq_top).mpr hle
    rw [heq,index_top] at hindex
    contradiction
  obtain ⟨u,hu,huZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hvalue (p : P) : ⁅u,p⁆ ∈ Z := by
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator hu (mem_top p)
  let displacement : P →* Z := {
    toFun := fun p => ⟨⁅u,p⁆,hvalue p⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro p q
      apply Subtype.ext
      change ⁅u,p*q⁆ = ⁅u,p⁆*⁅u,q⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc := mem_center_iff.mp (hZ (hvalue q)) p
      calc
        _ = ⁅u,p⁆*(p*⁅u,q⁆)*p⁻¹ := by group
        _ = _ := by rw [hc]; group }
  have hker : displacement.ker = centralizer (U : Set P) := by
    apply le_antisymm
    · intro p hp
      have hup : Commute u p := commutatorElement_eq_one_iff_commute.mp
        (congrArg Subtype.val (MonoidHom.mem_ker.mp hp))
      rw [mem_centralizer_iff]
      intro w hw
      by_cases hwZ : w∈Z
      · exact (mem_center_iff.mp (hZ hwZ) p).symm
      have hprod : u⁻¹*w∈Z := by
        have hh : (⟨u,hu⟩:U)⁻¹*⟨w,hw⟩ ∈ Z.subgroupOf U := by
          rw [mul_mem_iff_of_index_two hindex]
          change u⁻¹∈Z ↔ w∈Z
          simp [huZ,hwZ]
        exact hh
      have hz : Commute (u⁻¹*w) p :=
        (mem_center_iff.mp (hZ hprod) p).symm
      have hm := hup.mul_left hz
      simpa only [mul_inv_cancel_left] using hm.eq
    · intro p hp
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_commute.mpr
        (mem_centralizer_iff.mp hp u hu)
  rw [← hker,index_ker]
  exact Nat.card_le_card_of_injective displacement.range.subtype Subtype.val_injective

end Subgroup
