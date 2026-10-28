module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.Exclude1512.SeedOrders.Enumeration

/-!
# Orders of the two explicit nine-point seed groups

The first seed has order 504 by the kernel-checked enumeration in the companion
module. The permutation fixing 0, 1 and 2 and multiplying the seven-cycle's
coordinates by 3 conjugates the first seed to the second. Four pointwise word
identities prove both subgroup containments, so the second seed has the same
order. This proves the orders of the actual generated subgroups, without a
recognition theorem or a comparison with a projective model.

Application: condition K in the alternating case of Aschbacher–Smith,
`refs/quasithin.pdf`, printed pp.4 and 482.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction.Exclude1512

private def conjugator : Perm where
  toFun := ![0, 1, 2, 5, 8, 4, 7, 3, 6]
  invFun := ![0, 1, 2, 7, 5, 3, 8, 6, 4]
  left_inv := by decide
  right_inv := by decide

private theorem cycle_mem (b : Bool) : cycle ∈ seed b :=
  Subgroup.subset_closure (by simp)

private theorem involution_mem (b : Bool) : involution b ∈ seed b :=
  Subgroup.subset_closure (by simp)

private theorem conjugate_cycle : conjugator * cycle * conjugator⁻¹ = cycle ^ 3 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

private theorem conjugate_involution : conjugator * involution false * conjugator⁻¹ =
    cycle ^ 3 * involution true * cycle ^ 2 * involution true *
      cycle ^ 2 * involution true * cycle ^ 3 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

private theorem preimage_cycle : (MulAut.conj conjugator) (cycle ^ 5) = cycle := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

private theorem preimage_involution : (MulAut.conj conjugator)
    (cycle ^ 2 * involution false * cycle * involution false * cycle ^ 2) =
      involution true := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

private theorem closure_pair_le {G : Type*} [Group G] (a b : G) (K : Subgroup G)
    (ha : a ∈ K) (hb : b ∈ K) : Subgroup.closure {a, b} ≤ K := by
  apply (Subgroup.closure_le K).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact ha
  · exact (Set.mem_singleton_iff.mp hx) ▸ hb

private theorem map_pair_eq {G : Type*} [Group G] (a b c d : G) (e : G ≃* G)
    (ha : e a ∈ Subgroup.closure {c, d}) (hb : e b ∈ Subgroup.closure {c, d})
    (hc : c ∈ (Subgroup.closure {a, b}).map e.toMonoidHom)
    (hd : d ∈ (Subgroup.closure {a, b}).map e.toMonoidHom) :
    (Subgroup.closure {a, b}).map e.toMonoidHom = Subgroup.closure {c, d} := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr (closure_pair_le a b _ ha hb)
  · exact closure_pair_le c d _ hc hd

private theorem image_cycle_mem :
    (MulAut.conj conjugator) cycle ∈ seed true := by
  change conjugator * cycle * conjugator⁻¹ ∈ seed true
  rw [conjugate_cycle]
  exact (seed true).pow_mem (cycle_mem true) 3

private theorem image_involution_mem :
    (MulAut.conj conjugator) (involution false) ∈ seed true := by
  change conjugator * involution false * conjugator⁻¹ ∈ seed true
  rw [conjugate_involution]
  have hc := cycle_mem true
  have ht := involution_mem true
  have hc2 := (seed true).pow_mem hc 2
  have hc3 := (seed true).pow_mem hc 3
  exact (seed true).mul_mem
    ((seed true).mul_mem
      ((seed true).mul_mem
        ((seed true).mul_mem ((seed true).mul_mem ((seed true).mul_mem hc3 ht) hc2) ht)
        hc2) ht) hc3

private theorem cycle_mem_image :
    cycle ∈ (seed false).map (MulAut.conj conjugator).toMonoidHom :=
  ⟨cycle ^ 5, (seed false).pow_mem (cycle_mem false) 5, preimage_cycle⟩

private theorem involution_mem_image :
    involution true ∈ (seed false).map (MulAut.conj conjugator).toMonoidHom := by
  refine ⟨cycle ^ 2 * involution false * cycle * involution false * cycle ^ 2,
    ?_, preimage_involution⟩
  have hc := cycle_mem false
  have ht := involution_mem false
  have hc2 := (seed false).pow_mem hc 2
  exact (seed false).mul_mem
    ((seed false).mul_mem ((seed false).mul_mem ((seed false).mul_mem hc2 ht) hc) ht) hc2

private theorem conjugate_seed :
    (seed false).map (MulAut.conj conjugator).toMonoidHom = seed true :=
  map_pair_eq cycle (involution false) cycle (involution true) (MulAut.conj conjugator)
    image_cycle_mem image_involution_mem cycle_mem_image involution_mem_image

/-- Both explicit pairs generate a subgroup of order 504. -/
public theorem seed_card (b : Bool) : Nat.card (seed b) = 504 := by
  cases b
  · exact SeedEnumeration.card_false
  · calc
      Nat.card (seed true) = Nat.card (seed false) := by
        rw [← conjugate_seed]
        exact (Nat.card_congr
          ((MulAut.conj conjugator).subgroupMap (seed false)).toEquiv).symm
      _ = 504 := SeedEnumeration.card_false

end CFSG.Quasithin.MainConverse.NineReduction.Exclude1512
