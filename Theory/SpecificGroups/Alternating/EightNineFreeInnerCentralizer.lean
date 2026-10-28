module

public import Theory.Alternating.Aut
public import Theory.GroupAction.InnerCentralizerCardinality
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Involution centralizers in Aut(A₈) are nine-free

The genuine conjugation isomorphism S₈ ≃ Aut(A₈) takes the marked element
to its inner automorphism. An even involution has two or four transpositions;
the corresponding symmetric centralizers have orders 192 and 384.
Source: Aschbacher--Smith 14.3.20, printed p.998, the PSL₄(2) row.
-/

public section
open Subgroup Equiv.Perm
namespace alternatingGroup

/-- The bound concerns all automorphisms of the actual alternating carrier. -/
theorem eight_not_nine_dvd_inner_involution_centralizer
    (x : alternatingGroup (Fin 8)) (hx : orderOf x = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj x} :
      Set (MulAut (alternatingGroup (Fin 8))))) := by
  let e : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))
  have he : e (x : Equiv.Perm (Fin 8)) = MulAut.conj x := by
    ext y
    rfl
  rw [← he, ← Nat.card_congr
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e
      (x : Equiv.Perm (Fin 8))).toEquiv]
  have ho : orderOf (x : Equiv.Perm (Fin 8)) = 2 := (orderOf_coe x).trans hx
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hb := (x : Equiv.Perm (Fin 8)).sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hb
  have hs := mem_alternatingGroup.mp x.property
  rw [sign_of_cycleType', hk] at hs
  have hkb : k ≤ 3 := by omega
  rw [nat_card_centralizer, hk]
  interval_cases k
  · norm_num at hs
  · norm_num [Nat.factorial]
  · norm_num at hs
  · norm_num [Nat.factorial]

end alternatingGroup
