module

public import Theory.Mathieu.M12.SylowOvergroups.Representatives
public import Theory.Mathieu.M12.SylowOvergroups.Tables
public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.Order
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry

/-!+# Prime-order obstructions to small Sylow overgroups in M₁₂

Each of the proposed double-coset representatives either belongs to one of
the two marked parabolics or, together with the Sylow subgroup, produces an
element of order five or eleven. The kernel checks the explicit short words.
Consequently, once double-coset coverage is established, every Sylow overgroup
whose order is prime to 55 lies in one of the two parabolics and has order at
most 192. No coverage or classification theorem is asserted unconditionally.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511; the M₁₂ entries of
Aschbacher's *Overgroups of Sylow subgroups in sporadic groups* (1986) and
GLS3 Table 5.3b. The proof uses the actual Witt-design permutation model.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups
open SylowEnumeration

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem representative_zero : representative 0 = 1 := by decide +kernel

theorem representative_37_mem_first : representative 37 ∈ firstParabolic := by
  rw [mem_firstParabolic_iff]
  decide +kernel

theorem representative_41_mem_second : representative 41 ∈ secondParabolic := by
  rw [mem_secondParabolic_iff]
  decide +kernel

/-- The three exceptional indices are exactly the representatives used in the
two marked parabolics; every other index has a checked prime-order word. -/
theorem obstruction_order : ∀ i : Fin 44, i = 0 ∨ i = 37 ∨ i = 41 ∨
    orderOf (obstruction i) = 5 ∨ orderOf (obstruction i) = 11 := by
  have h : ∀ i : Fin 44, i = 0 ∨ i = 37 ∨ i = 41 ∨
      (obstructionPerm i ≠ 1 ∧ obstructionPerm i ^ 5 = 1) ∨
      (obstructionPerm i ≠ 1 ∧ obstructionPerm i ^ 11 = 1) := by decide +kernel
  intro i
  rcases h i with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · right; right; right; left
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    rw [← orderOf_injective M12.subtype M12.subtype_injective]
    change orderOf (obstruction i).val = 5
    rw [obstruction_perm]
    exact orderOf_eq_prime h.2 h.1
  · right; right; right; right
    let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
    rw [← orderOf_injective M12.subtype M12.subtype_injective]
    change orderOf (obstruction i).val = 11
    rw [obstruction_perm]
    exact orderOf_eq_prime h.2 h.1

theorem representative_mem_parabolic (H : Subgroup M12)
    (hS : sylowCandidate ≤ H) (h5 : ¬ 5 ∣ Nat.card H) (h11 : ¬ 11 ∣ Nat.card H)
    (i : Fin 44) (hi : representative i ∈ H) :
    representative i ∈ firstParabolic ∨ representative i ∈ secondParabolic := by
  rcases obstruction_order i with rfl | rfl | rfl | h | h
  · exact Or.inl (representative_zero ▸ firstParabolic.one_mem)
  · exact Or.inl representative_37_mem_first
  · exact Or.inr representative_41_mem_second
  · have hd := H.orderOf_dvd_natCard (localWord_mem H hS i hi (obstructionWords[i.val]!))
    change orderOf (obstruction i) ∣ Nat.card H at hd
    exact (h5 (h ▸ hd)).elim
  · have hd := H.orderOf_dvd_natCard (localWord_mem H hS i hi (obstructionWords[i.val]!))
    change orderOf (obstruction i) ∣ Nat.card H at hd
    exact (h11 (h ▸ hd)).elim

/-- Double-coset coverage converts the finite word checks into exhaustive
containment for all subgroups whose order is divisible by neither five nor eleven. -/
theorem parabolic_containment_of_covers (hcover : Covers) (H : Subgroup M12)
    (hS : sylowCandidate ≤ H) (h5 : ¬ 5 ∣ Nat.card H) (h11 : ¬ 11 ∣ Nat.card H) :
    H ≤ firstParabolic ∨ H ≤ secondParabolic := by
  apply SubgroupClass.subset_union.mp
  intro g hg
  obtain ⟨i, s, t, rfl⟩ := hcover g
  have hi : representative i ∈ H := by
    have h := H.mul_mem (H.mul_mem (H.inv_mem (hS s.property)) hg)
      (H.inv_mem (hS t.property))
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  rcases representative_mem_parabolic H hS h5 h11 i hi with h | h
  · exact Or.inl (firstParabolic.mul_mem
      (firstParabolic.mul_mem s.property.1 h) t.property.1)
  · exact Or.inr (secondParabolic.mul_mem
      (secondParabolic.mul_mem s.property.2 h) t.property.2)

/-- The exact cardinal bound used by the Sylow-pair exclusion. -/
theorem card_le_of_covers (hcover : Covers) (H : Subgroup M12)
    (hS : sylowCandidate ≤ H) (h5 : ¬ 5 ∣ Nat.card H) (h11 : ¬ 11 ∣ Nat.card H) :
    Nat.card H ≤ 192 := by
  rcases parabolic_containment_of_covers hcover H hS h5 h11 with h | h
  · simpa only [card_firstParabolic] using Subgroup.card_le_of_le h
  · simpa only [card_secondParabolic] using Subgroup.card_le_of_le h

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
