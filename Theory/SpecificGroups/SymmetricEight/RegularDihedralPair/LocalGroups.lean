module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.CubicCatalogue
public import Mathlib.GroupTheory.Complement

/-! The four actual S₄ overgroups, retaining their inclusion in S₈. -/

@[expose] public section
open Equiv Subgroup
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair

def localGroup (j : Fin 4) : Subgroup P8 := closure (Set.range ![r,s,cubic j])

theorem local_generator_mem (j : Fin 4) (k : Fin 3) :
    (![r,s,cubic j] : Fin 3 → P8) k ∈ localGroup j := subset_closure ⟨k, rfl⟩

theorem twoGroup_le_localGroup (j : Fin 4) : twoGroup ≤ localGroup j := by
  rintro _ ⟨i, rfl⟩
  exact (localGroup j).mul_mem ((localGroup j).pow_mem (local_generator_mem j 0) _)
    ((localGroup j).pow_mem (local_generator_mem j 1) _)

theorem cubic_mem_localGroup (j : Fin 4) : cubic j ∈ localGroup j := local_generator_mem j 2

theorem localGroup_le {Q : Subgroup P8} (j : Fin 4)
    (hT : twoGroup ≤ Q) (hc : cubic j ∈ Q) : localGroup j ≤ Q := by
  apply (closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact hT r_mem
  · exact hT s_mem
  · exact hc

private def cubicFour : Perm (Fin 4) := swap 0 1 * swap 1 2

private theorem cubicFour_order : orderOf cubicFour = 3 :=
  orderOf_eq_prime (by decide) (by decide)

local instance : Fintype (Perm (Fin 4)) := fintypePerm

private theorem symmetricFour_relations (a b : Perm (Fin 4))
    (ha : a ^ 3 = 1) (hna : a ≠ 1) (hb : b ^ 4 = 1) (hnb : b ^ 2 ≠ 1) :
    (a * b ^ 2) ^ 3 = 1 ∧ (a * b) ^ 4 = 1 := by
  decide +revert +kernel

/-- Every actual S₄ overgroup in the ambient group is one of the four displayed
subgroups; the Sylow hypothesis is used in the cubic classification. -/
theorem symmetricFour_classification {X : Subgroup P8} (hX : MaximalTwo X)
    (A : Subgroup P8) (hAX : A ≤ X) (hT : twoGroup ≤ A)
    (e : A ≃* Perm (Fin 4)) : ∃ j : Fin 4, A = localGroup j := by
  let a : A := e.symm cubicFour
  have haorder : orderOf a = 3 := (e.symm.orderOf_eq cubicFour).trans cubicFour_order
  have ha3 : a ^ 3 = 1 := haorder ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by intro h; simp [h] at haorder
  let b : A := ⟨r, hT r_mem⟩
  have hb4 : b ^ 4 = 1 := Subtype.ext r_four
  have hb2 : b ^ 2 ≠ 1 := fun h => r_square_ne (congrArg Subtype.val h)
  have hr := symmetricFour_relations (e a) (e b)
    (by simp only [← map_pow, ha3, map_one])
    (fun h => ha1 (e.injective (h.trans (map_one e).symm)))
    (by simp only [← map_pow, hb4, map_one])
    (fun h => hb2 (e.injective (by simpa only [map_pow, map_one] using h)))
  have hcrit : Criterion (a : P8) := by
    refine ⟨congrArg Subtype.val ha3, fun h => ha1 (Subtype.ext h), ?_, ?_⟩
    · have h : (a * b ^ 2) ^ 3 = 1 := e.injective (by
        simpa only [map_pow, map_mul, map_one] using hr.1)
      exact congrArg A.subtype h
    · have h : (a * b) ^ 4 = 1 := e.injective (by
        simpa only [map_pow, map_mul, map_one] using hr.2)
      exact congrArg A.subtype h
  obtain ⟨j, i, hi⟩ := cubic_catalogue hX a (hAX a.property) hcrit
  have hcA : cubic j ∈ A := by
    have ht := hT (tWord_mem i)
    have hh := A.mul_mem (A.mul_mem (A.inv_mem ht) a.property) ht
    simpa only [hi, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  have hAcard : Nat.card A = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hTcard : Nat.card (twoGroup.subgroupOf A) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hT).toEquiv).trans twoGroup_card
  have hCcard : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, haorder]
  have hcomp : (twoGroup.subgroupOf A).IsComplement' (zpowers a) :=
    isComplement'_of_coprime (by rw [hTcard, hCcard, hAcard])
      (by rw [hTcard, hCcard]; decide)
  refine ⟨j, le_antisymm ?_ (localGroup_le j hT hcA)⟩
  have haQ : (a : P8) ∈ localGroup j := by
    rw [hi]
    exact (localGroup j).mul_mem
      ((localGroup j).mul_mem (twoGroup_le_localGroup j (tWord_mem i))
        (cubic_mem_localGroup j))
      ((localGroup j).inv_mem (twoGroup_le_localGroup j (tWord_mem i)))
  have hC : zpowers a ≤ (localGroup j).subgroupOf A := zpowers_le.mpr haQ
  intro x hx
  obtain ⟨⟨t, z⟩, htz⟩ := hcomp.2 (⟨x, hx⟩ : A)
  have he : ((t : A) : P8) * ((z : A) : P8) = x := congrArg Subtype.val htz
  rw [← he]
  exact (localGroup j).mul_mem (twoGroup_le_localGroup j t.property) (hC z.property)

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
