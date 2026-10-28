module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.ClosureSwap
public import Theory.ElementaryAbelian.Quotient
import Mathlib.Tactic

/-!
# Two transverse matching subgroups of the symmetric six-group

The matchings `01|23|45` and `05|12|34` are conjugate by an even permutation.
Every nonidentity element of the second matching subgroup other than its three
individual swaps generates the whole symmetric group together with the first.
The proof uses only the eight binary matching words and transposition paths.

This is the displayed six-letter calculation following (12.7.18), printed
p. 846, in Aschbacher--Smith. It does not identify this six-letter action with
the coordinate permutation action on the hexacode.
-/

public section

namespace Theory.SpecificGroups.SymmetricSix.MatchingEightGeneration

open Equiv Subgroup

/-- Independent swaps within the three displayed matching pairs. -/
@[expose] def matchingEight : Subgroup (Perm (Fin 6)) :=
  closure {swap 0 1, swap 2 3, swap 4 5}

/-- The transverse matching used in the generation calculation. -/
@[expose] def shiftedMatchingEight : Subgroup (Perm (Fin 6)) :=
  closure {swap 0 5, swap 1 2, swap 3 4}

private def matchingWordHom (shifted : Bool) :
    Multiplicative (Fin 3 → ZMod 2) →* Perm (Fin 6) where
  toFun v := if shifted then
    swap 0 5 ^ (v.toAdd 0).val * swap 1 2 ^ (v.toAdd 1).val *
      swap 3 4 ^ (v.toAdd 2).val
    else swap 0 1 ^ (v.toAdd 0).val * swap 2 3 ^ (v.toAdd 1).val *
      swap 4 5 ^ (v.toAdd 2).val
  map_one' := by cases shifted <;> decide +kernel
  map_mul' := by cases shifted <;> decide +kernel

private theorem matchingWordHom_range (s : Bool) :
    (matchingWordHom s).range = if s then shiftedMatchingEight else matchingEight := by
  cases s <;> apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact mul_mem (mul_mem
      (pow_mem (subset_closure (by simp)) _)
      (pow_mem (subset_closure (by simp)) _))
      (pow_mem (subset_closure (by simp)) _)
  · apply (closure_le _).mpr
    rintro _ (rfl | rfl | rfl)
    · exact ⟨Multiplicative.ofAdd ![1, 0, 0], by decide +kernel⟩
    · exact ⟨Multiplicative.ofAdd ![0, 1, 0], by decide +kernel⟩
    · exact ⟨Multiplicative.ofAdd ![0, 0, 1], by decide +kernel⟩
  · rintro _ ⟨v, rfl⟩
    exact mul_mem (mul_mem
      (pow_mem (subset_closure (by simp)) _)
      (pow_mem (subset_closure (by simp)) _))
      (pow_mem (subset_closure (by simp)) _)
  · apply (closure_le _).mpr
    rintro _ (rfl | rfl | rfl)
    · exact ⟨Multiplicative.ofAdd ![1, 0, 0], by decide +kernel⟩
    · exact ⟨Multiplicative.ofAdd ![0, 1, 0], by decide +kernel⟩
    · exact ⟨Multiplicative.ofAdd ![0, 0, 1], by decide +kernel⟩

/-- Both displayed matching subgroups have exactly eight elements. -/
theorem matching_card : Nat.card matchingEight = 8 ∧ Nat.card shiftedMatchingEight = 8 := by
  have hh (s : Bool) : Nat.card (matchingWordHom s).range = 8 := by
    have hinj : Function.Injective (matchingWordHom s) := by
      cases s <;> decide +kernel
    let e := Equiv.ofBijective (matchingWordHom s).rangeRestrict
      ⟨fun _ _ h => hinj (congrArg Subtype.val h),
        (matchingWordHom s).rangeRestrict_surjective⟩
    rw [← Nat.card_congr e]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact ⟨by simpa [matchingWordHom_range] using hh false,
    by simpa [matchingWordHom_range] using hh true⟩

/-- These order-eight groups are elementary abelian. -/
theorem matching_elementary : IsElementaryAbelian 2 matchingEight ∧
    IsElementaryAbelian 2 shiftedMatchingEight := by
  let : IsElementaryAbelian 2 (Multiplicative (Fin 3 → ZMod 2)) := {
    is_comm.comm := mul_comm
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel) }
  have hh (s : Bool) : IsElementaryAbelian 2 (matchingWordHom s).range :=
    IsElementaryAbelian.of_surjective (matchingWordHom s).rangeRestrict
      (matchingWordHom s).rangeRestrict_surjective
  have he0 : (matchingWordHom false).range = matchingEight := matchingWordHom_range false
  have he1 : (matchingWordHom true).range = shiftedMatchingEight := matchingWordHom_range true
  exact ⟨(congrArg (fun K : Subgroup (Perm (Fin 6)) => IsElementaryAbelian 2 K) he0).mp
      (hh false),
    (congrArg (fun K : Subgroup (Perm (Fin 6)) => IsElementaryAbelian 2 K) he1).mp
      (hh true)⟩

/-- The five-cycle `(1 5 4 3 2)` sends the first matching to the second. -/
theorem exists_even_matching_conjugator :
    ∃ g : alternatingGroup (Fin 6),
      matchingEight.map (MulAut.conj g.val).toMonoidHom = shiftedMatchingEight := by
  let g : Perm (Fin 6) := swap 1 2 * swap 1 3 * swap 1 4 * swap 1 5
  have hg : g ∈ alternatingGroup (Fin 6) := by
    change g.sign = 1
    decide +kernel
  refine ⟨⟨g, hg⟩, ?_⟩
  change (Subgroup.closure _).map _ = Subgroup.closure _
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  have h01 : (MulAut.conj g) (swap 0 1) = swap 0 5 := by decide +kernel
  have h23 : (MulAut.conj g) (swap 2 3) = swap 1 2 := by decide +kernel
  have h45 : (MulAut.conj g) (swap 4 5) = swap 3 4 := by decide +kernel
  constructor
  · rintro ⟨y, (rfl | rfl | rfl), rfl⟩
    · exact Or.inl h01
    · exact Or.inr (Or.inl h23)
    · exact Or.inr (Or.inr h45)
  · rintro (rfl | rfl | rfl)
    · exact ⟨swap 0 1, Or.inl rfl, h01⟩
    · exact ⟨swap 2 3, Or.inr (Or.inl rfl), h23⟩
    · exact ⟨swap 4 5, Or.inr (Or.inr rfl), h45⟩

private theorem top_of_star_swaps (H : Subgroup (Perm (Fin 6)))
    (h : ∀ i : Fin 6, swap 0 i ∈ H) : H = ⊤ := by
  apply top_unique
  rw [← Perm.closure_isSwap]
  apply (closure_le _).mpr
  rintro _ ⟨a, b, _, rfl⟩
  exact SubmonoidClass.swap_mem_trans H (by simpa [swap_comm] using h a) (h b)

private theorem matching_join_double_or_triple (x : Perm (Fin 6))
    (hx : x = swap 0 5 * swap 1 2 ∨ x = swap 0 5 * swap 3 4 ∨
      x = swap 1 2 * swap 3 4 ∨ x = swap 0 5 * swap 1 2 * swap 3 4) :
    matchingEight ⊔ zpowers x = ⊤ := by
  let H := matchingEight ⊔ zpowers x
  have h00 : swap (0 : Fin 6) 0 ∈ H := by rw [swap_self]; exact one_mem H
  have h01 : swap (0 : Fin 6) 1 ∈ H := mem_sup_left (subset_closure (by simp))
  have h23 : swap (2 : Fin 6) 3 ∈ H := mem_sup_left (subset_closure (by simp))
  have h45 : swap (4 : Fin 6) 5 ∈ H := mem_sup_left (subset_closure (by simp))
  have hconj {a b : Fin 6} (hab : swap a b ∈ H) : swap (x a) (x b) ∈ H := by
    rw [swap_apply_apply]
    exact mul_mem (mul_mem (mem_sup_right (mem_zpowers x)) hab)
      (inv_mem (mem_sup_right (mem_zpowers x)))
  have hc01 := hconj h01
  have hc23 := hconj h23
  have hc45 := hconj h45
  apply top_of_star_swaps
  rcases hx with rfl | rfl | rfl | rfl
  · change swap (5 : Fin 6) 2 ∈ H at hc01
    change swap (1 : Fin 6) 3 ∈ H at hc23
    change swap (4 : Fin 6) 0 ∈ H at hc45
    have h03 := SubmonoidClass.swap_mem_trans H h01 hc23
    have h02 := SubmonoidClass.swap_mem_trans H h03 (by simpa [swap_comm] using h23)
    have h04 : swap (0 : Fin 6) 4 ∈ H := by simpa [swap_comm] using hc45
    have h05 := SubmonoidClass.swap_mem_trans H h04 h45
    intro i; fin_cases i <;> assumption
  · change swap (5 : Fin 6) 1 ∈ H at hc01
    change swap (2 : Fin 6) 4 ∈ H at hc23
    change swap (3 : Fin 6) 0 ∈ H at hc45
    have h03 : swap (0 : Fin 6) 3 ∈ H := by simpa [swap_comm] using hc45
    have h02 := SubmonoidClass.swap_mem_trans H h03 (by simpa [swap_comm] using h23)
    have h04 := SubmonoidClass.swap_mem_trans H h02 hc23
    have h05 := SubmonoidClass.swap_mem_trans H h04 h45
    intro i; fin_cases i <;> assumption
  · change swap (0 : Fin 6) 2 ∈ H at hc01
    change swap (1 : Fin 6) 4 ∈ H at hc23
    change swap (3 : Fin 6) 5 ∈ H at hc45
    have h03 := SubmonoidClass.swap_mem_trans H hc01 h23
    have h04 := SubmonoidClass.swap_mem_trans H h01 hc23
    have h05 := SubmonoidClass.swap_mem_trans H h04 h45
    intro i; fin_cases i <;> assumption
  · change swap (5 : Fin 6) 2 ∈ H at hc01
    change swap (1 : Fin 6) 4 ∈ H at hc23
    change swap (3 : Fin 6) 0 ∈ H at hc45
    have h03 : swap (0 : Fin 6) 3 ∈ H := by simpa [swap_comm] using hc45
    have h02 := SubmonoidClass.swap_mem_trans H h03 (by simpa [swap_comm] using h23)
    have h04 := SubmonoidClass.swap_mem_trans H h01 hc23
    have h05 := SubmonoidClass.swap_mem_trans H h04 h45
    intro i; fin_cases i <;> assumption

/-- Each nonswap nonidentity element of the transverse matching generates `S₆`
together with the original matching. -/
theorem matching_join_eq_top (x : Perm (Fin 6)) (hx : x ∈ shiftedMatchingEight)
    (hne : x ≠ 1) (hswap : ¬x.IsSwap) : matchingEight ⊔ zpowers x = ⊤ := by
  have hx' : x ∈ (matchingWordHom true).range := by
    simpa [matchingWordHom_range] using hx
  obtain ⟨v, rfl⟩ := hx'
  apply matching_join_double_or_triple
  have classification : ∀ v : Multiplicative (Fin 3 → ZMod 2),
      matchingWordHom true v = 1 ∨
      (matchingWordHom true v).IsSwap ∨
      matchingWordHom true v = swap 0 5 * swap 1 2 ∨
      matchingWordHom true v = swap 0 5 * swap 3 4 ∨
      matchingWordHom true v = swap 1 2 * swap 3 4 ∨
      matchingWordHom true v = swap 0 5 * swap 1 2 * swap 3 4 := by
    unfold Perm.IsSwap
    decide +kernel
  exact ((classification v).resolve_left hne).resolve_left hswap

end Theory.SpecificGroups.SymmetricSix.MatchingEightGeneration
