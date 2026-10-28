module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Offenders
import Mathlib.Tactic


/-!
# The natural transposition four-group and its conjugates

The two fixed pair-vectors have pointwise fixer exactly D. A five-cycle,
which is even, carries the two disjoint swaps to the complementary adjacent
swaps; the two four-groups therefore generate S₅. The standard eight-group
contains D and has the full two-part of S₅.

Source: Aschbacher–Smith, the S₅ calculations in C.1.24 and E.2.3,
printed pp.131 and 216–217.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.SymmetricFive
open BinaryPermutation Representation.BinaryOffender ChapterB.Offenders Subgroup Equiv
abbrev Sym := Perm (Fin 5)
private def firstPair : core (Fin 5) := ⟨![1,1,0,0,0], by rw [mem_core]; decide⟩
private def secondPair : core (Fin 5) := ⟨![0,0,1,1,0], by rw [mem_core]; decide⟩

theorem fixed_space_fixer_le_D (g : Sym)
    (hf : ∀ v ∈ fixedSpace (coreRepresentation (Fin 5)) (D 5),
      coreRepresentation (Fin 5) g v = v) : g ∈ D 5 := by
  have hfirst : firstPair ∈ fixedSpace (coreRepresentation (Fin 5)) (D 5) := by
    rw [core_fixed_disjointTranspositions_iff]
    decide
  have hsecond : secondPair ∈ fixedSpace (coreRepresentation (Fin 5)) (D 5) := by
    rw [core_fixed_disjointTranspositions_iff]
    decide
  have hc : ∀ g : Sym,
      representation (Fin 5) g firstPair.val = firstPair.val →
      representation (Fin 5) g secondPair.val = secondPair.val →
      g = 1 ∨ g = pairSwap 5 0 ∨ g = pairSwap 5 1 ∨ g = pairSwap 5 0 * pairSwap 5 1 := by
    decide +kernel
  rcases hc g (congrArg Subtype.val (hf firstPair hfirst))
      (congrArg Subtype.val (hf secondPair hsecond)) with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact pairSwap_mem 0 (by decide)
  · exact pairSwap_mem 1 (by decide)
  · exact mul_mem (pairSwap_mem 0 (by decide)) (pairSwap_mem 1 (by decide))

/-- The pointwise-fixer calculation respects the actual conjugate coordinates. -/
theorem fixed_space_fixer_le_conjugate_D (a g : Sym)
    (hf : ∀ v ∈ fixedSpace (coreRepresentation (Fin 5))
      ((D 5).map (MulAut.conj a).toMonoidHom), coreRepresentation (Fin 5) g v = v) :
    g ∈ (D 5).map (MulAut.conj a).toMonoidHom := by
  let ρ := coreRepresentation (Fin 5)
  have hg : a⁻¹ * g * a ∈ D 5 := by
    apply fixed_space_fixer_le_D
    intro v hv
    have hva : ρ a v ∈ fixedSpace ρ ((D 5).map (MulAut.conj a).toMonoidHom) := by
      rintro ⟨x, b, hb, rfl⟩
      change ρ (a * b * a⁻¹) (ρ a v) = ρ a v
      rw [map_mul, map_mul]
      simp only [Module.End.mul_apply]
      have hcancel : ρ a⁻¹ (ρ a v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      have hvb : ρ b v = v := hv ⟨b, hb⟩
      rw [hcancel, hvb]
    have hw := hf (ρ a v) hva
    change ρ g (ρ a v) = ρ a v at hw
    have hh := congrArg (ρ a⁻¹) hw
    change ρ (a⁻¹ * g * a) v = v
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, mul_assoc] using hh
  refine ⟨a⁻¹ * g * a, hg, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

def fiveCycle : Sym := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

theorem fiveCycle_even : fiveCycle ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide +kernel

theorem two_four_groups_generate : (D 5) ⊔ (D 5).map (MulAut.conj fiveCycle).toMonoidHom = ⊤ := by
  let X := (D 5) ⊔ (D 5).map (MulAut.conj fiveCycle).toMonoidHom
  have h01 : swap (0 : Fin 5) 1 ∈ X := Subgroup.mem_sup_left (pairSwap_mem 0 (by decide))
  have h23 : swap (2 : Fin 5) 3 ∈ X := Subgroup.mem_sup_left (pairSwap_mem 1 (by decide))
  have h12 : swap (1 : Fin 5) 2 ∈ X := by
    have h : (MulAut.conj fiveCycle) (pairSwap 5 0) = swap (1 : Fin 5) 2 := by decide +kernel
    rw [← h]
    exact Subgroup.mem_sup_right (mem_map_of_mem _ (pairSwap_mem 0 (by decide)))
  have h34 : swap (3 : Fin 5) 4 ∈ X := by
    have h : (MulAut.conj fiveCycle) (pairSwap 5 1) = swap (3 : Fin 5) 4 := by decide +kernel
    rw [← h]
    exact Subgroup.mem_sup_right (mem_map_of_mem _ (pairSwap_mem 1 (by decide)))
  apply Subgroup.toSubmonoid_injective
  apply top_unique
  rw [← Perm.mclosure_swap_castSucc_succ 4, Submonoid.closure_le]
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact h01
  · exact h12
  · exact h23
  · exact h34

theorem D_card : Nat.card (D 5) = 4 :=
  Odd.card_disjointTranspositions (Or.inl rfl) le_rfl
end CFSG.Quasithin.ChapterC.SymmetricFive
