module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Marked
import Mathlib.Tactic
/-!
# Identification of the A₆ marked set with the source definition

Among the sixteen binary coordinate vectors, exactly the first three basis
vectors have transposition image and trivial central coordinate. Conjugation
by L preserves those properties. Combined with the even-conjugator construction,
this proves that the four constructed generators are exactly {z} ∪ (rᴸ ∩ A).
The calculation uses the actual marked product equivalence throughout.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.Six
open Equiv Equiv.Perm Subgroup
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem coordinateHom_transposition_iff (v : Binary) :
    ((coordinateHom v).1.cycleType = {2} ∧ (coordinateHom v).2 = 1) ↔
      ∃ i : Fin 4, i ≠ 3 ∧ v = basis i := by
  revert v; decide +kernel

variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

theorem lift_equiv (M : AlternatingProductModel L z r 6) (a : AlternatingOvergroup L z r) :
    lift M (M.equiv a) = (a : G) := by
  change (M.equiv.symm (M.equiv a) : G) = (a : G)
  rw [M.equiv.symm_apply_apply]

/-- Precisely the three noncentral generators are L-conjugate to r inside A. -/
theorem component_conjugate_mem_elementary_iff (M : AlternatingProductModel L z r 6) {a : G}
    (ha : a ∈ elementary M) :
    (∃ l ∈ L, MulAut.conj l r = a) ↔ ∃ i : Fin 4, i ≠ 3 ∧ a = generator M i := by
  constructor
  · rintro ⟨l, hl, he⟩
    obtain ⟨v, rfl⟩ := ha
    let ll : AlternatingOvergroup L z r := ⟨l, mem_sup_left (mem_sup_left hl)⟩
    let p := M.equiv ll
    have hv : coordinateHom v = p * (outerPermutation M, 1) * p⁻¹ := by
      apply lift_injective M
      rw [map_mul, map_mul, map_inv, lift_outer]
      change embedding M v = lift M (M.equiv ll) * r * (lift M (M.equiv ll))⁻¹
      rw [lift_equiv]
      exact he.symm
    have hp : p.2 = 1 := ((M.component_iff ll).mp hl).2
    have hc : IsConj (outerPermutation M) (coordinateHom v).1 := by
      apply isConj_iff.mpr
      refine ⟨p.1, ?_⟩
      simp only [hv, Prod.fst_mul, Prod.fst_inv]
    obtain ⟨i, hi, hvi⟩ := (coordinateHom_transposition_iff v).mp
      ⟨(isConj_iff_cycleType_eq.mp hc).symm.trans (outerPermutation_cycleType M), by simp [hv, hp]⟩
    exact ⟨i, hi, congrArg (embedding M) hvi⟩
  · rintro ⟨i, hi, rfl⟩
    exact generator_component_conjugate M i hi

/-- The constructed four-element set is exactly the source set {z} ∪ (rᴸ ∩ A). -/
theorem mem_alpha_iff (M : AlternatingProductModel L z r 6) (a : G) :
    a ∈ alpha M ↔ a = z ∨ (a ∈ elementary M ∧ ∃ l ∈ L, MulAut.conj l r = a) := by
  classical
  constructor
  · intro ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    by_cases hi : i = 3
    · exact Or.inl (hi ▸ generator_three M)
    · exact Or.inr ⟨generator_mem M i, generator_component_conjugate M i hi⟩
  · rintro (rfl | ⟨ha, hl⟩)
    · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, generator_three M⟩
    · obtain ⟨i, _, rfl⟩ := (component_conjugate_mem_elementary_iff M ha).mp hl
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end CFSG.Quasithin.Chapter16.Intersections.Six
