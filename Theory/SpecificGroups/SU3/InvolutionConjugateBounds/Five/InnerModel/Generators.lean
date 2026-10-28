module

public import Theory.Alternating.SevenInvolutionGeneration
import Mathlib.Tactic.FinCases

/-!
# The involutory generating triple for A₇

Apply the proved three-conjugate generation theorem to the double
transposition (01)(23), and package its generators as a `Fin 3` tuple.
The conclusion uses subgroup closure, as required by the actual maximal-A₇
calculation for PSU₃(5).

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11. The intrinsic alternating-group calculation is in
`Theory.Alternating.SevenInvolutionGeneration`.
-/

public section

open Subgroup Equiv
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five

/-- Three elements of order two generate the actual alternating group on seven letters. -/
theorem alternatingSeven_involution_generators :
    ∃ t : Fin 3 → alternatingGroup (Fin 7),
      (∀ i, orderOf (t i) = 2) ∧ closure (Set.range t) = ⊤ := by
  let x : alternatingGroup (Fin 7) :=
    ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
  have hx1 : x ≠ 1 := by decide +kernel
  have hx2 : x ^ 2 = 1 := by decide +kernel
  have hx : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  obtain ⟨g, h, hgen⟩ := alternatingGroup.SevenInvolutionGeneration.three_conjugates_generate x hx1 hx2
  let t : Fin 3 → alternatingGroup (Fin 7) := ![x, g * x * g⁻¹, h * x * h⁻¹]
  refine ⟨t, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hx
    · exact ((MulAut.conj g).orderOf_eq x).trans hx
    · exact ((MulAut.conj h).orderOf_eq x).trans hx
  · apply top_unique
    rw [← hgen]
    apply sup_le
    · apply sup_le
      · exact zpowers_le.mpr (subset_closure ⟨0, rfl⟩)
      · exact zpowers_le.mpr (subset_closure ⟨1, rfl⟩)
    · exact zpowers_le.mpr (subset_closure ⟨2, rfl⟩)

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five
