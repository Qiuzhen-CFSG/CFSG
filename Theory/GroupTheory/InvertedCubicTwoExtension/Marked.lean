module

public import Theory.GroupTheory.InvertedCubicTwoExtension

/-!
# Marking the inverter in a cubic two-extension

A finite group with trivial two-core, a normal cubic subgroup and two-group
quotient is S₃ when an element inverts the cubic subgroup. The recognition
from `InvertedCubicTwoExtension` can be chosen to send that very inverter
to the transposition (1 2), while keeping the cubic subgroup equal to A₃.

After recognition, every inverter of A₃ is a transposition. Conjugating the
S₃ coordinates aligns it with (1 2); normality preserves the A₃ marking.
The finite permutation calculation is checked by the kernel.

Application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), covered paragraph, printed p.957.
-/

public section

open Subgroup
namespace InvertedCubicTwoExtension
variable {C : Type*} [Group C] [Finite C]
/-- Recognize the cubic subgroup and the specified inverter simultaneously. -/
theorem exists_equiv_preserving_cubic_and_inverter (X : Subgroup C) [X.Normal]
    (hX : Nat.card X = 3) (hquot : IsPGroup 2 (C ⧸ X))
    (hcore : pCore 2 C = ⊥)
    (c : C) (hc : ∀ x ∈ X, c * x * c⁻¹ = x⁻¹) :
    ∃ e : C ≃* Equiv.Perm (Fin 3),
      X.map e.toMonoidHom = alternatingGroup (Fin 3) ∧
      e c = Equiv.swap (1 : Fin 3) 2 := by
  obtain ⟨e, he⟩ := exists_equiv_preserving_cubic X hX hquot hcore c hc
  have hinv : ∀ x ∈ alternatingGroup (Fin 3), e c * x * (e c)⁻¹ = x⁻¹ := by
    intro x hx
    rw [← he] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change e c * e y * (e c)⁻¹ = (e y)⁻¹
    simpa only [map_mul, map_inv] using congrArg e (hc y hy)
  have hconj : ∀ t : Equiv.Perm (Fin 3),
      (∀ x ∈ alternatingGroup (Fin 3), t * x * t⁻¹ = x⁻¹) →
      ∃ a : Equiv.Perm (Fin 3), a * t * a⁻¹ = Equiv.swap (1 : Fin 3) 2 := by
    simp_rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  obtain ⟨a, ha⟩ := hconj (e c) hinv
  refine ⟨e.trans (MulAut.conj a), ?_, ha⟩
  change X.map ((MulAut.conj a).toMonoidHom.comp e.toMonoidHom) = _
  rw [← map_map, he]
  exact Normal.map_conj_eq _ a
end InvertedCubicTwoExtension
