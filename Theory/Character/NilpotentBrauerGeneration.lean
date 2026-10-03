module

public import Theory.Character.NilpotentBrauerEvaluation
public import Theory.Character.NilpotentBrauerLocal

/-!
# Integral Brauer generation from nilpotent subgroups

To generate all ordinary characters integrally from nilpotent subgroups, it
suffices that a generator survives evaluation at each group element modulo
each maximal ideal of the algebraic integers. The maximal-ideal description
and the ideal property then show that the integer span contains one, and the
projection formula gives every character.

Local nonvanishing is supplied by the elementary centralizer construction and
cyclic Fourier orthogonality. This proves the generation theorem over ℤ,
retaining the conditional assembly lemmas as reusable interfaces.
Source: the character-ring proof of Brauer induction, Serre,
*Linear Representations of Finite Groups*, Chapter 10.
-/

public section
noncomputable section

namespace BrauerInduction
variable {G : Type*} [Group G] [Fintype G]

/-- Local nonvanishing of elements of the span excludes every maximal ideal. -/
theorem character_mem_nilpotentInducedSpan_of_local
    (hlocal : ∀ (g : G) (P : Ideal (integralClosure ℤ ℂ)), P.IsMaximal →
      ∃ f : characterRing G,
        f.val ∈ nilpotentInducedSpan G ∧ characterEvaluation g f ∉ P)
    {f : ClassFunction G} (hf : IsCharacter f) :
    f ∈ nilpotentInducedSpan G := by
  apply character_mem_nilpotentInducedSpan_of_maximal _ hf
  intro M hM
  let := hM
  obtain ⟨g, P, hP, rfl⟩ := exists_maximal_evaluation M
  obtain ⟨f, hf, hnot⟩ := hlocal g P hP
  exact ⟨f, hf, hnot⟩

/-- The irreducible-character target follows from local nonvanishing, with
integer coefficients throughout. -/
theorem irreducible_mem_nilpotentInducedSpan_of_local
    (hlocal : ∀ (g : G) (P : Ideal (integralClosure ℤ ℂ)), P.IsMaximal →
      ∃ f : characterRing G,
        f.val ∈ nilpotentInducedSpan G ∧ characterEvaluation g f ∉ P)
    (χ : ConjClassFunction G) (hχ : IsIrreducibleConjCharacter χ) :
    ofConjClassFunction χ ∈ nilpotentInducedSpan G := by
  apply character_mem_nilpotentInducedSpan_of_local hlocal
  obtain ⟨n, ρ, rfl⟩ := hχ.1
  rw [ofConjClassFunction_characterClassFunction]
  exact ⟨n, ρ, rfl⟩

/-- Every ordinary character is an integer linear combination of characters
induced from nilpotent subgroups. -/
theorem character_mem_nilpotentInducedSpan
    {f : ClassFunction G} (hf : IsCharacter f) :
    f ∈ nilpotentInducedSpan G :=
  character_mem_nilpotentInducedSpan_of_local local_nonvanishing hf

/-- Every irreducible ordinary character is an integer linear combination of
characters induced from nilpotent subgroups. -/
theorem irreducible_mem_nilpotentInducedSpan
    (χ : ConjClassFunction G) (hχ : IsIrreducibleConjCharacter χ) :
    ofConjClassFunction χ ∈ nilpotentInducedSpan G :=
  irreducible_mem_nilpotentInducedSpan_of_local local_nonvanishing χ hχ

end BrauerInduction
