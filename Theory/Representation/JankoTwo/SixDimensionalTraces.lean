module

public import Theory.Representation.JankoTwo.SixDimensionalCertificate.TraceComparison

/-!
# Absolute degree-six trace rigidity for the literal Hall--Janko carrier

Two faithful six-dimensional representations over an algebraically closed
field of characteristic two have equal trace characters after precomposition
by the identity or `ExceptionalParabolics.involutionAut`. In particular this
applies to the faithful irreducible representations in the source statement;
the checked local geometry already forces their irreducibility.

The imported certificate proves completeness using simultaneous weights of
the literal ATLAS order-five pair, cubic commutator constraints, exhaustive
odd-order conjugacy coverage and p-regular trace reduction. Its outer marking
exchanges the two surviving weight patterns. Thus no representation catalogue,
carrier comparison, simplicity or recognition premise remains in this theorem.

Source: Hiss--Malle, corrected Table 2, degree-six characteristic-two J₂ entry
with field b5. Guralnick--Malle, Proposition 5.1, uses this degree-six case in
the sporadic analysis; its offender hypotheses are not used as a replacement
for trace completeness. See `SixDimensionalCertificate/Source.md` for the
checked proof route and ATLAS attribution. The application to the actual
marked constituent is in `SixDimensionalTraces.ConstituentDescent`.
-/

public section

namespace Representation.JankoTwo.SixDimensionalTraces

open Sporadic.LeechRelated.J2

universe v
variable {E : Type*} {U W : Type v}
  [Field E] [CharP E 2] [IsAlgClosed E]
  [AddCommGroup U] [Module E U] [FiniteDimensional E U]
  [AddCommGroup W] [Module E W] [FiniteDimensional E W]

/-- The trace-comparison automorphism can be chosen to be exactly the identity
or the checked outer involution on the literal ATLAS carrier. -/
theorem exists_character_eq_comp_one_or_involution
    (ρ : Representation E Carrier U) (τ : Representation E Carrier W)
    (hρ : Function.Injective ρ) (hτ : Function.Injective τ)
    (hdρ : Module.finrank E U = 6) (hdτ : Module.finrank E W = 6) :
    ∃ a : MulAut Carrier, (a = 1 ∨ a = ExceptionalParabolics.involutionAut) ∧
      ρ.character = Representation.character (τ.comp a.toMonoidHom) := by
  rcases SixDimensionalCertificate.character_eq_or_involutionTwist
    ρ τ hρ hτ hdρ hdτ with h | h
  · exact ⟨1, Or.inl rfl, h⟩
  · exact ⟨ExceptionalParabolics.involutionAut, Or.inr rfl, h⟩

/-- Absolute degree-six trace rigidity. Faithfulness and dimension six suffice;
in particular the conclusion holds for faithful irreducible representations. -/
theorem exists_character_eq_comp
    (ρ : Representation E Carrier U) (τ : Representation E Carrier W)
    (hρ : Function.Injective ρ) (hτ : Function.Injective τ)
    (hdρ : Module.finrank E U = 6) (hdτ : Module.finrank E W = 6) :
    ∃ a : MulAut Carrier, ρ.character = Representation.character (τ.comp a.toMonoidHom) := by
  obtain ⟨a, _, ha⟩ := exists_character_eq_comp_one_or_involution ρ τ hρ hτ hdρ hdτ
  exact ⟨a, ha⟩

end Representation.JankoTwo.SixDimensionalTraces
