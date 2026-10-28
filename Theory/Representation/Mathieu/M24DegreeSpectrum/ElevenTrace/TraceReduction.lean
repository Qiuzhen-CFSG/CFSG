module
public import Theory.Representation.PRegularTrace
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.TracePowers

/-!
# From odd square conjugacy to binary traces

The p-regular reduction replaces each element by an odd-order element with
the same trace. Square conjugacy fixes that trace under Frobenius because
in characteristic two the trace of a square is the square of the trace.
No irreducibility or field-of-definition hypothesis is used. The M₂₄
application supplies the native group fusion in `ElevenTrace`.
-/

public section
namespace Representation

/-- Characteristic-two traces are binary valued if squaring preserves every odd class. -/
theorem character_sq_of_odd_square_conjugacy
    {G K W : Type*} [Group G] [Finite G] [Field K] [CharP K 2]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K G W)
    (h : ∀ g : G, ¬ 2 ∣ orderOf g → IsConj g (g ^ 2)) (g : G) :
    ρ.character g ^ 2 = ρ.character g := by
  obtain ⟨x, hx, he⟩ := exists_pRegular_same_character (F := K) 2 g
  rw [he W ρ, ← character_sq_charTwo]
  obtain ⟨c, hc⟩ := isConj_iff.mp (h x hx)
  rw [← hc, char_conj]

end Representation
