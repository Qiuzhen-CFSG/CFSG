module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.FieldReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.LargeFamily

/-!
# Assembly boundary for odd PSL₂ rank-one E-generation

Strong quasithinness reduces the actual model to an odd prime or prime-square
field. Rank-one actors are handled by the whole-group E2 construction; the
remaining two field cases require the large-family local witnesses below.
This is a conditional reduction, not a proof of E.1.14(6). The simple-socle
producer and both local geometry calculations must be supplied in the final
assembly, including diagonal and field two-automorphisms.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.3(2) and E.1.14(6), printed pp.33 and 214, with E.1.2's corrected local tau.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration

variable {G : Type*} [Group G] [Finite G]

/-- An actual application of the defining-field restriction to E-generation.
The three explicit inputs retain their independent proof obligations. -/
theorem isEGenerated_of_prime_and_square_calculations
    {K : GroupClass} (hG : IsSQTK K G) (L : Subgroup G) {q : ℕ}
    (hodd : Odd q) (hq : 5 < q) (hL : ClassicalGroup.IsPSL L 2 q)
    (hcomponent : ∀ (T : Sylow 2 G) (A : Subgroup G), IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → ECaseComponent (T : Subgroup G) A ⊤)
    (hprime : ∀ p : ℕ, p.Prime → Odd p → 5 < p → ClassicalGroup.IsPSL L 2 p →
      ∀ T : Sylow 2 G, LargeFamilyEscapeAt T)
    (hsquare : ∀ p : ℕ, p.Prime → Odd p → 5 < p ^ 2 →
      ClassicalGroup.IsPSL L 2 (p ^ 2) → ∀ T : Sylow 2 G, LargeFamilyEscapeAt T) :
    IsEGenerated 1 G := by
  apply isEGenerated_of_component_and_large_escape hcomponent
  obtain ⟨p, hp, hpo, hfield⟩ :=
    parameter_eq_prime_or_prime_sq hG.stronglyQuasithin L hodd hL
  rcases hfield with h | h
  · exact hprime p hp hpo (h ▸ hq) (h ▸ hL)
  · exact hsquare p hp hpo (h ▸ hq) (h ▸ hL)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration
