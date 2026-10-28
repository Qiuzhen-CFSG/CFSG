module

public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.Decomposition

/-!
# The highest-root centralizer over the four-element field

All field units have cube one, so the whole centralizing torus is scalar.
The faithful unitriangular embedding therefore covers the projective
centralizer, which is a two-group. This uses the actual centralizer
factorization and does not identify groups from their orders.

Source: the small linear endpoint of the inner case in Aschbacher–Smith
16.4.8, printed p.1188.
-/

public section
open Matrix.PSL3Even.UnipotentGeometry

namespace Matrix.PSL3.EvenInnerCentralizers
variable (F : Type*) [Field F] [Finite F]

omit [Finite F] in
/-- The centralizing torus vanishes projectively over the four-element field. -/
theorem torus_eq_one_of_card_four (hF : Nat.card F = 4) (a : Fˣ) : torus F a = 1 := by
  apply (torus_eq_one_iff F a).mpr
  have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  simpa only [hc] using (pow_card_eq_one' (x := a))

omit [Finite F] in
/-- The entire marked centralizer is unitriangular at q = 4. -/
theorem unipotentInCentralizer_surjective_of_card_four [CharP F 2]
    (hF : Nat.card F = 4) : Function.Surjective (unipotentInCentralizer F) := by
  intro g
  obtain ⟨a,u,he⟩ := centralizer_factorization F g
  rw [torus_eq_one_of_card_four F hF, one_mul] at he
  exact ⟨u,he.symm⟩

/-- The marked projective involution centralizer over F₄ is a two-group. -/
theorem centralizer_isTwoGroup_of_card_four (hF : Nat.card F = 4) :
    IsPGroup 2 (centralizer F) := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF])
  let : CharP F 2 := ringChar.of_eq hc
  have hu : IsPGroup 2 (U F) := IsPGroup.of_card (n := 6) (by rw [card_U, hF]; rfl)
  exact hu.of_surjective (unipotentInCentralizer F)
    (unipotentInCentralizer_surjective_of_card_four F hF)

end Matrix.PSL3.EvenInnerCentralizers
