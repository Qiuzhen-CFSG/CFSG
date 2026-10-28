module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.Torus

/-!
# Cardinality of the literal fixed Ree torus

The two long simple-root characters give an isomorphism from two copies of
the coefficient field's unit group onto `Parabolics.fixedTorus m`. The
underlying parametrization is the inverse diagonal matrix with characters
`b, c, theta(c), theta(b)`, matching the convention `T⁻¹ * x * T`.

The imported torus construction proves both membership in the coroot-word
torus and exhaustiveness: twisting root conjugation forces the exceptional
character equations, and the inverse F₄ Cartan matrix recovers all four
coordinates. Thus counting the parameters gives `(2^(2*m+1)-1)^2`, without
any assumption on the ambient Ree order or simplicity. This includes `m = 0`.

This supplies exactly `ht` in `Order.card_model_of_torus_and_cells`; the
inversion-subgroup counts remain with that theorem's assembly owner.

Source: GLS3, Table 2.2 and §§2.3–2.4, `refs/KGroup/GLS3/chapter2.tex`.
Our field size `2^(2*m+1)` is the square of GLS3's half-integer parameter.
-/

@[expose] public noncomputable section

namespace ReeF4.CentralCovers.OddPrimary.Order
open Parabolics ConverseParabolics.FullLeviRepresentation

/-- The two long-root characters parametrize the literal fixed coroot torus.
The representative is the inverse diagonal matrix in the defining representation. -/
def fixedTorusEquiv (m : ℕ) :
    (CoefficientField m)ˣ × (CoefficientField m)ˣ ≃* fixedTorus m :=
  MulEquiv.ofBijective
    ((torusHom m).codRestrict (fixedTorus m) fun bc => torusElement_mem bc.1 bc.2)
    ⟨fun _ _ h => torusHom_injective m (congrArg Subtype.val h), by
      intro x
      obtain ⟨b, c, h⟩ := exists_torusElement x.val x.property
      exact ⟨(b, c), Subtype.ext h⟩⟩

@[simp] theorem fixedTorusEquiv_apply (m : ℕ)
    (bc : (CoefficientField m)ˣ × (CoefficientField m)ˣ) :
    (fixedTorusEquiv m bc : Model m) = torusElement bc.1 bc.2 := rfl

/-- The fixed intersection of the coroot-word torus has order `(q-1)^2`.
This also holds at the full binary Ree endpoint. -/
theorem card_fixedTorus (m : ℕ) :
    Nat.card (fixedTorus m) = (2 ^ (2 * m + 1) - 1) ^ 2 := by
  rw [← Nat.card_congr (fixedTorusEquiv m).toEquiv, Nat.card_prod,
    Nat.card_units, field_card, pow_two]

end ReeF4.CentralCovers.OddPrimary.Order
