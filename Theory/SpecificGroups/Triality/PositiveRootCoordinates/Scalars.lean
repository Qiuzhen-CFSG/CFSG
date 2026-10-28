module

public import Theory.SpecificGroups.Triality.LeviFields
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Roots

/-!
# Scalar coordinates fixed by triality

The three length-three root orbits each contribute one parameter over GF(q³),
and the three singleton orbits each contribute one parameter in the actual
q-Frobenius fixed field. An explicit equivalence gives exactly q^12 fixed
coordinate tuples, for every prime power including q = 2.

This is the scalar calculation in GLS3, 2.3.6–7 and Table 2.4, type III
(`refs/KGroup/GLS3/chapter2.tex`). Identifying these tuples with fixed matrix
products still requires the normal form and its graph-field equivariance.
-/

@[expose] public section

namespace Triality.Standard.PositiveCoordinates
noncomputable section

abbrev Coordinates (P : Parameters) := Fin 12 → ExtensionField P

/-- Pull back the root permutation and apply coefficient q-Frobenius. -/
def twist (P : Parameters) (a : Coordinates P) : Coordinates P :=
  fun i => fieldFrobenius P (a (diagram.symm i))

theorem twist_eq_self_iff (P : Parameters) (a : Coordinates P) :
    twist P a = a ↔ ∀ i, a (diagram i) = fieldFrobenius P (a i) := by
  constructor
  · intro h i
    simpa only [twist, Equiv.symm_apply_apply] using (congrFun h (diagram i)).symm
  · intro h
    funext i
    simpa only [twist, Equiv.apply_symm_apply] using (h (diagram.symm i)).symm

abbrev FixedCoordinates (P : Parameters) := {a : Coordinates P // twist P a = a}
abbrev OrbitParameters (P : Parameters) :=
  (Fin 3 → ExtensionField P) × (Fin 3 → fixedField P)

/-- The coordinates on a triple are t, F(t), F²(t); singleton coordinates are fixed. -/
def expand (P : Parameters) (a : OrbitParameters P) : Coordinates P :=
  ![a.1 0, fieldFrobenius P (a.1 0), fieldFrobenius P (fieldFrobenius P (a.1 0)),
    a.2 0, a.1 1, fieldFrobenius P (a.1 1), fieldFrobenius P (fieldFrobenius P (a.1 1)),
    a.1 2, fieldFrobenius P (a.1 2), fieldFrobenius P (fieldFrobenius P (a.1 2)),
    a.2 1, a.2 2]

theorem expand_fixed (P : Parameters) (a : OrbitParameters P) :
    twist P (expand P a) = expand P a := by
  rw [twist_eq_self_iff]
  intro i
  have hf (j : Fin 3) : fieldFrobenius P (a.2 j : ExtensionField P) = a.2 j :=
    (a.2 j).property
  fin_cases i <;>
    simp [expand, diagram, -fieldFrobenius_apply, fieldFrobenius_three, hf]

def restrict (P : Parameters) (a : FixedCoordinates P) : OrbitParameters P :=
  (![a.1 0, a.1 4, a.1 7],
    ![⟨a.1 3, ((twist_eq_self_iff P a.1).mp a.2 3).symm⟩,
      ⟨a.1 10, ((twist_eq_self_iff P a.1).mp a.2 10).symm⟩,
      ⟨a.1 11, ((twist_eq_self_iff P a.1).mp a.2 11).symm⟩])

/-- Three extension-field parameters and three fixed-field parameters. -/
def fixedCoordinatesEquiv (P : Parameters) : OrbitParameters P ≃ FixedCoordinates P where
  toFun a := ⟨expand P a, expand_fixed P a⟩
  invFun := restrict P
  left_inv a := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  right_inv a := by
    apply Subtype.ext
    funext i
    have h := (twist_eq_self_iff P a.1).mp a.2
    have h0 := h 0
    have h1 := h 1
    have h4 := h 4
    have h5 := h 5
    have h7 := h 7
    have h8 := h 8
    fin_cases i <;> simp_all [expand, restrict, diagram]

theorem card_coordinates (P : Parameters) : Nat.card (Coordinates P) = P.q ^ 36 := by
  rw [Nat.card_fun, card_extensionField]
  simp [← pow_mul]

theorem card_fixedCoordinates (P : Parameters) : Nat.card (FixedCoordinates P) = P.q ^ 12 := by
  rw [← Nat.card_congr (fixedCoordinatesEquiv P), Nat.card_prod,
    Nat.card_fun, Nat.card_fun, card_extensionField, card_fixedField]
  simp only [Nat.card_fin, ← pow_mul, ← pow_add]

end
end Triality.Standard.PositiveCoordinates
