module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.ModelInputs
public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.SmallDerived

/-!
# All six value implications in the conditional I.1.3 assembly

The completed PSL₂, PSL₄(2), A₆ and A₇ calculations are inserted directly.
The remaining individual model kernels are explicit inputs. In particular,
no cyclic-three result is used outside its degree-three field domain.
The exceptional order-48 kernel rules out an accidental PSL₃(4) alias in
the cyclic-three branch by an isomorphism contradiction on the kernels.

This proves the value half of the source table conditional on the named
remaining calculations; it does not instantiate those calculations.
Source: Aschbacher--Smith I.1.3(1)--(6), printed p.407.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers
open PerfectCentralCovering
universe u
variable {S : Type u} [Group S] [Finite S] [Group.IsPerfect S] [IsSimpleGroup S]

omit [Finite S] [IsSimpleGroup S] in
/-- The literal small G₂ derived endpoint consumes the ordinary PSU₃(3)
kernel, with its field-degree restriction discharged at p = 3, f = 1. -/
theorem multiplier_g2Derived_of_unitary_three (K : KernelInputs S)
    (e : S ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Subsingleton (schurMultiplier S) := by
  have hp : DegreeThreeParameters 3 :=
    Or.inr ⟨3, 1, by decide, by decide, Or.inl rfl, by decide⟩
  simpa using K.unitaryThree 3 hp (by decide) (g2Derived_isPSU_three e)

omit [Finite S] [IsSimpleGroup S] in
/-- C₃ and (C₄ × C₄) × C₃ cannot both be the same canonical multiplier. -/
theorem not_linearThreeFour_of_multiplier_three (K : KernelInputs S)
    (h3 : Nonempty (schurMultiplier S ≃* MultiplierShape.three.Carrier)) :
    ¬ ClassicalGroup.IsPSL S 3 4 := by
  intro h4
  obtain ⟨e3⟩ := h3
  obtain ⟨e48⟩ := K.linearThreeFour h4
  have hc := Nat.card_congr (e3.symm.trans e48).toEquiv
  norm_num [MultiplierShape.Carrier, Nat.card_prod] at hc

/-- Assemble the seven alternatives of the cyclic-two source row. -/
theorem multiplier_two_of_inputs (K : KernelInputs S) (h : MultiplierRow S .two) :
    Nonempty (schurMultiplier S ≃* MultiplierShape.two.Carrier) := by
  change ClassicalGroup.IsPSL S 4 2 ∨ ClassificationModels.IsG2At S 4 ∨
    Nonempty (S ≃* Sporadic.Mathieu.M12) ∨
    Nonempty (S ≃* Sporadic.LeechRelated.J2.Carrier) ∨
    Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) ∨
    Nonempty (S ≃* Rudvalis.Model) ∨
    (∃ q, Odd q ∧ q ≠ 9 ∧ ClassicalGroup.IsPSL S 2 q) at h
  rcases h with h | h | h | h | h | h | ⟨q, ho, h9, h⟩
  · exact LieMultipliers.PSL4Two.schurMultiplier_equiv_two h
  · exact K.g2Four h
  · exact K.m12 h
  · exact K.j2 h
  · exact K.hs h
  · exact K.ru h
  · exact multiplier_odd_psl2 ho h9 h

omit [Finite S] in
/-- Both degree-three clauses use the field bounds supplied by the actual
rank producer, including the unitary fixed-field order. -/
theorem multiplier_three_of_inputs (K : KernelInputs S) (R : RankInputs S)
    (h : MultiplierRow S .three) :
    Nonempty (schurMultiplier S ≃* MultiplierShape.three.Carrier) := by
  change (¬ ClassicalGroup.IsPSL S 3 4) ∧
    ((∃ q, q % 3 = 1 ∧ ClassicalGroup.IsPSL S 3 q) ∨
      ∃ p f, p.Prime ∧ 0 < f ∧ (p ^ f) % 3 = 2 ∧ ClassicalGroup.IsPSU S 3 (p ^ f)) at h
  rcases h with ⟨h4, h | h⟩
  · obtain ⟨q, hq, he⟩ := h
    have hn2 : q ≠ 2 := by omega
    have hn4 : q ≠ 4 := fun heq => h4 (heq ▸ he)
    simpa only [hq, ↓reduceIte] using K.linearThree q (R.linearThree q he) hn2 hn4 he
  · obtain ⟨p, f, _, _, hq, he⟩ := h
    have hne : p ^ f ≠ 2 := fun hq2 => not_psu3_two (hq2 ▸ he)
    have hp := R.unitaryThree (p ^ f) he
    simpa only [hq, ↓reduceIte] using K.unitaryThree (p ^ f) hp hne he

/-- All six actual kernel identifications, conditional only on the unresolved
individual model kernels and the degree-three parameter deductions. -/
theorem values_of_model_inputs (K : KernelInputs S) (R : RankInputs S) :
    ∀ r, MultiplierRow S r → Nonempty (schurMultiplier S ≃* r.Carrier) := by
  intro r h
  cases r with
  | two => exact multiplier_two_of_inputs K h
  | three => exact multiplier_three_of_inputs K R h
  | six => exact multiplier_six h
  | twelve => exact K.m22 h
  | elementaryFour => exact K.suzukiEight h
  | exceptionalFortyEight => exact K.linearThreeFour h

end CFSG.Quasithin.ChapterI.SQTKMultipliers
