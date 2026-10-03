module
public import Stellmacher.Recognition.FongWreathedSylowCharacter
public import Stellmacher.Recognition.FongWreathedFusionOrientationDefs
public import Theory.Character.IntegralRestriction
public import Theory.Character.RationalPower

/-!
# Full-Sylow restriction numerators in Fong's order-32 case

For an integer-valued ordinary character of a finite simple group, evaluate
its restriction to an oriented wreathed Sylow subgroup against both the
principal character and the actual degree-one character `w(F) = I`,
`w(E) = -I`. The fourteen internal classes collapse by ambient fusion and
integer-valued power invariance. Their normal-form multiplicities give
`d + 7a + 6c + 10b + 8f` and `d - 5a - 2c + 6b`, respectively.
Ordinary character multiplicity makes both numerators divisible by 32.

The inputs are precisely an actual presentation, its `BaseOrientation`,
and an actual integer-valued character. No exceptional-character existence
or additional character-table data is assumed.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)* (1967), pp. 69–70 and p. 73, congruence (iii). The principal
restriction is the supplementary census in
`refs/original/n-group-global/sylow32-source-audit/fong-degree-calculation-audit.md`.
-/

noncomputable section
open scoped BigOperators
namespace Stellmacher.Recognition.FongWreathedIntrinsic
namespace RestrictionSums
open ABG.Wreathed
attribute [local instance] Fintype.ofFinite
private theorem class_eq {H : Type*} [Group H] {φ : H → ℂ}
    (hφ : IsClassFunction φ) {x y : H} (h : IsConj x y) : φ x = φ y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (hφ x g).symm

private theorem character_class {H : Type*} [Group H] {χ : ClassFunction H}
    (hχ : IsCharacter χ) : IsClassFunction χ := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  exact fun x g => Representation.char_conj ρ x g

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
  (T : Sylow 2 G) (Q : Presentation T 2) (ho : BaseOrientation T Q)
  {χ : ClassFunction G} (hχ : IsCharacter χ)
  (hint : ∀ g, ∃ z : ℤ, χ g = (z : ℂ))
  (d a b c f : ℤ)
  (hd : χ 1 = (d : ℂ)) (ha : χ ((J Q : T) : G) = (a : ℂ))
  (hb : χ (X Q * F Q ^ 2 : T) = (b : ℂ))
  (hc : χ (F Q ^ 2 : T) = (c : ℂ)) (hf : χ ((F Q : T) : G) = (f : ℂ))

include ho hχ hint hd ha hb hc hf

private theorem character_table (i : Fin 14) :
    χ ((sylowRepresentative Q i : T) : G) =
      ![(d : ℂ), a, a, c, c, b, f, f, c, b, c, b, b, a] i := by
  have hconj {x y : G} (h : IsConj x y) := class_eq (character_class hχ) h
  have hci : χ (((F Q ^ 2)⁻¹ : T) : G) = (c : ℂ) := by
    rw [Subgroup.coe_inv, hχ.inv_eq_of_integer_value _ (hint _)]
    exact hc
  have hf3 : χ ((F Q ^ 3 : T) : G) = (f : ℂ) := by
    have hp : ((F Q : T) : G) ^ 8 = 1 := by
      rw [← Subgroup.coe_pow, ← F_orderOf Q, pow_orderOf_eq_one, Subgroup.coe_one]
    rw [Subgroup.coe_pow, hχ.pow_eq_of_integer_value _ (by decide : 8 ≠ 0)
      hp (by decide : Nat.Coprime 3 8) (hint _)]
    exact hf
  fin_cases i
  · exact hd
  · exact ha
  · exact (hconj (isConj_X_J T Q)).trans ha
  · exact hc
  · exact hci
  · exact hb
  · exact hf
  · exact hf3
  · exact (hconj ho.square_inv_E.symm).trans hci
  · exact (hconj ho.X_square_EJ.symm).trans hb
  · exact (hconj ho.square_EX.symm).trans hc
  · exact (hconj ho.X_square_EXJ.symm).trans hb
  · exact (hconj (isConj_XF_sq_EF T Q).symm).trans hb
  · exact (hconj (isConj_EF_inv_J T Q)).trans ha

/-- The principal restriction numerator, counted on all 32 normal forms. -/
public theorem principal_sum :
    ∑ x : T, χ (x : G) = ((d + 7*a + 6*c + 10*b + 8*f : ℤ) : ℂ) := by
  rw [sum_table Q (fun x : T => χ (x : G))
    (isClassFunction_comp_hom (T : Subgroup G).subtype (character_class hχ))]
  simp_rw [character_table T Q ho hχ hint d a b c f hd ha hb hc hf]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  ring

/-- The restriction numerator paired with Fong's actual degree-one character. -/
public theorem linear_sum :
    ∑ x : T, χ (x : G) * star (w Q x) = ((d - 5*a - 2*c + 6*b : ℤ) : ℂ) := by
  have hclass : IsClassFunction (fun x : T => χ (x : G) * star (w Q x)) := by
    intro x g
    change χ ((g * x * g⁻¹ : T) : G) * star (w Q (g * x * g⁻¹)) =
      χ (x : G) * star (w Q x)
    rw [show χ ((g * x * g⁻¹ : T) : G) = χ (x : G) from
      isClassFunction_comp_hom (T : Subgroup G).subtype (character_class hχ) x g]
    have hw : w Q (g * x * g⁻¹) = w Q x := by
      exact character_class (by
        obtain ⟨n, ρ, _, hρ⟩ := w_isLinearCharacter Q |>.1
        exact ⟨n, ρ, hρ⟩) x g
    rw [hw]
  rw [sum_table Q _ hclass]
  simp_rw [character_table T Q ho hχ hint d a b c f hd ha hb hc hf, w_table]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Complex.star_def, map_one,
    map_neg, Complex.conj_I, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  ring

/-- The two full-Sylow restriction congruences under Fong's supplied-input contract. -/
public theorem full_sylow_numerators :
    (32 : ℤ) ∣ d + 7*a + 6*c + 10*b + 8*f ∧
    (32 : ℤ) ∣ d - 5*a - 2*c + 6*b := by
  have hcard : Nat.card T = 32 := Q.card
  constructor
  · simpa only [hcard, Nat.cast_ofNat] using hχ.card_dvd_restriction_sum (T : Subgroup G).subtype _
      (principal_sum T Q ho hχ hint d a b c f hd ha hb hc hf)
  · have hw : IsCharacter (w Q : T → ℂ) := by
      obtain ⟨n, ρ, _, hρ⟩ := w_isLinearCharacter Q |>.1
      exact ⟨n, ρ, hρ⟩
    have hz : IsCharacter (0 : ClassFunction T) := by
      refine ⟨0, Representation.trivial ℂ T (Fin 0 → ℂ), ?_⟩
      funext x
      simp [Representation.character]
    have hgen : IsGeneralizedCharacter (w Q : T → ℂ) :=
      ⟨w Q, 0, hw, hz, by simp⟩
    simpa only [hcard, Nat.cast_ofNat] using hχ.card_dvd_restriction_numerator
      (T : Subgroup G).subtype hgen _
      (linear_sum T Q ho hχ hint d a b c f hd ha hb hc hf)

end RestrictionSums
end Stellmacher.Recognition.FongWreathedIntrinsic
