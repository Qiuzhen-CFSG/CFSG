module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.Coordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.Transport

/-!
# Orders of the concrete Ree radicals

Unique split root coordinates and the solved Ree fixed equations give order
`q^10` for the Suzuki radical, `q^11` for the linear radical and `q^12` for the
positive fixed subgroup. The Suzuki support has four commuting pairs and three
B₂ quartets; the linear support has three pairs and four quartets; the positive
support has four of each. Each pair contributes one free field scalar and each
quartet contributes two, including the noncommutative correction terms.

The unconditional order theorems discharge both coordinate hypotheses of the
retained assembly lemmas. Matrix-preserving subgroup equivalences transport
the radical orders to the local residuals and the existing local seeds.
Identifying these root-defined radicals with the intrinsic two-cores belongs
to the separate local quotient calculation.

Source: Aschbacher–Smith F.1.12(I)(5), printed p.263 (PDF p.274),
`refs/quasithin.pdf`. The parameter is `q = 2^(2*m+1)` with `m ≥ 0`;
the binary endpoint is the full Ree group, not its Tits derived subgroup.
-/

public section
noncomputable section

namespace ReeF4.Parabolics

open LargeLocalSeeds RadicalCoordinates

/-- Count the fixed subgroup after both coordinate obligations have been proved. -/
theorem card_fixedSubgroup_of_coordinates (m : ℕ) {k : Support} (e : RootOrder k)
    (hword : Function.Bijective (wordInSubgroup m e))
    (c : FixedParameters m e ≃ (Fin (fixedDimension k) → CoefficientField m)) :
    Nat.card (RadicalCoordinates.fixedSubgroup m k) =
      (2 ^ (2 * m + 1)) ^ fixedDimension k := by
  rw [card_fixedSubgroup m e hword, Nat.card_congr c, Nat.card_fun, Nat.card_fin, field_card]

/-- Conditional assembly for either root-defined radical. -/
theorem card_radical_of_coordinates (m : ℕ) (s : Side) (e : RootOrder (.radical s))
    (hword : Function.Bijective (wordInSubgroup m e))
    (c : FixedParameters m e ≃ (Fin (fixedDimension (.radical s)) → CoefficientField m)) :
    Nat.card (radical m s) = (2 ^ (2 * m + 1)) ^ fixedDimension (.radical s) := by
  simpa only [fixedSubgroup_radical] using card_fixedSubgroup_of_coordinates m e hword c

/-- Conditional assembly inside the actual local residual. -/
theorem card_localRadical_of_coordinates (m : ℕ) (s : Side) (e : RootOrder (.radical s))
    (hword : Function.Bijective (wordInSubgroup m e))
    (c : FixedParameters m e ≃ (Fin (fixedDimension (.radical s)) → CoefficientField m)) :
    Nat.card (localRadical m s) = (2 ^ (2 * m + 1)) ^ fixedDimension (.radical s) := by
  rw [card_localRadical]
  exact card_radical_of_coordinates m s e hword c

/-- Conditional assembly for the existing local-seed interface, preserving matrices. -/
theorem card_seedRadical_of_coordinates {m : ℕ} (d : LocalBlockInput m) (s : Side)
    (e : RootOrder (.radical s))
    (hword : Function.Bijective (wordInSubgroup m e))
    (c : FixedParameters m e ≃ (Fin (fixedDimension (.radical s)) → CoefficientField m)) :
    Nat.card (seedRadical d s) = (2 ^ (2 * m + 1)) ^ fixedDimension (.radical s) := by
  rw [card_seedRadical]
  exact card_radical_of_coordinates m s e hword c

/-- The identical coordinate argument also supplies the positive fixed subgroup order. -/
theorem card_unipotent_of_coordinates (m : ℕ) (e : RootOrder .positive)
    (hword : Function.Bijective (wordInSubgroup m e))
    (c : FixedParameters m e ≃ (Fin 12 → CoefficientField m)) :
    Nat.card (unipotent m) = (2 ^ (2 * m + 1)) ^ 12 := by
  simpa only [fixedSubgroup_positive, fixedDimension] using
    card_fixedSubgroup_of_coordinates m e hword c

/-- The actual fixed subgroup has the predicted order, with both coordinate
calculations discharged for every support and every `m : ℕ`. -/
theorem card_fixedSubgroup_eq_pow (m : ℕ) (k : Support) :
    Nat.card (RadicalCoordinates.fixedSubgroup m k) =
      (2 ^ (2 * m + 1)) ^ fixedDimension k := by
  obtain ⟨e⟩ := rootOrder_nonempty k
  obtain ⟨c⟩ := FixedCoordinates.fixedParametersEquiv m
    (fun f => wordInSubgroup_bijective m f) e
  exact card_fixedSubgroup_of_coordinates m e (wordInSubgroup_bijective m e) c

/-- The order of either root-defined radical in the full Ree group. -/
theorem card_radical (m : ℕ) (s : Side) :
    Nat.card (radical m s) = (2 ^ (2 * m + 1)) ^ fixedDimension (.radical s) := by
  simpa only [fixedSubgroup_radical] using card_fixedSubgroup_eq_pow m (.radical s)

/-- The Suzuki-side root radical has order `q^10`, including `q = 2`. -/
theorem card_radical_suzuki (m : ℕ) :
    Nat.card (radical m .suzuki) = (2 ^ (2 * m + 1)) ^ 10 :=
  card_radical m .suzuki

/-- The linear-side root radical has order `q^11`, including `q = 2`. -/
theorem card_radical_linear (m : ℕ) :
    Nat.card (radical m .linear) = (2 ^ (2 * m + 1)) ^ 11 :=
  card_radical m .linear

/-- The positive fixed subgroup has order `q^12`, including `q = 2`. -/
theorem card_unipotent (m : ℕ) :
    Nat.card (unipotent m) = (2 ^ (2 * m + 1)) ^ 12 := by
  simpa only [fixedSubgroup_positive, fixedDimension] using
    card_fixedSubgroup_eq_pow m .positive

/-- Restriction to the local residual preserves the radical's order. -/
theorem card_localRadical_eq_pow (m : ℕ) (s : Side) :
    Nat.card (localRadical m s) = (2 ^ (2 * m + 1)) ^ fixedDimension (.radical s) := by
  rw [card_localRadical, card_radical]

theorem card_localRadical_suzuki (m : ℕ) :
    Nat.card (localRadical m .suzuki) = (2 ^ (2 * m + 1)) ^ 10 :=
  card_localRadical_eq_pow m .suzuki

theorem card_localRadical_linear (m : ℕ) :
    Nat.card (localRadical m .linear) = (2 ^ (2 * m + 1)) ^ 11 :=
  card_localRadical_eq_pow m .linear

/-- Any specified fixed carrier has the same radical matrices and order. -/
theorem card_standardRadical_eq_pow {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    Nat.card (standardRadical d s) =
      (2 ^ (2 * m + 1)) ^ fixedDimension (.radical s) := by
  rw [card_standardRadical, card_radical]

/-- Transport to the existing local-seed radical through its actual equivalence. -/
theorem card_seedRadical_eq_pow {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    Nat.card (seedRadical d s) = (2 ^ (2 * m + 1)) ^ fixedDimension (.radical s) := by
  rw [card_seedRadical, card_radical]

theorem card_seedRadical_suzuki {m : ℕ} (d : LocalBlockInput m) :
    Nat.card (seedRadical d .suzuki) = (2 ^ (2 * m + 1)) ^ 10 :=
  card_seedRadical_eq_pow d .suzuki

theorem card_seedRadical_linear {m : ℕ} (d : LocalBlockInput m) :
    Nat.card (seedRadical d .linear) = (2 ^ (2 * m + 1)) ^ 11 :=
  card_seedRadical_eq_pow d .linear

end ReeF4.Parabolics
