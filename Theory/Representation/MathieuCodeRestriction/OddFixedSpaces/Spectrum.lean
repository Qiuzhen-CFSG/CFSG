module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.Attainment
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.Reduction
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.OrbitCounting
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.PointRestrictions

/-!
# The numerical reduction for the native Mathieu odd-prime spectrum

The actual cocode fixed dimension n satisfies
`2 * (n + 1) * p = 24 + (p - 1) * fixedPoints`.
Concrete order-three subgroups attain displacement six for both M₂₄ and M₂₃.
For the uniform bound and equality criterion, this module gives the final
arithmetic deduction from explicit native point-count restrictions. Those
restrictions remain hypotheses of the theorems named `of_point_counts`;
these conditional theorems do not assert completion of the source spectrum.
The unconditional wrappers below discharge them using the native
permutation-group restriction from `PointRestrictions`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the beta tables
on printed p.396 and H.15.7(1) on printed pp.401–402. The conjugacy and
normalizer conclusions are independent of the structural numerical criterion.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Representation.BinaryOffender
namespace MathieuCode

theorem prime_cocode_fixed_point_equation (D : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    2 * (Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) + 1) * p =
      24 + (p - 1) * Nat.card (MulAction.fixedPoints D (Fin 24)) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  rw [twice_cocode_fixed_add_two_eq_orbits D (hD.symm ▸ ho)]
  exact prime_point_orbit_count D hp hD

theorem cubic_six_fixed_cocode_dimension (D : Subgroup M24) (hD : Nat.card D = 3)
    (hf : Nat.card (MulAction.fixedPoints D (Fin 24)) = 6) :
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) = 5 := by
  have h := prime_cocode_fixed_point_equation D (by decide) (by decide) hD
  rw [hf] at h
  omega

theorem cubic_six_fixed_cocode_displacement (D : Subgroup M24) (hD : Nat.card D = 3)
    (hf : Nat.card (MulAction.fixedPoints D (Fin 24)) = 6) :
    fixedCodim cocodeRepresentation D = 6 := by
  have h := fixedCodim_add_finrank cocodeRepresentation D
  rw [finrank_cocode, cubic_six_fixed_cocode_dimension D hD hf] at h
  omega

/-- The numerical conclusion conditional on the independent native point restrictions. -/
theorem cocode_fixed_alternative_of_point_counts (D : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hpoints : (p = 3 ∧ (Nat.card (MulAction.fixedPoints D (Fin 24)) = 0 ∨
        Nat.card (MulAction.fixedPoints D (Fin 24)) = 6)) ∨
      (5 ≤ p ∧ Nat.card (MulAction.fixedPoints D (Fin 24)) ≤ 4)) :
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) ≤ 3 ∨
      (Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) = 5 ∧
        p = 3 ∧ Nat.card (MulAction.fixedPoints D (Fin 24)) = 6) := by
  have h := prime_cocode_fixed_point_equation D hp ho hD
  rcases hpoints with ⟨rfl, hf | hf⟩ | ⟨hp5, hf⟩
  · rw [hf] at h
    exact Or.inl (by omega)
  · exact Or.inr ⟨cubic_six_fixed_cocode_dimension D hD hf, rfl, hf⟩
  · left
    have hmul := Nat.mul_le_mul_left (p - 1) hf
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    by_contra hn
    have hn4 : 4 ≤ Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) := by omega
    nlinarith

/-- The beta lower bound after supplying the permutation-group restriction. -/
theorem cocode_fixedCodim_ge_six_of_point_counts (D : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hpoints : (p = 3 ∧ (Nat.card (MulAction.fixedPoints D (Fin 24)) = 0 ∨
        Nat.card (MulAction.fixedPoints D (Fin 24)) = 6)) ∨
      (5 ≤ p ∧ Nat.card (MulAction.fixedPoints D (Fin 24)) ≤ 4)) :
    6 ≤ fixedCodim cocodeRepresentation D := by
  have h := cocode_fixed_alternative_of_point_counts D hp ho hD hpoints
  have he := fixedCodim_add_finrank cocodeRepresentation D
  rw [finrank_cocode] at he
  rcases h with h | ⟨h, _⟩ <;> omega

/-- The equality criterion keeps the literal fixed-point action explicit. -/
theorem cocode_fixedCodim_eq_six_iff_of_point_counts (D : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hpoints : (p = 3 ∧ (Nat.card (MulAction.fixedPoints D (Fin 24)) = 0 ∨
        Nat.card (MulAction.fixedPoints D (Fin 24)) = 6)) ∨
      (5 ≤ p ∧ Nat.card (MulAction.fixedPoints D (Fin 24)) ≤ 4)) :
    fixedCodim cocodeRepresentation D = 6 ↔
      p = 3 ∧ Nat.card (MulAction.fixedPoints D (Fin 24)) = 6 := by
  constructor
  · intro hc
    have he := fixedCodim_add_finrank cocodeRepresentation D
    rw [finrank_cocode, hc] at he
    rcases cocode_fixed_alternative_of_point_counts D hp ho hD hpoints with h | ⟨_, h⟩
    · omega
    · exact h
  · rintro ⟨rfl, hf⟩
    exact cubic_six_fixed_cocode_displacement D hD hf

/-- The numerical part of H.15.7, still conditional on the native point restriction. -/
theorem large_cocode_fixed_of_point_counts (D : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hpoints : (p = 3 ∧ (Nat.card (MulAction.fixedPoints D (Fin 24)) = 0 ∨
        Nat.card (MulAction.fixedPoints D (Fin 24)) = 6)) ∨
      (5 ≤ p ∧ Nat.card (MulAction.fixedPoints D (Fin 24)) ≤ 4))
    (hlarge : 4 ≤ Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D)) :
    p = 3 ∧ Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) = 5 ∧
      Nat.card (MulAction.fixedPoints D (Fin 24)) = 6 := by
  rcases cocode_fixed_alternative_of_point_counts D hp ho hD hpoints with h | ⟨h5, h3, hf⟩
  · omega
  · exact ⟨h3, h5, hf⟩

/- The permutation restriction is now available for the native M₂₄ action,
and the point-stabilizer embedding makes the same restriction literal for
M₂₃.  Keep this small transport theorem separate so every later numerical
statement uses the actual twenty-four-point image. -/
theorem m23_odd_prime_point_restriction (D : Subgroup M23) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    (p = 3 ∧ (Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 0 ∨
        Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6)) ∨
      (5 ≤ p ∧ Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) ≤ 4) := by
  exact m24_odd_prime_point_restriction (D.map pointEmbedding) hp ho
    ((Subgroup.card_map_of_injective pointEmbedding_injective).trans hD)

/- The unconditional M₂₄ spectrum. -/
theorem cocode_fixedCodim_ge_six (D : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    6 ≤ fixedCodim cocodeRepresentation D := by
  exact cocode_fixedCodim_ge_six_of_point_counts D hp ho hD
    (m24_odd_prime_point_restriction D hp ho hD)

theorem cocode_fixedCodim_eq_six_iff (D : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    fixedCodim cocodeRepresentation D = 6 ↔
      p = 3 ∧ Nat.card (MulAction.fixedPoints D (Fin 24)) = 6 := by
  exact cocode_fixedCodim_eq_six_iff_of_point_counts D hp ho hD
    (m24_odd_prime_point_restriction D hp ho hD)

theorem large_cocode_fixed (D : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hlarge : 4 ≤ Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D)) :
    p = 3 ∧ Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) = 5 ∧
      Nat.card (MulAction.fixedPoints D (Fin 24)) = 6 := by
  exact large_cocode_fixed_of_point_counts D hp ho hD
    (m24_odd_prime_point_restriction D hp ho hD) hlarge
theorem m23_cubic_six_fixed_cocode_dimension (D : Subgroup M23) (hD : Nat.card D = 3)
    (hf : Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6) :
    Module.finrank (ZMod 2) (fixedSpace m23CocodeRepresentation D) = 5 := by
  rw [m23_cocode_fixedSpace_eq_map]
  exact cubic_six_fixed_cocode_dimension _
    ((Subgroup.card_map_of_injective pointEmbedding_injective).trans hD) hf

theorem m23_cubic_six_fixed_cocode_displacement (D : Subgroup M23) (hD : Nat.card D = 3)
    (hf : Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6) :
    fixedCodim m23CocodeRepresentation D = 6 := by
  rw [m23_cocode_fixedCodim_eq_map]
  exact cubic_six_fixed_cocode_displacement _
    ((Subgroup.card_map_of_injective pointEmbedding_injective).trans hD) hf

/-- Displacement six is attained by a native order-three subgroup of M₂₄. -/
theorem exists_m24_cocode_displacement_six : ∃ D : Subgroup M24,
    Nat.card D = 3 ∧ fixedCodim cocodeRepresentation D = 6 := by
  obtain ⟨D, hD, hf⟩ := exists_m24_cubic_six_fixed
  exact ⟨D, hD, cubic_six_fixed_cocode_displacement D hD hf⟩

/-- Displacement six is attained by a native order-three subgroup of M₂₃. -/
theorem exists_m23_cocode_displacement_six : ∃ D : Subgroup M23,
    Nat.card D = 3 ∧ fixedCodim m23CocodeRepresentation D = 6 := by
  obtain ⟨D, hD, hf⟩ := exists_m23_cubic_six_fixed
  exact ⟨D, hD, m23_cubic_six_fixed_cocode_displacement D hD hf⟩

/-- The lower bound transfers along the actual M₂₃ embedding. -/
theorem m23_cocode_fixedCodim_ge_six_of_point_counts (D : Subgroup M23) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hpoints : (p = 3 ∧ (Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 0 ∨
        Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6)) ∨
      (5 ≤ p ∧ Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) ≤ 4)) :
    6 ≤ fixedCodim m23CocodeRepresentation D := by
  rw [m23_cocode_fixedCodim_eq_map]
  exact cocode_fixedCodim_ge_six_of_point_counts _ hp ho
    ((Subgroup.card_map_of_injective pointEmbedding_injective).trans hD) hpoints

/-- Equality is tested on the native twenty-four-point image of M₂₃. -/
theorem m23_cocode_fixedCodim_eq_six_iff_of_point_counts (D : Subgroup M23) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hpoints : (p = 3 ∧ (Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 0 ∨
        Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6)) ∨
      (5 ≤ p ∧ Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) ≤ 4)) :
    fixedCodim m23CocodeRepresentation D = 6 ↔
      p = 3 ∧ Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6 := by
  rw [m23_cocode_fixedCodim_eq_map]
  exact cocode_fixedCodim_eq_six_iff_of_point_counts _ hp ho
    ((Subgroup.card_map_of_injective pointEmbedding_injective).trans hD) hpoints

/-- The conditional large-fixed-space conclusion uses the native M₂₃ image. -/
theorem m23_large_cocode_fixed_of_point_counts (D : Subgroup M23) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hpoints : (p = 3 ∧ (Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 0 ∨
        Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6)) ∨
      (5 ≤ p ∧ Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) ≤ 4))
    (hlarge : 4 ≤ Module.finrank (ZMod 2) (fixedSpace m23CocodeRepresentation D)) :
    p = 3 ∧ Module.finrank (ZMod 2) (fixedSpace m23CocodeRepresentation D) = 5 ∧
      Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6 := by
  rw [m23_cocode_fixedSpace_eq_map] at hlarge ⊢
  exact large_cocode_fixed_of_point_counts _ hp ho
    ((Subgroup.card_map_of_injective pointEmbedding_injective).trans hD) hpoints hlarge

/- The unconditional M₂₃ spectrum, with fixed points measured in the native
twenty-four-point image of M₂₃. -/
theorem m23_cocode_fixedCodim_ge_six (D : Subgroup M23) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    6 ≤ fixedCodim m23CocodeRepresentation D := by
  exact m23_cocode_fixedCodim_ge_six_of_point_counts D hp ho hD
    (m23_odd_prime_point_restriction D hp ho hD)

theorem m23_cocode_fixedCodim_eq_six_iff (D : Subgroup M23) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    fixedCodim m23CocodeRepresentation D = 6 ↔
      p = 3 ∧ Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6 := by
  exact m23_cocode_fixedCodim_eq_six_iff_of_point_counts D hp ho hD
    (m23_odd_prime_point_restriction D hp ho hD)

theorem m23_large_cocode_fixed (D : Subgroup M23) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p)
    (hlarge : 4 ≤ Module.finrank (ZMod 2) (fixedSpace m23CocodeRepresentation D)) :
    p = 3 ∧ Module.finrank (ZMod 2) (fixedSpace m23CocodeRepresentation D) = 5 ∧
      Nat.card (MulAction.fixedPoints (D.map pointEmbedding) (Fin 24)) = 6 := by
  exact m23_large_cocode_fixed_of_point_counts D hp ho hD
    (m23_odd_prime_point_restriction D hp ho hD) hlarge

end MathieuCode
