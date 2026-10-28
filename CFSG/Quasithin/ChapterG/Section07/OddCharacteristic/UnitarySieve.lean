module

public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.OrderSieve
public import Theory.SpecificGroups.SU3.PrimeOrderDivisibility

/-!
# The unitary parameter reduction in G.7.2(3)

The defining-prime cube divides the order of both special and projective
unitary groups. In binary degree at most eight this forces prime three.
The special group then maps isomorphically to its projective image.
Together with the linear exclusions this leaves an actual PSU₃(3) model.

This proves the group identification in Aschbacher--Smith G.7.2(3), printed
pp.347--348. The further assertion that a faithful irreducible module has
degree six is a separate representation-theoretic obligation.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section07.OddCharacteristic

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Only fixed-field prime three survives for projective unitary groups. -/
theorem psu3_parameter_eq_three (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU G 3 p)
    (hd : Module.finrank (ZMod 2) V ≤ 8) : p = 3 := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  have hdiv : p ^ 3 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv]
    exact J.prime_cube_dvd_card_projective hp hcard hconj
  exact prime_eq_three_of_cube_dvd_GL8 hp ho
    (hdiv.trans ((Representation.card_dvd_card_GL_of_injective ρ hρ).trans
      (Representation.BinaryEight.card_binary_GL_dvd_eight hd)))

/-- The same defining-prime reduction before quotienting the scalar center. -/
theorem su3_parameter_eq_three (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : IsSUThree G p)
    (hd : Module.finrank (ZMod 2) V ≤ 8) : p = 3 := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  have hdiv : p ^ 3 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv]
    exact J.prime_cube_dvd_card_special hp hcard hconj
  exact prime_eq_three_of_cube_dvd_GL8 hp ho
    (hdiv.trans ((Representation.card_dvd_card_GL_of_injective ρ hρ).trans
      (Representation.BinaryEight.card_binary_GL_dvd_eight hd)))

omit [Finite G] in
/-- The special unitary model at three is an actual projective unitary model. -/
theorem IsSUThree.isPSU_three (hmodel : IsSUThree G 3) :
    ClassicalGroup.IsPSU G 3 3 := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  exact ⟨F, hF, hfin, J, hcard, hconj,
    ⟨e.trans (J.specialProjectiveEquivOfCardNine (by simpa using hcard))⟩⟩

/-- The group-identification part of G.7.2(3), with no module classification
assumed: all four alternatives reduce to an actual PSU₃(3) isomorphism. -/
theorem linear_unitary_three_identification (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : IsLinearUnitaryThree G p)
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    p = 3 ∧ ClassicalGroup.IsPSU G 3 3 := by
  rcases hmodel with h | h | h | h
  · exact (Nat.not_lt_of_ge hd (psl3_degree_gt_eight ρ hρ hp ho h)).elim
  · exact (Nat.not_lt_of_ge hd (sl3_degree_gt_eight ρ hρ hp ho h)).elim
  · have hp3 := psu3_parameter_eq_three ρ hρ hp ho h hd
    exact ⟨hp3, hp3 ▸ h⟩
  · have hp3 := su3_parameter_eq_three ρ hρ hp ho h hd
    exact ⟨hp3, IsSUThree.isPSU_three (hp3 ▸ h)⟩

end CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
