module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondefiningRank
public import Theory.GroupTheory.PerfectCentralCoverOddPart
public import Theory.GroupTheory.PerfectCentralCoverOddSupport

/-!
# A support reduction for perfect central covers of PSU₄(3)

The actual projective unitary image has order dividing GL₄(9), whose only
repeated odd prime factors are three and five. Cyclic-Sylow transfer therefore
leaves only two, three and five in a perfect central kernel. Oddness and a
trivial three-core reduce that kernel to a five-group.

This is a partial source reduction for Aschbacher–Smith A.2.17, printed p.39.
The five-primary exclusion is still required to conclude that the kernel is
trivial. This module does not assert the full multiplier calculation I.1.4(5).
-/

public section

open BenderSuzuki.MatrixGroups PerfectCentralCovering

namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.OddCentralKernels

variable {F : Type*} [Field F] [Finite F]

private theorem square_not_dvd_generalLinear_order {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hr5 : r ≠ 5) :
    ¬ r ^ 2 ∣ 2 ^ 15 * 3 ^ 12 * 5 ^ 2 * 7 * 13 * 41 := by
  intro hd
  have hrd := (dvd_pow_self r (by decide : 2 ≠ 0)).trans hd
  have he : r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 13 ∨ r = 41 := by
    rcases hr.dvd_mul.mp hrd with h | h
    · rcases hr.dvd_mul.mp h with h | h
      · rcases hr.dvd_mul.mp h with h | h
        · rcases hr.dvd_mul.mp h with h | h
          · rcases hr.dvd_mul.mp h with h | h
            · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
                (hr.dvd_of_dvd_pow h))
            · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
                (hr.dvd_of_dvd_pow h)))
          · exact Or.inr (Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hr (by decide)).mp (hr.dvd_of_dvd_pow h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hr (by decide)).mp h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hr (by decide)).mp h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hr (by decide)).mp h)))))
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hr2 rfl
  · exact hr3 rfl
  · exact hr5 rfl
  all_goals norm_num at hd

/-- The GL order leaves only two, three and five as possible kernel primes. -/
theorem prime_dvd_kernel_eq_two_or_three_or_five
    (J : HermitianForm 4 F) (hF : Nat.card F = 9)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card f.toMonoidHom.ker) :
    r = 2 ∨ r = 3 ∨ r = 5 := by
  by_cases hr2 : r = 2
  · exact Or.inl hr2
  by_cases hr3 : r = 3
  · exact Or.inr (Or.inl hr3)
  by_cases hr5 : r = 5
  · exact Or.inr (Or.inr hr5)
  let : Fact r.Prime := ⟨hr⟩
  exact (f.not_dvd_card_kernel_of_square_not_dvd
    (fun h => square_not_dvd_generalLinear_order hr hr2 hr3 hr5
      (h.trans (projective_card_dvd_generalLinear_order J hF))) hd).elim

/-- The remaining odd kernel is five-primary; exclusion of five is separate. -/
theorem kernel_isFiveGroup_of_odd_of_threeCore_eq_bot
    (J : HermitianForm 4 F) (hF : Nat.card F = 9)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J))
    (hodd : Odd (Nat.card f.toMonoidHom.ker)) (hcore : pCore 3 E = ⊥) :
    IsPGroup 5 f.toMonoidHom.ker :=
  f.kernel_isPGroup_of_odd_of_pCore_eq_bot (by decide) hodd hcore
    (fun _ hr hd => prime_dvd_kernel_eq_two_or_three_or_five J hF f hr hd)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.OddCentralKernels
