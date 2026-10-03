module
public import Theory.Character.CyclicSevenNormalizerPeriods

/-!
# The second moment of the three quadratic periods

Expand the squared orbit sums and reindex one action coordinate. Summing over
the three rows gives the nonprincipal Fourier sum: six when the action fixes
the generator, and minus one for the other action element. Thus the
second moment is five. Freeness follows because a nonidentity element generates
C7 and the supplied action is faithful.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `Theory.Character.CyclicThirteenPeriodNorms`,
whose source is Alperin--Brauer--Gorenstein, III.8, pp.116--117.
-/

public section
open scoped BigOperators IsMulCommutative
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace CyclicSevenNormalizer
variable {G : Type*} [Group G] [Finite G] {P : Subgroup G}
private theorem linear_star (χ : P →* ℂ) (x : P) : star (χ x) = χ x⁻¹ := by
  obtain ⟨n, ρ, _, hρ⟩ := χ.isLinearCharacter.1
  rw [hρ]
  exact (Representation.representation_character_inv_eq_star_character ρ x).symm

/-- The three local quadratic rows have squared column norm five away from one. -/
theorem Rows.sum_normSq_restriction (s : Rows P) (hP : Nat.card P = 7) (u : P) (hu : u ≠ 1) :
    ∑ i : Fin 3, Complex.normSq (s.chi i (ConjClasses.mk (inclusion P u))) = 5 := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hfree (a : Two) : s.action a u = u ↔ a = 1 := by
    constructor
    · intro ha
      apply s.action_injective
      apply MulEquiv.ext
      intro x
      obtain ⟨n, rfl⟩ := mem_powers_of_prime_card hP (g' := x) hu
      simpa using congrArg (fun y => y ^ n) ha
    · rintro rfl
      simp
  have hrow (i : Fin 3) :
      s.chi i (ConjClasses.mk (inclusion P u)) *
        star (s.chi i (ConjClasses.mk (inclusion P u))) =
      ∑ a : Two, s.chi i (ConjClasses.mk (inclusion P (s.action a u * u⁻¹))) := by
    simp only [s.restriction, star_sum, Finset.sum_mul, Finset.mul_sum]
    calc
      _ = ∑ b : Two, ∑ a : Two,
          s.linear i (s.action (b * a) u) * star (s.linear i (s.action b u)) := by
        apply Finset.sum_congr rfl
        intro b _
        exact (Equiv.sum_comp (Equiv.mulLeft b)
          (fun a => s.linear i (s.action a u) * star (s.linear i (s.action b u)))).symm
      _ = ∑ a : Two, ∑ b : Two,
          s.linear i (s.action b (s.action a u * u⁻¹)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        simp only [linear_star, map_mul, map_inv, MulAut.mul_apply]
  have hsum (a : Two) :
      ∑ i : Fin 3, s.chi i (ConjClasses.mk (inclusion P (s.action a u * u⁻¹))) =
        if a = 1 then 6 else -1 := by
    split_ifs with ha
    · subst a
      norm_num [s.degree]
    · exact s.sum_restriction hP _ (by intro he; exact ha ((hfree a).mp (mul_inv_eq_one.mp he)))
  have hc : (∑ i : Fin 3, s.chi i (ConjClasses.mk (inclusion P u)) *
        star (s.chi i (ConjClasses.mk (inclusion P u)))) = (5 : ℂ) := by
    simp_rw [hrow]
    rw [Finset.sum_comm]
    simp_rw [hsum]
    calc
      _ = ∑ a : Two, ((if a = 1 then 7 else 0) - 1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> norm_num
      _ = 5 := by norm_num [Finset.sum_sub_distrib, Two]
  have hr := congrArg Complex.re hc
  simpa [Complex.re_sum, Complex.star_def, Complex.mul_conj] using hr
end CyclicSevenNormalizer
