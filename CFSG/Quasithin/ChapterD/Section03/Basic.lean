module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Rank calculus for §D.3

Aschbacher--Smith, *The Classification of Quasithin Groups* (1 March 2004),
§D.3, uses the cubic parameter
`q̂ = m(V / C_V(A)) / m(A)` throughout the analysis of modules.  The
group-theoretic identification of the possible simple sections is supplied by
§B.4 and §D.2.  This file records the independent arithmetic part of the
argument.  It is deliberately phrased in terms of the two ranks; consequently
it can be reused for chief-factor sums before a particular representation is
chosen.

The inequality is stored as a natural-number cross multiplication.  This
avoids choosing a division convention at zero and makes the direct-sum and
finite-chief-factor arguments completely constructive.
-/

namespace CFSG.Quasithin.ChapterD.Section03

/-- The rank data attached to an offender and a module.

`codim` is `m(V / C_V(A))` and `offenderRank` is `m(A)`.  The positivity
condition is the source condition `A ≠ 1`; `bound` is exactly `q̂ ≤ 2` after
cross multiplication.
-/
public structure QHatProfile where
  offenderRank : ℕ
  codim : ℕ
  offender_pos : 0 < offenderRank
  bound : codim ≤ 2 * offenderRank

namespace QHatProfile

/-- The rational value represented by a profile. -/
public noncomputable def value (p : QHatProfile) : ℚ :=
  (p.codim : ℚ) / p.offenderRank

/-- A profile has nonnegative cubic parameter. -/
public theorem value_nonneg (p : QHatProfile) : 0 ≤ p.value := by
  unfold value
  positivity

/-- The stored cross-multiplied inequality is equivalent to `q̂ ≤ 2`. -/
public theorem value_le_two (p : QHatProfile) : p.value ≤ 2 := by
  unfold value
  apply (div_le_iff₀ (by exact_mod_cast p.offender_pos)).2
  exact_mod_cast p.bound

/-- Strict cross-multiplication gives the strict inequality used in the
contradiction branches of D.3. -/
public theorem value_lt_two_of_bound_lt (p : QHatProfile)
    (h : p.codim < 2 * p.offenderRank) : p.value < 2 := by
  unfold value
  apply (div_lt_iff₀ (by exact_mod_cast p.offender_pos)).2
  exact_mod_cast h

/-- Equality at the endpoint is detected arithmetically. -/
public theorem bound_eq_of_value_eq_two (p : QHatProfile)
    (h : p.value = 2) : p.codim = 2 * p.offenderRank := by
  unfold value at h
  have hp : (p.offenderRank : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt p.offender_pos)
  have hc : (p.codim : ℚ) = 2 * p.offenderRank :=
    (div_eq_iff hp).mp h
  exact_mod_cast hc

/-- Combining two independent chief-factor blocks preserves `q̂ ≤ 2`.

This is the numerical step used whenever D.3 replaces a module by a direct
sum of homogeneous components.
-/
public def directSum (p q : QHatProfile) : QHatProfile where
  offenderRank := p.offenderRank + q.offenderRank
  codim := p.codim + q.codim
  offender_pos := Nat.add_pos_left p.offender_pos _
  bound := by
    calc
      p.codim + q.codim ≤ 2 * p.offenderRank + 2 * q.offenderRank :=
        Nat.add_le_add p.bound q.bound
      _ = 2 * (p.offenderRank + q.offenderRank) := by omega

@[simp] public theorem directSum_offenderRank (p q : QHatProfile) :
    (p.directSum q).offenderRank = p.offenderRank + q.offenderRank := by
  simp [directSum]

@[simp] public theorem directSum_codim (p q : QHatProfile) :
    (p.directSum q).codim = p.codim + q.codim := by
  simp [directSum]

public theorem directSum_value_le_two (p q : QHatProfile) :
    (p.directSum q).value ≤ 2 :=
  (p.directSum q).value_le_two

end QHatProfile

/-- A finite family of profiles still satisfies the same cross-multiplied
bound after summing its chief factors. -/
public theorem sum_codim_le_two_mul_sum_offenderRank
    {ι : Type*} [Fintype ι] (p : ι → QHatProfile) :
    (∑ i, (p i).codim) ≤ 2 * ∑ i, (p i).offenderRank := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i hi => (p i).bound)
  calc
    (∑ i, (p i).codim) ≤ ∑ i, 2 * (p i).offenderRank := h
    _ = 2 * ∑ i, (p i).offenderRank := by
      rw [Finset.mul_sum]

/-- If one chief-factor block is strict, the whole profile obtained by adding a
fixed complementary block remains strict whenever the complementary block has
the same strict margin.  This elementary form is convenient for iterating the
strict branch of D.3. -/
public theorem sum_codim_lt_two_mul_sum_offenderRank
    {ι : Type*} [Fintype ι] (p : ι → QHatProfile)
    (j : ι) (hj : (p j).codim < 2 * (p j).offenderRank)
    (hrest : ∀ i, i ≠ j → (p i).codim ≤ 2 * (p i).offenderRank) :
    (∑ i, (p i).codim) < 2 * ∑ i, (p i).offenderRank := by
  classical
  have hsum : (∑ i, (p i).codim) < ∑ i, 2 * (p i).offenderRank := by
    apply Finset.sum_lt_sum
    · intro i hi
      by_cases hij : i = j
      · simpa [hij] using hj.le
      · exact hrest i hij
    · exact ⟨j, Finset.mem_univ _, hj⟩
  calc
    (∑ i, (p i).codim) < ∑ i, 2 * (p i).offenderRank := hsum
    _ = 2 * ∑ i, (p i).offenderRank := by rw [Finset.mul_sum]

end CFSG.Quasithin.ChapterD.Section03
