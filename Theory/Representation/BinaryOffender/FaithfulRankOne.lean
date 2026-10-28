module

public import Theory.Representation.BinaryOffender.Replacement

/-!
# Faithful modules whose minimal best offenders have rank one

Strict Thompson replacement preserves a strict offender inequality while
passing to a minimal best offender. A rank-one subgroup could satisfy that
inequality only by fixing the entire module, contrary to faithfulness.
Consequently a faithful FF-module with this rank-one property has quadratic
ratio exactly one, and all its best offenders have weight equal to the
ambient dimension.

These are conditional reductions. They do not assert that minimal best
offenders in a solvable group have rank one; that is a structural input to
Aschbacher–Smith, B.1.8(1)–(3), printed p. 70, citing Glauberman (1973) and
Aschbacher, *Finite Group Theory*, 32.3. Replacement is B.1.4(3)–(5).
-/

public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
/-- A hyperplane with a strictly larger fixed space has the same weight as
the best offender containing it. The hyperplane may be trivial. -/
theorem IsBestOffender.equalWeightLE_of_hyperplane
    {A B : Subgroup G} (hA : IsBestOffender ρ A) (hBA : B ≤ A)
    (hrank : rank A = rank B + 1)
    (hfixed : fixedSpace ρ A < fixedSpace ρ B) : EqualWeightLE ρ B A := by
  refine ⟨hBA, le_antisymm (hA.2 B hBA) ?_⟩
  have hdim := Submodule.finrank_lt_finrank_of_lt hfixed
  unfold weight
  omega

omit [Finite G] in
/-- The hyperplane supplied by the coprime-action argument must be trivial
for a minimal best offender. This isolates the numerical step of
Kurzweil–Stellmacher 9.3.2 from the construction of that hyperplane. -/
theorem IsMinimalBestOffender.rank_one_of_hyperplane
    {A B : Subgroup G} (hA : IsMinimalBestOffender ρ A) (hBA : B ≤ A)
    (hrank : rank A = rank B + 1)
    (hfixed : fixedSpace ρ A < fixedSpace ρ B) : rank A = 1 := by
  have hBbot : B = ⊥ := by
    by_contra hne
    have he := hA.1.equalWeightLE_of_hyperplane ρ hBA hrank hfixed
    have hB := hA.1.of_equalWeightLE ρ (hA.1.1.of_le hBA hne) he
    have hEq := hA.2 B hB he
    rw [hEq] at hrank
    omega
  simpa only [hBbot, rank_bot, zero_add] using hrank

omit [Finite G] in
/-- Every nontrivial subgroup has positive fixed-space codimension in a faithful action. -/
theorem fixedCodim_pos_of_faithful (hρ : Function.Injective ρ)
    {A : Subgroup G} (hA : A ≠ ⊥) : 0 < fixedCodim ρ A := by
  have hproper : fixedSpace ρ A ≠ ⊤ := by
    intro htop
    apply hA
    apply le_bot_iff.mp
    intro g hg
    apply hρ
    apply LinearMap.ext
    intro v
    have hv : v ∈ fixedSpace ρ A := by rw [htop]; trivial
    exact (hv ⟨g, hg⟩).trans (by simp)
  have := Submodule.finrank_lt hproper
  have := fixedCodim_add_finrank ρ A
  omega

/-- Strict replacement reduces exclusion of all strong offenders to rank one
for minimal best offenders. Faithfulness excludes codimension zero. -/
theorem not_isStrongFFModule_of_minimalBestOffender_rank_one
    (hρ : Function.Injective ρ)
    (hrank : ∀ A, IsMinimalBestOffender ρ A → rank A = 1) :
    ¬ IsStrongFFModule ρ := by
  rintro ⟨A, hA⟩
  obtain ⟨B, _, hB, _, hstrong⟩ := hA.exists_quadratic_minimalBestOffender ρ
  have hpos := fixedCodim_pos_of_faithful ρ hρ hB.1.1.1
  have hlt := hstrong.2
  rw [hrank B hB] at hlt
  omega

/-- For an FF-module, the rank-one condition on minimal best offenders forces
the quadratic ratio to be exactly one. -/
theorem quadraticRatio_eq_one_of_minimalBestOffender_rank_one
    (hρ : Function.Injective ρ) (hff : IsFFModule ρ)
    (hrank : ∀ A, IsMinimalBestOffender ρ A → rank A = 1) :
    quadraticRatio ρ = 1 := by
  apply le_antisymm ((isFFModule_iff_quadraticRatio_le_one ρ).mp hff)
  apply le_of_not_gt
  intro hlt
  exact not_isStrongFFModule_of_minimalBestOffender_rank_one ρ hρ hrank
    ((isStrongFFModule_iff_quadraticRatio_lt_one ρ).mpr hlt)

/-- Under the rank-one condition, every best offender has equality in the
offender dimension inequality. -/
theorem IsBestOffender.fixedCodim_eq_rank_of_minimal_rank_one
    (hρ : Function.Injective ρ)
    (hrank : ∀ A, IsMinimalBestOffender ρ A → rank A = 1)
    {A : Subgroup G} (hA : IsBestOffender ρ A) : fixedCodim ρ A = rank A := by
  apply le_antisymm (hA.isOffender ρ).2
  apply le_of_not_gt
  intro hlt
  exact not_isStrongFFModule_of_minimalBestOffender_rank_one ρ hρ hrank ⟨A, hA.1, hlt⟩

end Representation.BinaryOffender
