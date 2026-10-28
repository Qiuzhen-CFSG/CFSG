module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Levi

/-!
# Generators of the linear Ree seed

In the explicit F₄ root system, a root with zero middle simple coefficients
is one of the four signed end simple roots. Checking the pair, unit and
half-sign roots proves this directly. It partitions the seed generators
between the specified radical and the actual end-node Levi, giving their
subgroup join. This is generation, not yet a Levi decomposition.

Source: the root Levi construction underlying Aschbacher–Smith F.1.12(I)(5),
printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.BinaryLinear
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds Subgroup
noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The only roots supported on the end nodes are the four signed simple roots. -/
theorem isLeviRoot_of_middle_coefficients_zero (r : F4Chevalley.Root)
    (h1 : typeF4SimpleCoefficient r.val 1 = 0)
    (h2 : typeF4SimpleCoefficient r.val 2 = 0) :
    IsLeviRoot r := by
  have hc : r.val = typeF4SimpleRoot 0 ∨ r.val = -typeF4SimpleRoot 0 ∨
      r.val = typeF4SimpleRoot 3 ∨ r.val = -typeF4SimpleRoot 3 := by
    have sign_cases (x : ℝ) (hx : x ∈ ({-1, 1} : Set ℝ)) : x = -1 ∨ x = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    rcases r.property with (hp | hu) | hh
    · rcases hp with ⟨i, j, hij, a, b, ha, hb, hr⟩
      rw [hr] at h1 h2 ⊢
      rcases sign_cases a ha with rfl | rfl <;> rcases sign_cases b hb with rfl | rfl
      all_goals fin_cases i <;> fin_cases j
      all_goals norm_num [typeF4SimpleCoefficient, basisVector, Pi.single_apply, Fin.ext_iff] at h1 <;>
        norm_num [typeF4SimpleCoefficient, basisVector, Pi.single_apply, Fin.ext_iff] at h2
      all_goals first
        | exact False.elim (hij rfl)
        | (left; ext k; fin_cases k <;> norm_num [typeF4SimpleRoot, basisVector, Pi.single_apply, Fin.ext_iff] <;> first | assumption | done)
        | (right; left; ext k; fin_cases k <;> norm_num [typeF4SimpleRoot, basisVector, Pi.single_apply, Fin.ext_iff])
    · rcases hu with ⟨i, hi | hi⟩
      all_goals rw [hi] at h1 h2 ⊢
      all_goals fin_cases i
      all_goals norm_num [typeF4SimpleCoefficient, basisVector, Pi.single_apply, Fin.ext_iff] at h1
      all_goals norm_num [typeF4SimpleCoefficient, basisVector, Pi.single_apply, Fin.ext_iff] at h2
    · rcases hh with ⟨ε, he⟩
      rw [← he] at h1 h2 ⊢
      cases h0 : ε 0 <;> cases h1' : ε 1 <;> cases h2' : ε 2 <;> cases h3 : ε 3
      all_goals norm_num [typeF4SimpleCoefficient, halfSignVector, h0, h1', h2', h3] at h1 <;>
        norm_num [typeF4SimpleCoefficient, halfSignVector, h0, h1', h2', h3] at h2
      all_goals first
        | (right; right; left; ext k; fin_cases k <;> norm_num [typeF4SimpleRoot, halfSignVector, h0, h1', h2', h3] <;> first | assumption | done)
        | (right; right; right; ext k; fin_cases k <;> norm_num [typeF4SimpleRoot, halfSignVector, h0, h1', h2', h3] <;> assumption)
  rcases hc with hc | hc | hc | hc
  · exact ⟨0, by simp [leviNodes], Or.inl (Subtype.ext hc)⟩
  · refine ⟨0, by simp [leviNodes], Or.inr ?_⟩
    apply typeF4RootPairing.root.injective
    rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    exact hc
  · exact ⟨3, by simp [leviNodes], Or.inl (Subtype.ext hc)⟩
  · refine ⟨3, by simp [leviNodes], Or.inr ?_⟩
    apply typeF4RootPairing.root.injective
    rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    exact hc

/-- Every seed root is either a radical root or one of the four Levi roots. -/
theorem isSeedRoot_radical_or_levi {r : F4Chevalley.Root}
    (hr : IsSeedRoot .linear r) : IsRadicalRoot .linear r ∨ IsLeviRoot r := by
  classical
  rcases hr with hr | ⟨i, hi, hr⟩
  · by_cases h : IsRadicalRoot .linear r
    · exact Or.inl h
    · right
      apply isLeviRoot_of_middle_coefficients_zero
      · by_contra hn
        exact h ⟨hr, 1, by simp [leviNodes], hn⟩
      · by_contra hn
        exact h ⟨hr, 2, by simp [leviNodes], hn⟩
  · exact Or.inr ⟨i, hi, Or.inr hr⟩

/-- Generation by the specified radical and actual end-node Levi. This is a
subgroup join; relative normality and disjointness are separate calculations. -/
theorem splitSeed_eq_radical_sup_levi (m : ℕ) :
    splitSeed m .linear = splitRadical m .linear ⊔ splitLevi m := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨r, t, hr, rfl⟩
    rcases isSeedRoot_radical_or_levi hr with h | h
    · exact mem_sup_left (subset_closure ⟨r, t, h, rfl⟩)
    · exact mem_sup_right (root_mem_splitLevi m r t h)
  · exact sup_le ((splitRadical_le_unipotent m .linear).trans
      (splitUnipotent_le_splitSeed m .linear)) (splitLevi_le_seed m)

end ReeF4.Parabolics.BinaryLinear
