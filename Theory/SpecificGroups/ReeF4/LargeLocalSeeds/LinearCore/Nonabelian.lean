module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates

/-!
# Noncommuting elements in the linear Ree radical

The four positive roots of the middle B₂ subsystem lie outside the end-node
Levi subsystem, so their twist-fixed Suzuki words lie in the linear radical.
The actual matrix-coordinate chart gives
`w(1,0) w(t,0) = w(1+t,t)` and `w(t,0) w(1,0) = w(1+t,σ(t))`, where σ is the
Tits field automorphism. Its square is Frobenius, so a scalar fixed by σ is
either zero or one. For m ≥ 1 the field has more than two elements; choosing
another scalar and using injectivity of the matrix chart proves noncommutation.

The fixedness, product law and injectivity used here are the proved concrete
root calculations in `SuzukiChart`, for the supplied `LocalBlockInput`.
Source: GLS3, Table 2.4, type V (`refs/KGroup/GLS3/chapter2.tex`); the linear
local factor in Aschbacher–Smith F.1.12(I)(5), printed p.263, and the local
block exclusion in 2.3.9(7), printed p.526 (`refs/quasithin.pdf`).
-/

public section

namespace ReeF4.LargeLocalSeeds

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open Parabolics.RadicalCoordinates.FixedCoordinates

private theorem exists_moved_scalar {m : ℕ} (hm : 1 ≤ m) :
    ∃ t : CoefficientField m, titsEnd m t ≠ t := by
  classical
  have hc : 2 < Fintype.card (CoefficientField m) := by
    rw [← Nat.card_eq_fintype_card, field_card]
    have h := pow_le_pow_right₀ (by decide : 1 ≤ 2) (by omega : 2 ≤ 2 * m + 1)
    omega
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset (CoefficientField m))) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_two (by simpa using hc))
  refine ⟨t, fun h => ?_⟩
  have hs : t ^ 2 = t := by rw [← titsEnd_twice, h, h]
  rcases eq_zero_or_one_of_sq_eq_self hs with h0 | h1
  · exact ht (by simp [h0])
  · exact ht (by simp [h1])

private theorem middle_root_radical (i : Fin 4) :
    IsRadicalRoot .linear (SuzukiChart.roots i) := by
  refine ⟨SuzukiChart.positive i, ?_⟩
  fin_cases i
  · exact ⟨1, by simp [leviNodes, Fin.ext_iff], by
      rw [SuzukiChart.roots_val]
      norm_num [typeF4SimpleCoefficient, Matrix.cons_val_two, Matrix.cons_val_three]⟩
  · exact ⟨2, by simp [leviNodes, Fin.ext_iff], by
      rw [SuzukiChart.roots_val]
      norm_num [typeF4SimpleCoefficient, Matrix.cons_val_two, Matrix.cons_val_three]⟩
  · exact ⟨1, by simp [leviNodes, Fin.ext_iff], by
      rw [SuzukiChart.roots_val]
      norm_num [typeF4SimpleCoefficient, Matrix.cons_val_two, Matrix.cons_val_three]⟩
  · exact ⟨1, by simp [leviNodes, Fin.ext_iff], by
      rw [SuzukiChart.roots_val]
      norm_num [typeF4SimpleCoefficient, Matrix.cons_val_two, Matrix.cons_val_three]⟩

private theorem middle_word_mem_radical {m : ℕ} (t u : CoefficientField m) :
    suzukiWord m true t u ∈ splitRadical m .linear := by
  have hr (i : Fin 4) (a : CoefficientField m) :
      rootGeneratorInGroup m (SuzukiChart.roots i) a ∈ splitRadical m .linear :=
    Subgroup.subset_closure ⟨_, _, middle_root_radical i, rfl⟩
  rw [SuzukiChart.word_eq, SuzukiChart.splitWord_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hr 0 _) (hr 1 _))
    (hr 2 _)) (hr 3 _)

private theorem middle_words_noncommute {m : ℕ} (t : CoefficientField m)
    (ht : titsEnd m t ≠ t) :
    suzukiWord m true 1 0 * suzukiWord m true t 0 ≠
      suzukiWord m true t 0 * suzukiWord m true 1 0 := by
  intro h
  rw [SuzukiChart.positive_mul, SuzukiChart.positive_mul] at h
  simp only [map_one, one_pow, zero_add, one_mul, mul_one] at h
  have hp : (1 + t, t) = (t + 1, (theta m t) ^ 2) := by
    apply SuzukiChart.positive_injective
    exact h
  have he : t = (theta m t) ^ 2 := congrArg Prod.snd hp
  exact ht ((halfFrobenius_sq m t).symm.trans he.symm)

/-- The specified root radical in the concrete linear local factor contains
two noncommuting elements, for every supplied Ree twist over a large field. -/
theorem seedRadical_linear_exists_noncommuting {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) :
    ∃ x y : standardSeed d .linear,
      x ∈ seedRadical d .linear ∧ y ∈ seedRadical d .linear ∧ x * y ≠ y * x := by
  obtain ⟨t, ht⟩ := exists_moved_scalar hm
  let w (a : CoefficientField m) : d.fixedGroup :=
    ⟨suzukiWord m true a 0, SuzukiChart.positive_fixed d a 0⟩
  have hw (a : CoefficientField m) : w a ∈ standardRadical d .linear :=
    middle_word_mem_radical a 0
  let x : standardSeed d .linear := ⟨w 1, standardRadical_le_seed d .linear (hw 1)⟩
  let y : standardSeed d .linear := ⟨w t, standardRadical_le_seed d .linear (hw t)⟩
  refine ⟨x, y, hw 1, hw t, ?_⟩
  intro h
  exact middle_words_noncommute t ht
    (congrArg (fun z : standardSeed d .linear => z.val.val) h)

end ReeF4.LargeLocalSeeds

end
