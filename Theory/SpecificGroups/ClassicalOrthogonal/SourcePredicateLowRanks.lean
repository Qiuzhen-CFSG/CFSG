module

public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.FinCases

/-!
# Small split and odd orthogonal carriers

The rank-zero split space, the anisotropic odd line, and the rank-one
hyperbolic plane have trivial elementary groups. For the latter two this
follows directly from the Siegel formula. In characteristic two the existing
determinant-model equivalence identifies the literal rank-two projective
split carrier with SL₂ × SL₂; the first projection has a nontrivial proper
normal kernel. We do not replace the elementary carrier by the full isometry
group.

Source: the small-rank boundary of GLS3 Theorem 2.2.7 and §2.7; its application
here is Aschbacher–Smith Hypothesis 13.3.1(2), printed p.884.
-/

@[expose] public section
namespace ClassicalOrthogonal.SourcePredicateLowRanks

/-- The rank-zero split space has only the identity isometry. -/
theorem pOmegaPlus_zero_subsingleton (F : Type*) [Field F] : Subsingleton (POmegaPlus 0 F) := by
  exact Function.Surjective.subsingleton (projectiveElementaryMap_surjective (formD 0 F))

/-- In the anisotropic line, every singular direction is zero. -/
theorem omegaOdd_zero_eq_bot (F : Type*) [Field F] : elementarySubgroup (formB 0 F) = ⊥ := by
  apply le_antisymm _ bot_le
  change Subgroup.closure _ ≤ _
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  have hu0 : u = 0 := by
    apply Prod.ext (Subsingleton.elim _ _)
    have h : u.2 ^ 2 = 0 := by simpa using hu
    exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h
  subst u
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change Quadratic.siegel (formB 0 F) 0 v x = x
  simp [Quadratic.siegel]

/-- Every Siegel transformation of a hyperbolic plane is the identity. -/
theorem omegaPlus_one_eq_bot (F : Type*) [Field F] : elementarySubgroup (formD 1 F) = ⊥ := by
  apply le_antisymm _ bot_le
  change Subgroup.closure _ ≤ _
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change Quadratic.siegel (formD 1 F) u v x = x
  have hu' : u (.inl 0) * u (.inr 0) = 0 := by simpa using hu
  have huv' : u (.inl 0) * v (.inr 0) + v (.inl 0) * u (.inr 0) = 0 := by
    simpa only [polarD_apply, Fin.sum_univ_one] using huv
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    simp only [Quadratic.siegel, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, polarD_apply, formD_apply, Fin.sum_univ_one]
    rcases mul_eq_zero.mp hu' with hu0 | hu0
    · simp only [hu0, zero_mul, zero_add] at huv' ⊢
      rcases mul_eq_zero.mp huv' with hv0 | hu0 <;> simp_all <;> ring
    · simp only [hu0, mul_zero, add_zero] at huv' ⊢
      rcases mul_eq_zero.mp huv' with hu0 | hv0 <;> simp_all <;> ring

/-- The two actual SL₂ factors give a nontrivial proper normal subgroup. -/
theorem not_isSimpleGroup_pOmegaPlus_two (F : Type*) [Field F] [CharP F 2] :
    ¬ IsSimpleGroup (POmegaPlus 2 F) := by
  intro hsimp
  let := hsimp
  let S := Matrix.SpecialLinearGroup (Fin 2) F
  let t : S := Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) 1
  have ht : t ≠ 1 := by
    intro he
    have he' := congrArg (fun g : S => g 0 1) he
    simp [t, Matrix.SpecialLinearGroup.transvection, Matrix.transvection] at he'
  let : IsSimpleGroup (S × S) := FourPlusMatrix.projectiveEquiv.isSimpleGroup
  let p : S × S →* S := MonoidHom.fst S S
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal p.ker inferInstance with hb | htop
  · have he : (1, t) ∈ p.ker := by simp [p]
    rw [hb, Subgroup.mem_bot] at he
    exact ht (congrArg Prod.snd he)
  · have he : (t, 1) ∈ p.ker := htop ▸ Subgroup.mem_top _
    exact ht he

/-- Projectivizing the trivial odd elementary group preserves triviality. -/
theorem pOmegaOdd_zero_subsingleton (F : Type*) [Field F] :
    Subsingleton (POmegaOdd 0 F) := by
  have : Subsingleton (elementarySubgroup (formB 0 F)) := by
    rw [omegaOdd_zero_eq_bot]
    infer_instance
  exact (projectiveElementaryMap_surjective (formB 0 F)).subsingleton

/-- Projectivizing the trivial split rank-one elementary group preserves triviality. -/
theorem pOmegaPlus_one_subsingleton (F : Type*) [Field F] :
    Subsingleton (POmegaPlus 1 F) := by
  have : Subsingleton (elementarySubgroup (formD 1 F)) := by
    rw [omegaPlus_one_eq_bot]
    infer_instance
  exact (projectiveElementaryMap_surjective (formD 1 F)).subsingleton

end ClassicalOrthogonal.SourcePredicateLowRanks
