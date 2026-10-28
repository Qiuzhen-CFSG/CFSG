module
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.CubicInvariance.Support.Blocks

/-!
# Exact support of the marked zero-summand cubic

A nonzero coefficient cannot repeat a summand, by the concrete block
exclusions. The three summand labels therefore give a permutation of Fin 3.
Its inverse orders the original signed vectors into the literal odd, second,
and third marked families, with all signs retained.

This supplies the support branch consumed by `nonzeroReduction_of_branches`.
Only the specified odd-family comparison is conditional; the theorem has no
extra group-action or cubic-invariance premise.

Source: Aschbacher, *Sporadic Groups*, 9.3, 29.2(4), and the first paragraph
of the proof of 29.9, printed p. 158 (PDF p. 85).
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance

variable (e : oddSpace ≃ₗ[ℝ] TensorTwo)
  (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
include he

/-- On the literal signed families, every nonzero coefficient contains exactly
one vector from each source summand. This is the support step in 29.9; no
invariance or orbit-reduction hypothesis for `N` is used. -/
theorem nonzero_mixed_support :
    ∀ v : Fin 3 → ModelSpace, (∀ i, v i ∈ signedFamily) →
      tripleValue e v ≠ 0 → MixedShape v := by
  classical
  intro v hv hn
  have hs (k : Fin 3) : ∃ (i : Fin 3) (x : Omega) (b : ParkerLoop) (a : ℝ),
      (a = 1 ∨ a = -1) ∧ v k = a • markedVector i x b := by
    obtain ⟨i,x,b,h | h⟩ := hv k
    · exact ⟨i,x,b,1,Or.inl rfl,by simpa using h⟩
    · exact ⟨i,x,b,(-1 : ℝ),Or.inr rfl,h.trans (neg_one_smul ℝ _).symm⟩
  choose i x b a ha hvec using hs
  have hcoef : modelBeta e (markedVector (i 0) (x 0) (b 0))
      (markedVector (i 1) (x 1) (b 1)) (markedVector (i 2) (x 2) (b 2)) ≠ 0 := by
    intro hz
    apply hn
    simp only [tripleValue, hvec, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hz, mul_zero]
  have h01 : i 0 ≠ i 1 := by
    intro h
    apply hcoef
    rw [h]
    exact modelBeta_repeated_mark e he _ _ _ _ _ _ _ _
  have h02 : i 0 ≠ i 2 := by
    intro h
    apply hcoef
    rw [modelBeta_swap_right, h]
    exact modelBeta_repeated_mark e he _ _ _ _ _ _ _ _
  have h12 : i 1 ≠ i 2 := by
    intro h
    apply hcoef
    rw [modelBeta_swap_left, modelBeta_swap_right, h]
    exact modelBeta_repeated_mark e he _ _ _ _ _ _ _ _
  have hi : Function.Injective i := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp_all
  let p : Equiv.Perm (Fin 3) := (Equiv.ofBijective i
    (⟨hi, Finite.surjective_of_injective hi⟩)).symm
  have hip (k : Fin 3) : i (p k) = k :=
    (Equiv.ofBijective i (⟨hi, Finite.surjective_of_injective hi⟩)).apply_symm_apply k
  refine ⟨x (p 0),x (p 1),x (p 2),b (p 0),b (p 1),b (p 2),p,
    a (p 0),a (p 1),a (p 2),ha (p 0),ha (p 1),ha (p 2),?_⟩
  funext k
  fin_cases k <;> simp only [Function.comp_apply, hvec, hip, markedVector] <;> rfl

end Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance
