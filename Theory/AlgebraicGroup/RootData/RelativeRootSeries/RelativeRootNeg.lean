module

public import Theory.AlgebraicGroup.RootData.RelativeRoots

open scoped BigOperators

/-!
Negation identities for relative-root projections and heights.
-/

namespace Theory.AlgebraicGroup

/-- A zero relative-root projection has zero relative height. -/
public lemma relativeRootHeight_eq_zero_of_projection_eq_zero
    {ι : Type*} [Fintype ι]
    (coeff : ι → ι → ℤ) (base : Finset ι) (J : Set ι) {β : ι}
    (hzero : RelativeRootProjection coeff (base : Set ι) J β = 0) :
    RelativeRootHeight coeff base J β = 0 := by
  classical
  simp only [RelativeRootHeight]
  apply Finset.sum_eq_zero
  intro γ hγ
  by_cases hγJ : γ ∈ J
  · simp [hγJ]
  · have hvalue := congrArg (fun f : ι →₀ ℤ => f γ) hzero
    simpa [RelativeRootProjection, hγ, hγJ] using hvalue

/-- Reflection of a root in itself, hence root negation, reverses relative
height. -/
public lemma relativeRootHeight_reflectionPerm_self
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (α : ι) :
    RelativeRootHeight coeff base.support J (P.reflectionPerm α α) =
      -RelativeRootHeight coeff base.support J α := by
  classical
  have hCoeffUnique (β γ : ι) (hγ : γ ∈ base.support) {f : ι → ℤ}
      (hf : P.root β = ∑ j ∈ base.support, (f j : R) • P.root j) :
      coeff β γ = f γ := by
    have hc := (hCoeff β).1
    rw [base.support.sum_subtype (p := (· ∈ base.support)) (by simp)
      (F := inferInstance)] at hc hf
    have heq : ∑ j : base.support, (coeff β j : R) • P.root j =
        ∑ j : base.support, (f j : R) • P.root j := hc.symm.trans hf
    have heqCoeff : (coeff β γ : R) = (f γ : R) :=
      Fintype.linearIndependent_iffₛ.mp base.linearIndepOn_root
        (fun j : base.support => (coeff β j : R))
        (fun j : base.support => (f j : R)) heq ⟨γ, hγ⟩
    exact_mod_cast heqCoeff
  have hroot : P.root (P.reflectionPerm α α) =
      ∑ γ ∈ base.support, ((-coeff α γ : ℤ) : R) • P.root γ := by
    rw [P.root_reflectionPerm, P.reflection_apply_self, (hCoeff α).1]
    simp only [Int.cast_neg, neg_smul, Finset.sum_neg_distrib]
  simp only [RelativeRootHeight]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [hCoeffUnique (P.reflectionPerm α α) γ hγ hroot]
  by_cases hγJ : γ ∈ J
  · simp [hγJ]
  · simp [hγJ]

end Theory.AlgebraicGroup
