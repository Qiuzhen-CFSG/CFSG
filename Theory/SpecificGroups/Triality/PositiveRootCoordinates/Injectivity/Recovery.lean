module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Injectivity.Weights
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration

/-!
# Recovering a canonical root parameter

Conjugate a root curve back along its actual chosen integral Tits route. Its
simple Cartan/opposite-root entry is exactly the parameter, over every
commutative ring. Weight transport shows that this linear functional reads
only the Cartan rows of the original opposite-root column. This retains all
integral route signs before any specialization of scalars.

Source: the Geck root-string construction and the uniqueness in GLS3,
1.12.7 and 2.3.6–7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open scoped BigOperators
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace Triality.Standard.PositiveCoordinates.Injectivity
noncomputable section
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {S : Type*} [CommRing S]

def positiveRecovery (r : ι) (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S) : S :=
  let route := rootRoute (P := P) (b := b) r
  ((specializeMatrix (S := S) (titsWordInv route.word) * A *
    specializeMatrix (S := S) (titsWord route.word)) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)
    (Sum.inl route.simple) (Sum.inr (P.reflectionPerm route.simple route.simple))

lemma positiveRecovery_curve (r : ι) (hr : b.IsPos r) (t : S) :
    positiveRecovery (b := b) r
      (rootCurveMatrix (integralChevalleyRootOperators (b := b)) r t) = t := by
  let := P.indexNeg
  let route := rootRoute (P := P) (b := b) r
  let T := rootCurveTitsWord (S := S) route.word
  change ((T⁻¹ * rootCurveUnit (integralChevalleyRootOperators (b := b)) r t * T).val)
    (Sum.inl route.simple) (Sum.inr (-route.simple : ι)) = t
  rw [rootCurveUnit_of_pos r hr]
  change ((T⁻¹ * (T * positiveUnit route.simple t * T⁻¹) * T).val) _ _ = t
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  change positiveMatrix route.simple t (Sum.inl route.simple) (Sum.inr (-route.simple : ι)) = t
  simp [positiveMatrix_formula, eDividedPower, eMatrix]

/-- Recovery only reads the Cartan rows of the column on the opposite root. -/
lemma positiveRecovery_congr (r : ι)
    (A B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)
    (h : ∀ c : b.support,
      A (Sum.inl c) (Sum.inr (P.reflectionPerm r r)) =
        B (Sum.inl c) (Sum.inr (P.reflectionPerm r r))) :
    positiveRecovery (b := b) r A = positiveRecovery (b := b) r B := by
  classical
  let := P.indexNeg
  let route := rootRoute (P := P) (b := b) r
  let g := (RootPairing.Equiv.weightHom P (b.wordProd route.word)).toAddEquiv
  have hU := transports_inv (rootWeight (b := b)) g.toEquiv
    (titsWord_transports route.word) (titsWord_mul_inv route.word)
    (titsWord_inv_mul route.word)
  have hleft (j : ι) : specializeMatrix (S := S) (titsWordInv route.word)
      (Sum.inl route.simple) (Sum.inr j) = 0 := by
    have hz : titsWordInv route.word (Sum.inl route.simple) (Sum.inr j) = 0 := by
      by_contra hne
      have he := hU (Sum.inl route.simple) (Sum.inr j) hne
      change (0 : M) = g.symm (P.root j) at he
      have he' := congrArg g he
      simp only [map_zero, g.apply_symm_apply] at he'
      exact P.ne_zero j he'.symm
    simp only [specializeMatrix, Matrix.map_apply, hz, map_zero]
  have hright (j : b.support ⊕ ι) (hj : j ≠ Sum.inr (-r)) :
      specializeMatrix (S := S) (titsWord route.word) j
        (Sum.inr (-route.simple : ι)) = 0 := by
    have he := congrFun (titsWord_mulVec_v route.word (-route.simple : ι)) j
    rw [reflectionWord_neg, route.target] at he
    simp only [v, Matrix.mulVec_single_one, Matrix.col_apply] at he
    have hz : titsWord route.word j (Sum.inr (-route.simple : ι)) = 0 := by
      simpa only [Pi.smul_apply, Pi.single_apply, if_neg hj, smul_zero] using he
    simp only [specializeMatrix, Matrix.map_apply, hz, map_zero]
  unfold positiveRecovery
  change ((_ * A * _) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)
      (Sum.inl route.simple) (Sum.inr (-route.simple : ι)) =
    ((_ * B * _) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)
      (Sum.inl route.simple) (Sum.inr (-route.simple : ι))
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = Sum.inr (-r)
  · subst j
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rcases k with k | k
    · congr 1
      exact h k
    · rw [hleft k, zero_mul, zero_mul]
  · rw [hright j hj]
    simp

end
end Triality.Standard.PositiveCoordinates.Injectivity
