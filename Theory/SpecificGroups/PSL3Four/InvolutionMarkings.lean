module

public import Theory.SpecificGroups.PSL3Four.GraphFieldMarking
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.FieldTransport

/-!
# Graph and field involutions under arbitrary projective markings

Over the four-element field, separate graph and field involutions admit the
standard marking. Composing that marking with any supplied projective
isomorphism yields conjugacy inside the actual automorphism group.

Source: Aschbacher–Smith, 15.3.38, printed pp.1136–1137.
-/

public noncomputable section
open scoped MatrixGroups
namespace Matrix.PSL3Four.InvolutionMarkings
open Matrix.PSL3.OuterSolvable
open Matrix.PSL3Even.OuterElementaryRank.FixedRanks
private def coefficientEquiv {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 4) : K ≃+* Matrix.PSL3Four.F := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Matrix.PSL3Four.card_F])

private theorem field_order {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2) : orderOf σ = 2 := by
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hK)
  have he : σ = frobeniusEquiv K 2 := by
    ext x
    exact hσ x
  rw [he]
  exact FiniteField.frobeniusEquiv_orderOf_of_card hK

private theorem fieldEquiv_square {K : Type*} [Field K]
    (e : K ≃+* Matrix.PSL3Four.F) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2)
    (x : PSL(3,K)) :
    Atlas.fieldEquivPSL 3 e (Matrix.PSL3.OuterSolvable.fieldAction K σ x) =
      Matrix.PSL3Four.pslFrobenius (Atlas.fieldEquivPSL 3 e x) := by
  have he := Matrix.PSL3Four.fieldEquivPSL_graphField e σ hσ x
  change Atlas.fieldEquivPSL 3 e (graph K (Matrix.PSL3.OuterSolvable.fieldAction K σ x)) = _ at he
  rw [Matrix.PSL3.OddPrimeGraphExtension.FieldTransport.fieldEquivPSL_graph] at he
  exact (graph Matrix.PSL3Four.F).injective he

private theorem graph_marking {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (hs : (linearConj K g * graph K) ^ 2 = 1) :
    ∃ e : PSL(3,K) ≃* Matrix.PSL3Four.PSL, ∀ x,
      e ((linearConj K g * graph K) x) = graph Matrix.PSL3Four.F (e x) := by
  obtain ⟨a, ha⟩ := graph_involution_conjugate (f := 2) (by decide) hK g hs
  let f := coefficientEquiv hK
  refine ⟨a.trans (Atlas.fieldEquivPSL 3 f), fun x => ?_⟩
  have hx := DFunLike.congr_fun ha (a x)
  change a ((linearConj K g * graph K) (a.symm (a x))) = graph K (a x) at hx
  rw [a.symm_apply_apply] at hx
  change Atlas.fieldEquivPSL 3 f (a ((linearConj K g * graph K) x)) = _
  rw [hx]
  exact Matrix.PSL3.OddPrimeGraphExtension.FieldTransport.fieldEquivPSL_graph f (a x)

private theorem field_marking {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2)
    (hs : (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ) ^ 2 = 1) :
    ∃ e : PSL(3,K) ≃* Matrix.PSL3Four.PSL, ∀ x,
      e ((linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ) x) = Matrix.PSL3Four.pslFrobenius (e x) := by
  obtain ⟨C, hC⟩ := FieldDescent.exists_linear_conjugate_field g σ (field_order hK σ hσ) hs
  let a := linearConj K C
  let f := coefficientEquiv hK
  refine ⟨a.trans (Atlas.fieldEquivPSL 3 f), fun x => ?_⟩
  have hx := DFunLike.congr_fun hC (a x)
  change a ((linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ) (a.symm (a x))) = Matrix.PSL3.OuterSolvable.fieldAction K σ (a x) at hx
  rw [a.symm_apply_apply] at hx
  change Atlas.fieldEquivPSL 3 f (a ((linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ) x)) = _
  rw [hx]
  exact fieldEquiv_square f σ hσ (a x)


private theorem isConj_of_marking {K : Type*} [Group K]
    (a : MulAut K) (b : MulAut PSL) (e : K ≃* PSL)
    (e₀ : K ≃* PSL) (he₀ : ∀ x, e₀ (a x) = b (e₀ x)) :
    IsConj (MulAut.congr e a) b := by
  apply isConj_iff.mpr
  refine ⟨e.symm.trans e₀, ?_⟩
  ext x
  change e₀ (e.symm (e (a (e.symm (e (e₀.symm x)))))) = b x
  simp only [e.symm_apply_apply]
  rw [he₀, e₀.apply_symm_apply]

/-- Every supplied projective marking sends an involutory graph coset to
an automorphism conjugate to the standard graph automorphism. -/
theorem graph_isConj {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (hs : (linearConj K g * graph K) ^ 2 = 1)
    (e : PSL(3,K) ≃* PSL) :
    IsConj (MulAut.congr e (linearConj K g * graph K)) (graph F) := by
  obtain ⟨e₀, he₀⟩ := graph_marking hK g hs
  exact isConj_of_marking _ _ e e₀ he₀

/-- The analogous conjugacy for an involutory nontrivial field coset. -/
theorem field_isConj {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2)
    (hs : (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ) ^ 2 = 1)
    (e : PSL(3,K) ≃* PSL) :
    IsConj (MulAut.congr e (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ)) pslFrobenius := by
  obtain ⟨e₀, he₀⟩ := field_marking hK g σ hσ hs
  exact isConj_of_marking _ _ e e₀ he₀

end Matrix.PSL3Four.InvolutionMarkings
end
