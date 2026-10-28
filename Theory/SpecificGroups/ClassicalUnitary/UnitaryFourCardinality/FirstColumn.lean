module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual.Generation.VectorReduction

/-!
# First-column fibers of the actual special unitary group

Every norm-one vector in dimension at least three is the first column of
a special unitary matrix over the same quadratic finite field of odd
characteristic. Multiplication by a vector reducer identifies its fiber
with matrices fixing the first coordinate vector. The checked tail-block
construction identifies this latter fiber with the actual SU in one lower
dimension, giving the special-unitary order recurrence.

`UnitaryFourCardinality` applies the recurrence in dimensions three and four.
This is the counting input for Aschbacher–Smith I.1.4(3), printed p.408 of
`refs/quasithin.pdf`, and GLS3 §6.1.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental.Generation
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)

private def firstColumn (n : ℕ) (g : (form σ hσ (n+1)).specialSubgroup) :
    {x : Fin (n+1) → F // norm σ x = 1} :=
  ⟨fun i => g.val.val i 0, column_norm σ hσ g 0⟩

private theorem mulVec_injective {n : ℕ} (a : (form σ hσ n).specialSubgroup) :
    Function.Injective (Matrix.mulVec a.val.val) := by
  intro v w h
  have hunit : (a⁻¹).val.val * a.val.val = 1 := by
    change (a⁻¹ * a).val.val = 1
    rw [inv_mul_cancel]
    rfl
  have hh := congrArg (Matrix.mulVec (a⁻¹).val.val) h
  simpa only [Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec] using hh

private noncomputable def tailFiberEquiv (n : ℕ) :
    (form σ hσ n).specialSubgroup ≃
      {g : (form σ hσ (n+1)).specialSubgroup //
        (fun i => g.val.val i 0) = Pi.single 0 1} := by
  classical
  let f : (form σ hσ n).specialSubgroup →
      {g : (form σ hσ (n+1)).specialSubgroup //
        (fun i => g.val.val i 0) = Pi.single 0 1} := fun a =>
    ⟨tailEmbedding σ hσ n a, by
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact congrArg (fun g : (form σ hσ (n+1)).specialSubgroup => g.val.val i.succ j.succ)
      (congrArg Subtype.val h)
  · intro g
    obtain ⟨a, ha⟩ := exists_tail_of_first_column σ hσ g.val (by
      intro i
      simpa [Pi.single_apply, eq_comm] using congrFun g.property i)
    exact ⟨a, Subtype.ext ha⟩

private noncomputable def reductionFiberEquiv {n : ℕ}
    (x : {x : Fin (n+1) → F // norm σ x = 1})
    (a : (form σ hσ (n+1)).specialSubgroup)
    (ha : a.val.val *ᵥ x.val = Pi.single 0 1) :
    {g : (form σ hσ (n+1)).specialSubgroup // firstColumn σ hσ n g = x} ≃
      {g : (form σ hσ (n+1)).specialSubgroup //
        (fun i => g.val.val i 0) = Pi.single 0 1} := by
  apply (Equiv.mulLeft a).subtypeEquiv
  intro g
  rw [Subtype.ext_iff]
  change (fun i => g.val.val i 0) = x.val ↔
    a.val.val *ᵥ (fun i => g.val.val i 0) = Pi.single 0 1
  rw [← ha]
  exact (mulVec_injective σ hσ a).eq_iff.symm

private theorem card_firstColumn_fiber [Finite F] (k : ℕ)
    (hred : UnitVectorReduction σ hσ k)
    (x : {x : Fin (k+3) → F // norm σ x = 1}) :
    Nat.card {g : (form σ hσ (k+3)).specialSubgroup // firstColumn σ hσ (k+2) g = x} =
      Nat.card (form σ hσ (k+2)).specialSubgroup := by
  obtain ⟨a, _, ha⟩ := hred x.val x.property
  exact (Nat.card_congr (reductionFiberEquiv σ hσ x a ha)).trans
    (Nat.card_congr (tailFiberEquiv σ hσ (k+2))).symm

theorem card_special_succ [Finite F] {r e : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hc : Nat.card F = (r^e)^2)
    (hj : ∀ x, σ x = x^(r^e)) (k : ℕ) :
    Nat.card (form σ hσ (k+3)).specialSubgroup =
      Nat.card {x : Fin (k+3) → F // norm σ x = 1} *
        Nat.card (form σ hσ (k+2)).specialSubgroup := by
  classical
  let : Fintype {x : Fin (k+3) → F // norm σ x = 1} := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (firstColumn σ hσ (k+2))), Nat.card_sigma]
  simp_rw [card_firstColumn_fiber σ hσ k (unitVectorReduction σ hσ hr he hc hj k)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality
