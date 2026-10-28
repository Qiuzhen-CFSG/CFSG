module

public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.Representation.ScalarDescent
public import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Displacement from actual paired tensor coordinates

In coordinates U tensor U tensor Z, an exchanged pair acts by matrix
transposition, followed by an operator on Z. Strict upper-triangular matrices
embed under displacement, contributing binomial(dim U,2)*dim Z dimensions.
For dim U at least eight this is at least 7/16 of the whole dimension.
Kernel base change and equivariant transport retain the literal displacement
operator when applying the bound over an algebraic closure.

`HasPairedTensorCoordinates` specifies the remaining realization input. No
claim is made that an arbitrary triality outer involution admits these
coordinates. Constructing them requires the actual finite representation
classification and the action of the coefficient involution on its factors.

Source: the tensor-product branch of Guralnick--Malle, *Classification of
2F-modules, II*, Section 3.5 and Lemma 8.6, internal pp.20, 56--57. The bound
here is an elementary sufficient estimate for the first-power F inequality.
-/

@[expose] public section

namespace Triality.OuterDisplacement

variable {F Z : Type*} [Field F] [AddCommGroup Z] [Module F Z]
  [FiniteDimensional F Z]

/-- Strict upper-triangular entries inject into the displacement of a transposed
factor pair, allowing an arbitrary operator on the remaining coordinates. -/
theorem transpose_displacement_ge (d : ℕ)
    (T : Module.End F (Fin d → Fin d → Z)) (S : Module.End F Z)
    (hT : ∀ x i j, T x i j = S (x j i)) :
    d.choose 2 * Module.finrank F Z ≤
      Module.finrank F (LinearMap.range (T - LinearMap.id)) := by
  classical
  let I := {p : Fin d × Fin d // p.1 < p.2}
  let upper : (I → Z) →ₗ[F] (Fin d → Fin d → Z) := {
    toFun f i j := if h : i < j then f ⟨(i, j), h⟩ else 0
    map_add' := by intro f g; ext i j; split_ifs with h <;> simp [h]
    map_smul' := by intro a f; ext i j; split_ifs with h <;> simp [h] }
  let j : (I → Z) →ₗ[F] LinearMap.range (T - LinearMap.id) :=
    ((T - LinearMap.id).comp upper).codRestrict _ (fun f => ⟨upper f, rfl⟩)
  have hj : Function.Injective j := by
    intro x y hxy
    funext p
    have hh := congrArg (fun z : LinearMap.range (T - LinearMap.id) =>
      (z : Fin d → Fin d → Z) p.val.1 p.val.2) hxy
    change T (upper x) p.val.1 p.val.2 - upper x p.val.1 p.val.2 =
      T (upper y) p.val.1 p.val.2 - upper y p.val.1 p.val.2 at hh
    simpa [hT, upper, p.property, not_lt_of_gt p.property] using hh
  have hb := LinearMap.finrank_le_finrank_of_injective hj
  have hcard : Fintype.card I = d.choose 2 := by
    simpa [I, Fintype.card_subtype] using (Fintype.card_product_filter_lt (α := Fin d))
  simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hcard, Nat.cast_id] using hb

/-- A transposed pair of factors of dimension at least eight moves at least
seven sixteenths of the entire space. -/
theorem transpose_displacement_ratio (d : ℕ) (hd : 8 ≤ d)
    (T : Module.End F (Fin d → Fin d → Z)) (S : Module.End F Z)
    (hT : ∀ x i j, T x i j = S (x j i)) :
    7 * Module.finrank F (Fin d → Fin d → Z) ≤
      16 * Module.finrank F (LinearMap.range (T - LinearMap.id)) := by
  have hb := transpose_displacement_ge d T S hT
  have hc : 7 * d * d ≤ 16 * d.choose 2 := by
    have hchoose := Nat.choose_two_right d
    have heven : 2 ∣ d * (d - 1) := d.even_mul_pred_self.two_dvd
    have he := Nat.mul_div_cancel' heven
    rw [← hchoose] at he
    have hd1 : d - 1 + 1 = d := by omega
    nlinarith
  have hm := Nat.mul_le_mul_right (Module.finrank F Z) hc
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_fin]
  nlinarith

end Triality.OuterDisplacement

open scoped TensorProduct

namespace Triality.OuterDisplacement

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
  [FiniteDimensional E W]

/-- Extension of scalars preserves the rank of the actual displacement map. -/
theorem displacement_finrank_baseChange (T : Module.End E W)
    (F : Type*) [Field F] [Algebra E F] :
    Module.finrank F (LinearMap.range (T.baseChange F - LinearMap.id)) =
      Module.finrank E (LinearMap.range (T - LinearMap.id)) := by
  have hk := (LinearMap.kerBaseChangeEquiv (E := F) (T - LinearMap.id)).finrank_eq
  rw [Module.finrank_baseChange, LinearMap.baseChange_sub, LinearMap.baseChange_id] at hk
  have hF := (T.baseChange F - LinearMap.id).finrank_range_add_finrank_ker
  have hE := (T - LinearMap.id).finrank_range_add_finrank_ker
  rw [Module.finrank_baseChange] at hF
  omega

/-- Actual coordinates for a paired tensor action after extension to the
algebraic closure. This records an operator realization, not its existence. -/
def HasPairedTensorCoordinates (T : Module.End E W) : Prop :=
  ∃ d r : ℕ, 8 ≤ d ∧ ∃
    e : (AlgebraicClosure E ⊗[E] W) ≃ₗ[AlgebraicClosure E]
      (Fin d → Fin d → Fin r → AlgebraicClosure E),
    ∃ S : Module.End (AlgebraicClosure E) (Fin r → AlgebraicClosure E),
      ∀ w i j, e (T.baseChange (AlgebraicClosure E) w) i j = S (e w j i)

/-- The paired-factor estimate descends to the original coefficient field
through the given equivariant coordinates and the actual scalar extension. -/
theorem displacement_ratio_of_pairedTensorCoordinates (T : Module.End E W)
    (h : HasPairedTensorCoordinates T) :
    7 * Module.finrank E W ≤ 16 * Module.finrank E (LinearMap.range (T - LinearMap.id)) := by
  obtain ⟨d, r, hd, e, S, he⟩ := h
  let T' := e.conj (T.baseChange (AlgebraicClosure E))
  have hT' : ∀ x i j, T' x i j = S (x j i) := by
    intro x i j
    simpa only [T', LinearEquiv.conj_apply_apply, e.apply_symm_apply] using he (e.symm x) i j
  have hb := transpose_displacement_ratio d hd T' S hT'
  have hdim : Module.finrank (AlgebraicClosure E)
      (Fin d → Fin d → Fin r → AlgebraicClosure E) = Module.finrank E W := by
    rw [← e.finrank_eq, Module.finrank_baseChange]
  have hr := Representation.BinaryOffender.NaturalTensor.operatorFixedCodim_eq_of_equiv
    (T.baseChange (AlgebraicClosure E)) T' e (fun x => by simp [T'])
  change Module.finrank (AlgebraicClosure E)
      (LinearMap.range (T.baseChange (AlgebraicClosure E) - LinearMap.id)) =
    Module.finrank (AlgebraicClosure E) (LinearMap.range (T' - LinearMap.id)) at hr
  rw [hdim, ← hr, displacement_finrank_baseChange] at hb
  exact hb

end Triality.OuterDisplacement
