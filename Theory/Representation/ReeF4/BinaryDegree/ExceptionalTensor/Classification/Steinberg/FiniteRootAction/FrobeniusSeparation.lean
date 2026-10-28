module

public import Theory.FieldTheory.FrobeniusCoefficientSeparation
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters

/-!
# The finite coefficient step for the original Ree action

The native coefficient field has degree `2*m+1`, so its distinct Frobenius
characters separate all ordinary tensor positions. The final theorem applies
to a subrepresentation of the literal `Model m` action: an actual leading-term
expansion modulo a remainder subspace yields each individual leading vector
modulo that same subspace. The paired-root expansion and its degree estimates
are separate obligations; neither finite irreducibility nor tensor realization
is assumed or asserted here.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), proof of 12.2 via 5.1, pp.43 and 54–55.
-/

public section

open scoped BigOperators
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction

variable {m : ℕ} {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem frobenius_linearIndependent (f : CoefficientField m →+* F) :
    LinearIndependent F (fun i : Fin (2*m+1) =>
      fun t : CoefficientField m => f (t ^ (2 ^ i.val))) := by
  have h := FiniteField.embedded_frobenius_linearIndependent (p := 2) f
  rw [GaloisField.finrank 2 (by omega : 2*m+1 ≠ 0)] at h
  exact h

theorem coefficients_mem (f : CoefficientField m →+* F) (U : Submodule F V)
    (v : Fin (2*m+1) → V)
    (h : ∀ t : CoefficientField m, ∑ i, f (t ^ (2 ^ i.val)) • v i ∈ U) :
    ∀ i, v i ∈ U := by
  have he := FiniteField.frobenius_coefficients_mem (p := 2) f U
  rw [GaloisField.finrank 2 (by omega : 2*m+1 ≠ 0)] at he
  exact he v h

/-- This consumer keeps the original finite Ree action and the original
subrepresentation. Only the explicit root-word expansion remains to be supplied. -/
theorem leading_coefficients_mem_sup
    (f : CoefficientField m →+* F) (σ : Representation F (Model m) V)
    (W : Subrepresentation σ) (R : Submodule F V)
    (g : CoefficientField m → Model m) {v : V} (hv : v ∈ W)
    (a : Fin (2*m+1) → V)
    (hexp : ∀ t, σ (g t) v - v - ∑ i, f (t ^ (2 ^ i.val)) • a i ∈ R) :
    ∀ i, a i ∈ W.toSubmodule ⊔ R := by
  apply coefficients_mem f
  intro t
  have hd : σ (g t) v - v ∈ W.toSubmodule ⊔ R :=
    (show W.toSubmodule ≤ W.toSubmodule ⊔ R from le_sup_left) (W.toSubmodule.sub_mem (W.apply_mem_toSubmodule (g t) hv) hv)
  have hr : σ (g t) v - v - ∑ i, f (t ^ (2 ^ i.val)) • a i ∈
      W.toSubmodule ⊔ R := (show R ≤ W.toSubmodule ⊔ R from le_sup_right) (hexp t)
  simpa only [sub_sub_cancel] using (W.toSubmodule ⊔ R).sub_mem hd hr

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
