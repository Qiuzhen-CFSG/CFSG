module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.SpecificGroups.SL2.PrimeToResidual
public import Mathlib.GroupTheory.Solvable

/-!
# The prime-to-p residual of a two-dimensional unitary group

The determinant kernel in GU₂ is SU₂. If this SU₂ is identified with SL₂ over
a field of characteristic p, transvection generation puts it in O^{p′}.
The reverse inclusion follows when the multiplicative group of the matrix
field has order coprime to p. The abelian determinant quotient also places
the terminal derived subgroup in this kernel.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.3.21(a), printed p. 55. The finite quadratic-field witnesses are supplied
by the source-facing application.
-/

public section

namespace BenderSuzuki.MatrixGroups.HermitianForm

variable {F E : Type*} [Field F] [Field E] (J : HermitianForm 2 F)

/-- Determinant on the full unitary group. -/
@[expose] noncomputable def unitaryDet : J.unitarySubgroup →* Fˣ :=
  Matrix.GeneralLinearGroup.det.comp J.unitarySubgroup.subtype

/-- Its kernel is the actual special unitary group, with the same matrices. -/
noncomputable def unitaryDetKernelEquiv : J.unitaryDet.ker ≃* J.specialSubgroup where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- An actual SL₂ identification computes O^{p′}(GU₂), without perfectness. -/
theorem primeToResidual_eq_unitaryDet_ker (p : ℕ) [CharP E p]
    (e : J.specialSubgroup ≃* Matrix.SpecialLinearGroup (Fin 2) E)
    (hc : Nat.Coprime p (Nat.card Fˣ)) :
    Subgroup.primeToResidual p J.unitarySubgroup = J.unitaryDet.ker := by
  apply le_antisymm (Subgroup.primeToResidual_le_ker J.unitaryDet hc)
  intro x hx
  let f := J.unitaryDet.ker.subtype.comp
    ((J.unitaryDetKernelEquiv.trans e).symm.toMonoidHom)
  have h := Matrix.SL2.map_mem_primeToResidual p f
    (e (J.unitaryDetKernelEquiv ⟨x, hx⟩))
  simpa [f] using h

/-- The residual is genuinely SL₂ over the specified field. -/
noncomputable def unitaryPrimeToResidualEquiv (p : ℕ) [CharP E p]
    (e : J.specialSubgroup ≃* Matrix.SpecialLinearGroup (Fin 2) E)
    (hc : Nat.Coprime p (Nat.card Fˣ)) :
    Subgroup.primeToResidual p J.unitarySubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) E :=
  (MulEquiv.subgroupCongr (J.primeToResidual_eq_unitaryDet_ker p e hc)).trans
    (J.unitaryDetKernelEquiv.trans e)

/-- The commutator subgroup already lies in the residual. -/
theorem unitary_commutator_le_primeToResidual (p : ℕ) [CharP E p]
    (e : J.specialSubgroup ≃* Matrix.SpecialLinearGroup (Fin 2) E)
    (hc : Nat.Coprime p (Nat.card Fˣ)) :
    commutator J.unitarySubgroup ≤ Subgroup.primeToResidual p J.unitarySubgroup := by
  rw [J.primeToResidual_eq_unitaryDet_ker p e hc]
  exact Abelianization.commutator_subset_ker _

/-- In particular the terminal derived subgroup lies in O^{p′}. -/
theorem unitary_terminalDerived_le_primeToResidual (p : ℕ) [CharP E p]
    (e : J.specialSubgroup ≃* Matrix.SpecialLinearGroup (Fin 2) E)
    (hc : Nat.Coprime p (Nat.card Fˣ)) :
    (⨅ n : ℕ, derivedSeries J.unitarySubgroup n) ≤
      Subgroup.primeToResidual p J.unitarySubgroup :=
  (iInf_le _ 1).trans (J.unitary_commutator_le_primeToResidual p e hc)

end BenderSuzuki.MatrixGroups.HermitianForm

end
