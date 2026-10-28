module

public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Descent
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual

/-!
# Applying coefficient descent to an inner-field involution

The coefficient-fixed equivalence discharges the descent premise of the
existing field-involution assembly, using the literal action and fixed field.
The independent cocycle-solving witness remains explicit: it identifies
the inner-field involution with a conjugate of the pure coefficient action.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 16.1.4(4), printed p.1171, and the full G₂(2) fixed group on p.1191.
-/

public section

namespace Atlas.G2.EvenFieldFixedResidual
open LieAutomorphismExtensions
variable {F : Type*} [Field F]

/-- Coefficient descent discharges the fixed-group equivalence input of the
field-involution assembly. Only the independent cocycle-solving input remains. -/
theorem field_involution_conclusion_of_coboundary [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F = 2 ^ n)
    (a : MulAut (Model F)) (ha : a ^ 2 = 1)
    (g : Model F) (σ : F ≃+* F)
    (he : a = MulAut.conj g * fieldAction σ)
    (hout : ∀ h : Model F, a ≠ MulAut.conj h)
    (hboundary : ∃ c : Model F, g = c * fieldAction σ c⁻¹) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧ Nat.card (fixedField σ) = 2 ^ m ∧
      orderOf (fieldAction σ) = 2 ∧
      (∃ c : Model F, a = MulAut.conj c * fieldAction σ * (MulAut.conj c)⁻¹) ∧
      Nonempty (a.fixedSubgroup ≃* Model (fixedField σ)) ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* commutator (Model (fixedField σ))) := by
  exact field_involution_conclusion_of_coboundary_of_descent hn hc a ha g σ he hout
    hboundary (coefficientFixedEquiv σ)

end Atlas.G2.EvenFieldFixedResidual
