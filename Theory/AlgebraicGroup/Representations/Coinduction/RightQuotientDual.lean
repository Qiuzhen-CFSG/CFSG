module

public import Theory.AlgebraicGroup.Representations.Coinduction.RightQuotient
public import Mathlib.LinearAlgebra.Pi

/-!
# Duality for finite right-coset coordinates of coinduction

Sum the evaluation pairings over the right cosets. Right multiplication
permutes those cosets, and the subgroup correction acts contragrediently on
each pair of coordinate blocks. The resulting perfect invariant pairing
identifies coinduction of the dual with the dual of coinduction whenever the
right-coset space is finite. No finite-dimensionality or semisimplicity of
the coefficient representation is needed.

This supplies the concrete pairing for the two M22 Hermitian inductions used
in Guralnick--Malle I, Proposition 5.1, pp.15--16. The induction comparison
itself is the finite-index induction/coinduction equivalence.
-/

@[expose] public noncomputable section
open Representation
namespace Theory.AlgebraicGroup
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Right translation permutes the right cosets. -/
def Subgroup.rightCosetMulEquiv (S : Subgroup G) (g : G) :
    Equiv.Perm (Quotient (QuotientGroup.rightRel S)) where
  toFun := Quotient.map' (fun x => x * g) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa only [mul_inv_rev, ← mul_assoc, mul_inv_cancel_right] using h)
  invFun := Quotient.map' (fun x => x * g⁻¹) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa only [mul_inv_rev, ← mul_assoc, mul_inv_cancel_right] using h)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x => change Quotient.mk _ (x * g * g⁻¹) = Quotient.mk _ x; simp
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h x => change Quotient.mk _ (x * g⁻¹ * g) = Quotient.mk _ x; simp

theorem Subgroup.rightCosetMulEquiv_apply (S : Subgroup G) (g : G)
    (q : Quotient (QuotientGroup.rightRel S)) :
    Subgroup.rightCosetMulEquiv S g q =
      Quotient.mk (QuotientGroup.rightRel S) (q.out * g) := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

namespace Representation
variable (S : Subgroup G) [Finite (Quotient (QuotientGroup.rightRel S))]
  (ρ : _root_.Representation k S V)

/-- Sum of the evaluation pairings over the finitely many right cosets. -/
def rightQuotientDualLinearEquiv :
    (Quotient (QuotientGroup.rightRel S) → Module.Dual k V) ≃ₗ[k]
      Module.Dual k (Quotient (QuotientGroup.rightRel S) → V) := by
  classical
  let : Fintype (Quotient (QuotientGroup.rightRel S)) := Fintype.ofFinite _
  exact LinearMap.lsum k (fun _ : Quotient (QuotientGroup.rightRel S) => V) k

private theorem pairing_invariant (g : G)
    (φ : Quotient (QuotientGroup.rightRel S) → Module.Dual k V)
    (v : Quotient (QuotientGroup.rightRel S) → V) :
    rightQuotientDualLinearEquiv S
      (coindRightQuotient S (Rep.of ρ.dual) g φ)
      (coindRightQuotient S (Rep.of ρ) g v) =
    rightQuotientDualLinearEquiv S φ v := by
  classical
  let : Fintype (Quotient (QuotientGroup.rightRel S)) := Fintype.ofFinite _
  simp only [rightQuotientDualLinearEquiv, LinearMap.lsum_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  simp only [coindRightQuotient_apply]
  change (∑ q, φ _ (ρ _ (ρ _ (v _)))) = _
  simp only [Representation.inv_self_apply]
  simpa only [Subgroup.rightCosetMulEquiv_apply, Quotient.mk'] using
    _root_.Equiv.sum_comp (Subgroup.rightCosetMulEquiv S g) (fun q => φ q (v q))

/-- Finite-index coinduction commutes with contragredient duality, in the
literal right-coset coordinates and right multiplication convention. -/
def rightQuotientDualEquiv :
    (coindRightQuotient S (Rep.of ρ.dual)).Equiv
      (coindRightQuotient S (Rep.of ρ)).dual :=
  .mk (rightQuotientDualLinearEquiv S) (by
    intro g
    ext φ v
    have h := pairing_invariant S ρ g φ
      (coindRightQuotient S (Rep.of ρ) g⁻¹ v)
    rw [Representation.self_inv_apply] at h
    exact h)
end Representation
end Theory.AlgebraicGroup
