module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.Operations

/-!
# Splitting the first factor of the specified tensor

The tensor in `Construction` is associated to the left and built by appending
factors. The restricted Steinberg step instead splits off its first factor.
Unit and associativity maps identify these actual representations, since the
remaining Frobenius exponents are all increased by one. This is a linear
intertwining equivalence; no tensor irreducibility is assumed.

Source: the iteration of GLS3, Theorem 2.8.5, and Corollary 2.8.6(a),
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open scoped TensorProduct
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v w
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

set_option backward.isDefEq.respectTransparency false in
/-- Split the literal prefix tensor into its first basic factor and the
Frobenius pullback of the tensor on the remaining digits. The map is built
from unit and associativity intertwiners, with no irreducibility premise. -/
def tensorHeadEquiv (A : BasicWeight → RationalFactor K)
    (φ : Monoid.End (Variety.Point K)) (a : ℕ → BasicWeight) (n : ℕ) :
    Representation.Equiv (tensor A φ (MonoidHom.id _) a (n + 1)).ρ
      (Representation.tprod ((A (a 0)).restrict (MonoidHom.id _)).ρ
        ((tensor A φ (MonoidHom.id _) (fun i => a (i + 1)) n).ρ.comp φ)) := by
  induction n with
  | zero =>
    exact (Representation.TensorProduct.lid k _).trans
      (Representation.TensorProduct.rid k _).symm
  | succ n ih =>
    let e := TensorProduct.congr ih.toLinearEquiv
      (LinearEquiv.refl k (A (a (n + 1))).Space)
    let f := e.trans (TensorProduct.assoc k _ _ _)
    refine .mk f ?_
    intro g
    apply TensorProduct.ext'
    intro x y
    change TensorProduct.assoc k _ _ _
      (ih ((tensor A φ (MonoidHom.id _) a (n + 1)).ρ g x) ⊗ₜ[k]
        ((A (a (n + 1))).action.action ((φ ^ (n + 1)) g)).val y) = _
    rw [show ih ((tensor A φ (MonoidHom.id _) a (n + 1)).ρ g x) =
      (Representation.tprod ((A (a 0)).restrict (MonoidHom.id _)).ρ
        ((tensor A φ (MonoidHom.id _) (fun i => a (i + 1)) n).ρ.comp φ)) g (ih x)
      from LinearMap.congr_fun (ih.isIntertwining' g) x]
    rw [pow_succ]
    change TensorProduct.assoc k _ _ _
      (TensorProduct.map _ _ (ih x) ⊗ₜ[k]
        ((A (a (n + 1))).action.action ((φ ^ n) (φ g))).val y) =
      TensorProduct.map _ (TensorProduct.map _ _)
        (TensorProduct.assoc k _ _ _ (ih x ⊗ₜ[k] y))
    rw [TensorProduct.map_map_assoc, TensorProduct.map_tmul]
    rfl

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
