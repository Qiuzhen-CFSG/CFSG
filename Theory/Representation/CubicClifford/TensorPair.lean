module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Tensor coordinates for a pair of constituents

A two-dimensional trivial tensor factor produces two copies of the other
representation. The equivalence is built from a basis of the factor and
the distributivity and unit equivalences for tensor products. Restriction
to a subgroup in the second factor's kernel gives the same actual
intertwining equivalence. All vector-space universes are independent.

This is the coordinate step in the multiplicity argument supporting
Aschbacher–Smith 13.8.21(1), printed p.956. It assumes an actual tensor
representation; it does not construct the Clifford multiplicity space.
-/

public section

open scoped TensorProduct
namespace Representation.CubicClifford
variable {F H E M : Type*} [Field F] [Group H]
  [AddCommGroup E] [Module F E] [AddCommGroup M] [Module F M]
  [FiniteDimensional F M]

/-- A tensor factor with trivial action and dimension two gives two copies
of the other factor, by an actual intertwining equivalence. -/
noncomputable def tensorPair (τ : Representation F H E) (μ : Representation F H M)
    (hμ : ∀ h, μ h = 1) (hdim : Module.finrank F M = 2) :
    Representation.Equiv (τ.tprod μ) (τ.prod τ) := by
  let b : M ≃ₗ[F] (F × F) := LinearEquiv.ofFinrankEq M (F × F) (by
    simpa using hdim)
  let e : (E ⊗[F] M) ≃ₗ[F] (E × E) :=
    (_root_.TensorProduct.congr (LinearEquiv.refl F E) b).trans
      ((_root_.TensorProduct.prodRight F F E F F).trans
        ((_root_.TensorProduct.rid F E).prodCongr (_root_.TensorProduct.rid F E)))
  refine Representation.Equiv.mk e ?_
  intro h
  apply _root_.TensorProduct.ext'
  intro v m
  simp [e, Representation.prod, hμ]

/-- Restriction of a tensor to a subgroup acting trivially on its second
factor is a pair when that factor is two-dimensional. -/
noncomputable def restrictionTensorPair (τ : Representation F H E)
    (μ : Representation F H M) (K : Subgroup H) (hK : K ≤ μ.ker)
    (hdim : Module.finrank F M = 2) :
    Representation.Equiv ((τ.tprod μ).comp K.subtype)
      (Representation.prod (τ.comp K.subtype) (τ.comp K.subtype)) :=
  tensorPair (τ.comp K.subtype) (μ.comp K.subtype) (fun k => hK k.property) hdim

end Representation.CubicClifford
