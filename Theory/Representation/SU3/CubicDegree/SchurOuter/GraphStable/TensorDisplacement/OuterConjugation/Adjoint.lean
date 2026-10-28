module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.GeometryInterface
public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.Operators

/-!
# Adjoint geometry on the bundled tensor factor

The trace-zero adjoint model and `Space K .adjoint` use separately bundled
module instances. An explicit identity equivalence transports the geometric
intertwiner between them. Its transpose coordinates are identified with the
literal `adjointTranspose` matrix equation, and its covariance retains the
original special-unitary matrices and every pair of quotient representatives.

This adapts the independent adjoint geometry contract for tensoring at each
Frobenius embedding; no single-adjoint model of the original representation is
assumed. The Chapter K outer tensor construction consumes this adapter.
Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation.SL3.BinaryDefiningFactors
open Representation.SU3.CubicDegree.SchurOuter
open Representation.SU3.CubicDegree.SchurOuter.AdjointBounds
open Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose
open Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups

variable {F K H : Type*} [Field F] [Field K] [Group H]
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.OuterConjugation

private def adjointCarrier : Space K .adjoint ≃ₗ[K] AdjointSpace K where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem adjointCarrier_action (J : HermitianForm 3 F) (ι : F →+* K)
    (π : J.specialSubgroup →* SL(3,F)) (hπ : ∀ g, (π g).val = g.val.val)
    (g : J.specialSubgroup) (X : Space K .adjoint) :
    adjointCarrier (factorRep ι .adjoint (π g) X) =
      adjoint J ι g (adjointCarrier X) := by
  apply Subtype.ext
  rw [adjoint_apply]
  change natural ι (π g) * X.val * natural ι ((π g)⁻¹) = _
  rw [← map_inv]
  change Matrix.toLin' ((π g).val.map ι) * X.val * Matrix.toLin' ((π g⁻¹).val.map ι) = _
  rw [hπ, hπ]
  rfl

/-- Transport the matrix-model witness to the literal bundled adjoint factor. -/
theorem factor_intertwiner_of_adjointGraphIntertwiner
    (J : HermitianForm 3 F) (ι : F →+* K)
    (π : J.specialSubgroup →* SL(3,F)) (hπ : ∀ g, (π g).val = g.val.val)
    (p : J.specialSubgroup →* H) (α : MulAut H)
    (hg : AdjointGraphIntertwiner J ι p α) :
    ∃ S c : Space K .adjoint ≃ₗ[K] Space K .adjoint,
      (∀ x, c (S x) = adjointTranspose (c x)) ∧
      ∀ g h : J.specialSubgroup, p h = α (p g) →
        S.toLinearMap * factorRep ι .adjoint (π g) =
          factorRep ι .adjoint (π h) * S.toLinearMap := by
  obtain ⟨S, ⟨c, hc⟩, hS⟩ := hg
  let q := adjointCarrier (K := K)
  let S' := q.trans (S.trans q.symm)
  let c' := q.trans (c.trans q.symm)
  refine ⟨S', c', ?_, ?_⟩
  · intro x
    apply Subtype.ext
    apply LinearMap.toMatrix'.injective
    rw [adjointTranspose_matrix]
    change LinearMap.toMatrix' (c (S x)).val = (LinearMap.toMatrix' (c x).val).transpose
    simpa only [adjointMatrix_apply, LinearEquiv.coe_coe] using hc x
  · intro g h hh
    apply LinearMap.ext
    intro x
    apply q.injective
    change q (q.symm (S (q (factorRep ι .adjoint (π g) x)))) =
      q (factorRep ι .adjoint (π h) (q.symm (S (q x))))
    rw [q.apply_symm_apply, adjointCarrier_action J ι π hπ,
      adjointCarrier_action J ι π hπ, q.apply_symm_apply]
    exact LinearMap.congr_fun (hS g h hh) (q x)

end Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.OuterConjugation
