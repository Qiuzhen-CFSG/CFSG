module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Certificate
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.NaturalCertificate
public import Theory.Representation.PSL3Two.SmallModuleProperties
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.Representation.AbsolutelyIrreducible

/-!
# Absolute irreducibility of the three binary linear-three models

The checked matrix certificates show that the natural and adjoint action
algebras contain every endomorphism. The natural-dual intertwiner transports
the same argument to the actual contragredient module. Density persists after
scalar extension, proving absolute irreducibility for all three models.

These are the model assertions accompanying the irreducible catalogue in
Aschbacher–Smith H.6.1, printed p.386 of the combined manuscript of 1 March 2004.
No irreducible-module classification is assumed in these proofs.
-/

@[expose] public section

open Matrix Representation
open scoped TensorProduct
namespace BinaryLinearThree.IrreducibleCatalogue

private theorem density_of_matrix_generators
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Representation (ZMod 2) Group V)
    (e : Module.End (ZMod 2) V ≃ₐ[ZMod 2] Matrix n n (ZMod 2))
    (a b : Group) (A B : Matrix n n (ZMod 2))
    (ha : e (ρ a) = A) (hb : e (ρ b) = B)
    (hd : ∀ Q : Subalgebra (ZMod 2) (Matrix n n (ZMod 2)), A ∈ Q → B ∈ Q → Q = ⊤) :
    Algebra.adjoin (ZMod 2) (Set.range ρ) = ⊤ := by
  let P := Algebra.adjoin (ZMod 2) (Set.range ρ)
  let Q := P.map e.toAlgHom
  have haQ : A ∈ Q := by
    rw [← ha]
    exact ⟨ρ a, Algebra.subset_adjoin (Set.mem_range_self a), rfl⟩
  have hbQ : B ∈ Q := by
    rw [← hb]
    exact ⟨ρ b, Algebra.subset_adjoin (Set.mem_range_self b), rfl⟩
  have hQ := hd Q haQ hbQ
  apply top_unique
  intro f _
  have hf : e f ∈ Q := by rw [hQ]; trivial
  obtain ⟨f', hf', he⟩ := hf
  exact e.injective he ▸ hf'

theorem natural_density : Algebra.adjoin (ZMod 2) (Set.range W) = ⊤ := by
  have hm (g : Group) : LinearMap.toMatrixAlgEquiv' (W g) = g.val := by
    change LinearMap.toMatrix' g.val.toLin' = g.val
    exact LinearMap.toMatrix'_toLin' _
  exact density_of_matrix_generators W LinearMap.toMatrixAlgEquiv'
    cycle shear cycle.val shear.val (hm cycle) (hm shear)
    NaturalCertificate.matrix_algebra_eq_top

noncomputable def adjointMatrixEquiv :
    Module.End (ZMod 2) Steinberg ≃ₐ[ZMod 2] Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  (coordinates.conjAlgEquiv (ZMod 2)).trans LinearMap.toMatrixAlgEquiv'

theorem steinberg_density : Algebra.adjoin (ZMod 2) (Set.range S) = ⊤ := by
  exact density_of_matrix_generators S adjointMatrixEquiv
    cycle shear cycleMatrix shearMatrix coordinateMatrix_cycle coordinateMatrix_shear
    Certificate.matrix_algebra_eq_top

theorem dual_density : Algebra.adjoin (ZMod 2) (Set.range W.dual) = ⊤ := by
  let e : Module.End (ZMod 2) (Module.Dual (ZMod 2) Vector) ≃ₐ[ZMod 2]
      Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    (AutomorphismAction.graphDualNatural.toLinearEquiv.conjAlgEquiv (ZMod 2)).trans
      LinearMap.toMatrixAlgEquiv'
  have he (g : Group) : e (W.dual (AutomorphismAction.graph g)) = g.val := by
    change LinearMap.toMatrix'
      (AutomorphismAction.graphDualNatural.conj
        ((W.dual.comp AutomorphismAction.graph.toMonoidHom) g)) = g.val
    rw [Representation.Equiv.conj_apply_self]
    exact LinearMap.toMatrix'_toLin' _
  exact density_of_matrix_generators W.dual e
    (AutomorphismAction.graph cycle) (AutomorphismAction.graph shear)
    cycle.val shear.val (he cycle) (he shear) NaturalCertificate.matrix_algebra_eq_top

private theorem absolute_of_density
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Nontrivial V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V)
    (hρ : Algebra.adjoin (ZMod 2) (Set.range ρ) = ⊤) : IsAbsolutelyIrreducible ρ := by
  refine ⟨?_⟩
  apply irreducible_of_jacobson_density_surjective
  exact (extendScalars_surj_iff (AlgebraicClosure (ZMod 2)) ρ).mp hρ

theorem natural_absolute : IsAbsolutelyIrreducible W :=
  absolute_of_density W natural_density

theorem dual_absolute : IsAbsolutelyIrreducible W.dual :=
  absolute_of_density W.dual dual_density

theorem steinberg_absolute : IsAbsolutelyIrreducible S := by
  let : Nontrivial Steinberg := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank (ZMod 2) Steinberg by rw [finrank_steinberg]; decide)
  exact absolute_of_density S steinberg_density

end BinaryLinearThree.IrreducibleCatalogue
