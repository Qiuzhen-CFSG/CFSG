module

public import Theory.Representation.QuadraticFourGroup.TensorClassification.AlgebraicInputs
public import Theory.Representation.QuadraticFourGroup.TensorClassification.SchurReduction
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Irreducible representations of a direct product

Over an algebraically closed field, every finite-dimensional irreducible product
representation is an actual external tensor of two irreducible representations.
Choose a simple submodule for the first factor. The second factor acts on its
Hom-space by postcomposition; choose a simple submodule of that multiplicity
space. Density makes the external tensor of these two simple modules irreducible.
Its nonzero evaluation map to the original module is therefore an equivalence.
Finite bases then put both factors on the required coordinate spaces.

This supplies the product-module input to GLS2, Theorem 25.14, Step 5
(`refs/KGroup/GLS2/ChapterG.tex`, lines 906–928), and applies it to the actual
Schur-closure representation. No semisimplicity of a group algebra or
irreducibility of the original restricted representations is required.
-/

@[expose] public section

open scoped TensorProduct
namespace Representation.QuadraticFourGroup.TensorClassification

namespace ProductFactors

/-- Density in the two factors gives density, hence irreducibility, on their tensor. -/
theorem externalTensor_isIrreducible {F G H U V : Type*} [Field F] [IsAlgClosed F] [Monoid G] [Monoid H]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (τ : Representation F G U) (σ : Representation F H V)
    [τ.IsIrreducible] [σ.IsIrreducible] : (externalTensor τ σ).IsIrreducible := by
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial τ
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  apply irreducible_of_jacobson_density_surjective
  let A := Algebra.adjoin F (Set.range (externalTensor τ σ))
  have hleft (f : Module.End F U) : LinearMap.rTensor V f ∈ A := by
    have h : Algebra.adjoin F (Set.range τ) ≤
        A.comap (Module.End.rTensorAlgHom F U V) := by
      apply Algebra.adjoin_le
      rintro _ ⟨g, rfl⟩
      change TensorProduct.map (τ g) LinearMap.id ∈ A
      have := Algebra.subset_adjoin (R := F) (s := Set.range (externalTensor τ σ))
        (Set.mem_range_self (g, 1))
      simpa [externalTensor_apply, Module.End.one_eq_id, A] using this
    rw [jacobson_density_surjective_isAlgClosed_rep τ] at h
    exact h (by trivial)
  have hright (f : Module.End F V) : LinearMap.lTensor U f ∈ A := by
    have h : Algebra.adjoin F (Set.range σ) ≤
        A.comap (Module.End.lTensorAlgHom F V U) := by
      apply Algebra.adjoin_le
      rintro _ ⟨g, rfl⟩
      change TensorProduct.map LinearMap.id (σ g) ∈ A
      have := Algebra.subset_adjoin (R := F) (s := Set.range (externalTensor τ σ))
        (Set.mem_range_self (1, g))
      simpa [externalTensor_apply, Module.End.one_eq_id, A] using this
    rw [jacobson_density_surjective_isAlgClosed_rep σ] at h
    exact h (by trivial)
  apply top_unique
  intro f hf
  clear hf
  change f ∈ A
  obtain ⟨x, rfl⟩ := (homTensorHomEquiv F U V U V).surjective f
  induction x using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using A.zero_mem
  | tmul f g =>
    rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
    have hm := A.mul_mem (hleft f) (hright g)
    convert hm using 1
    ext u v
    simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  | add x y hx hy => simpa only [map_add] using A.add_mem hx hy

variable {F G H W U : Type*} [Field F] [Monoid G] [Monoid H]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]

private abbrev left (ρ : Representation F (G × H) W) := ρ.comp (MonoidHom.inl G H)

/-- The commuting second factor acts on the first-factor Hom-space by postcomposition. -/
private def multiplicity (ρ : Representation F (G × H) W) (τ : Representation F G U) :
    Representation F H (τ.IntertwiningMap (left ρ)) where
  toFun h := {
    toFun f := {
      toLinearMap := (ρ (1,h)).comp f.toLinearMap
      isIntertwining' g := by
        ext u
        change ρ (1,h) (f (τ g u)) = ρ (g,1) (ρ (1,h) (f u))
        rw [IntertwiningMap.isIntertwining]
        change ρ (1,h) (ρ (g,1) (f u)) = _
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        simp }
    map_add' f f' := by ext u; exact map_add (ρ (1,h)) _ _
    map_smul' a f := by ext u; exact map_smul (ρ (1,h)) a _ }
  map_one' := by
    ext f u
    change ρ (1 : G × H) (f u) = f u
    rw [map_one]
    rfl
  map_mul' h k := by
    ext f u
    change ρ (1,h*k) (f u) = ρ (1,h) (ρ (1,k) (f u))
    rw [← Module.End.mul_apply, ← map_mul]
    simp

private noncomputable def evaluation (ρ : Representation F (G × H) W)
    (τ : Representation F G U) (S : Subrepresentation (multiplicity ρ τ)) :
    (externalTensor τ S.toRepresentation).IntertwiningMap ρ where
  toLinearMap := TensorProduct.lift {
    toFun u := {
      toFun f := f.val u
      map_add' f g := rfl
      map_smul' a f := rfl }
    map_add' u v := by ext f; exact map_add f.val u v
    map_smul' a u := by ext f; exact map_smul f.val a u }
  isIntertwining' g := by
    ext u f
    change ρ (1,g.2) (f.val (τ g.1 u)) = ρ g (f.val u)
    rw [IntertwiningMap.isIntertwining]
    change ρ (1,g.2) (ρ (g.1,1) (f.val u)) = _
    rw [← Module.End.mul_apply, ← map_mul]
    simp

private noncomputable def coordinateEquiv (τ : Representation F G U) [FiniteDimensional F U] :
    τ.Equiv (((Module.finBasis F U).equivFun.conjAlgEquiv F).toAlgHom.toMonoidHom.comp τ) := by
  let e := (Module.finBasis F U).equivFun
  apply Representation.Equiv.mk e
  intro g
  apply LinearMap.ext
  intro u
  change e (τ g u) = e (τ g (e.symm (e u)))
  rw [e.symm_apply_apply]

variable [FiniteDimensional F W] [IsAlgClosed F]

set_option backward.isDefEq.respectTransparency false in
/-- Every finite-dimensional irreducible representation of a product of monoids over an
algebraically closed field is an external tensor of irreducible coordinate representations.
The equivalence is induced by evaluation on a simple submodule of the multiplicity space. -/
theorem exists_irreducible_externalTensor_factors (ρ : Representation F (G × H) W) [ρ.IsIrreducible] :
    ∃ (d₁ d₂ : ℕ) (τ₁ : Representation F G (Fin d₁ → F))
      (τ₂ : Representation F H (Fin d₂ → F)),
      τ₁.IsIrreducible ∧ τ₂.IsIrreducible ∧ Nonempty (ρ.Equiv (externalTensor τ₁ τ₂)) := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨T, hT⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (left ρ)
  let τ := T.toRepresentation
  let : τ.IsIrreducible := hT
  let : Nontrivial T.toSubmodule := Subrepresentation.irreducible_module_nontrivial τ
  let inc : τ.IntertwiningMap (left ρ) := .mk T.toSubmodule.subtype (by intro g; ext u; rfl)
  have hinc : inc ≠ 0 := by
    obtain ⟨u, hu⟩ := exists_ne (0 : T.toSubmodule)
    intro he
    have hz := congrArg (fun f : τ.IntertwiningMap (left ρ) => f u) he
    apply hu
    exact Subtype.ext hz
  let : Nontrivial (τ.IntertwiningMap (left ρ)) := ⟨⟨inc, 0, hinc⟩⟩
  obtain ⟨S, hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (multiplicity ρ τ)
  let : S.toRepresentation.IsIrreducible := hS
  let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial S.toRepresentation
  let ev := evaluation ρ τ S
  have hev : ev ≠ 0 := by
    obtain ⟨f, hf⟩ := exists_ne (0 : S.toSubmodule)
    have hf' : f.val ≠ 0 := fun h => hf (Subtype.ext h)
    obtain ⟨u, hu⟩ : ∃ u, f.val u ≠ 0 := by
      by_contra! h
      exact hf' (IntertwiningMap.ext (LinearMap.ext h))
    intro he
    exact hu (congrArg (fun e : (externalTensor τ S.toRepresentation).IntertwiningMap ρ =>
      e (u ⊗ₜ[F] f)) he)
  let : (externalTensor τ S.toRepresentation).IsIrreducible := externalTensor_isIrreducible τ S.toRepresentation
  let e := (ev.ofBijective ((IsIrreducible.bijective_or_eq_zero ev).resolve_right hev)).symm
  let e₁ := coordinateEquiv τ
  let e₂ := coordinateEquiv S.toRepresentation
  refine ⟨_, _, _, _, ?_, ?_, ⟨e.trans (externalTensorEquiv e₁ e₂)⟩⟩
  · exact (RepEquiv.ofRepresentationEquiv e₁.symm).irreducible_of_euqiv hT
  · exact (RepEquiv.ofRepresentationEquiv e₂.symm).irreducible_of_euqiv hS


end ProductFactors

/-- The product-module input for the genuine `PSL₂(2ⁿ) × PSL₂(2ⁿ)` carrier.
The general product theorem also covers parameters outside the source range `1 < n`. -/
theorem hasIrreducibleProductFactors_of_isAlgClosed
    {n : ℕ} {F W : Type*} [Field F] [IsAlgClosed F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F (Factor n × Factor n) W) [ρ.IsIrreducible] :
    HasIrreducibleProductFactors ρ :=
  ProductFactors.exists_irreducible_externalTensor_factors ρ

/-- The literal Schur-closure consumer used in the binary tensor classification.
There are no cubic fixed-point or single-factor classification premises. -/
theorem schurClosureRep_hasIrreducibleProductFactors
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (Factor n × Factor n) V) [σ.IsIrreducible] :
    HasIrreducibleProductFactors (schurClosureRep σ) :=
  hasIrreducibleProductFactors_of_isAlgClosed (schurClosureRep σ)

end Representation.QuadraticFourGroup.TensorClassification

end
