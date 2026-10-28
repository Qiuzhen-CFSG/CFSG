module

public import Theory.Representation.CubicClifford.Extension
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Homogeneous Clifford dimension and the multiplicity representation

Let `K` be normal in a finite group `H`, let `ρ` be an irreducible finite-dimensional
binary representation of `H`, and suppose an absolutely irreducible constituent
of `ρ|K` extends to an `H`-representation `τ` on `E`. Then evaluation identifies
`E ⊗ Hom_K(τ|K,ρ|K)` with `ρ`, and the Hom-space is an irreducible `H`-module.

Isaacs, *Character Theory of Finite Groups*, Theorem 6.5 supplies an actual
internal direct sum of conjugate constituents. The extension identifies each
conjugate with `τ|K`; absolute irreducibility makes its endomorphisms scalars.
Thus the Hom-space has one dimension per summand, proving the exact dimension
comparison needed by `evaluation_repEquiv_of_finrank_eq`. A nonzero invariant
subspace of the Hom-space then gives a nonzero map onto the irreducible tensor
representation, forcing that subspace to have full dimension.

This is the homogeneous multiplicity argument used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.21(1), printed p.956. No
homogeneity, multiplicity, tensor decomposition, or evaluation injectivity is
assumed.
-/

public section

open scoped TensorProduct MonoidAlgebra DirectSum
open Representation

noncomputable section

namespace Representation.CubicClifford
variable {F G V E : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup E] [Module F E]

private def submoduleEquiv (ρ : Representation F G V) (σ : Representation F G E)
    (B : Subrepresentation ρ) (e : B.toRepresentation ≃ₗ σ) :
    B.asSubmodule ≃ₗ[F[G]] σ.asModule := by
  let f : B.asSubmodule →ₗ[F[G]] σ.asModule := {
    toFun := fun v => σ.asModuleEquiv.symm (e ⟨ρ.asModuleEquiv v.1, v.2⟩)
    map_add' := fun x y => e.map_add _ _
    map_smul' := fun a v => by
      induction a using MonoidAlgebra.induction_linear with
      | zero =>
        simp only [RingHom.id_apply, zero_smul]
        exact e.map_zero
      | add a b ha hb =>
        simp only [RingHom.id_apply, add_smul]
        change e ((⟨(a • v).1, _⟩ : B.toSubmodule) + (⟨(b • v).1, _⟩ : B.toSubmodule)) = _
        rw [e.map_add]
        exact congrArg₂ (· + ·) ha hb
      | single g a =>
        simp only [RingHom.id_apply, SetLike.val_smul, Representation.single_smul]
        change e ⟨a • ρ g v.1, _⟩ = a • σ g (e ⟨v.1, v.2⟩)
        exact (e.map_smul a (B.toRepresentation g ⟨v.1, v.2⟩)).trans
          (congrArg (a • ·) (e.isIntertwining g ⟨v.1, v.2⟩)) }
  exact LinearEquiv.ofBijective f e.bijective

private def postcompEquiv (σ : Representation F G E)
    {M N : Type*} [AddCommGroup M] [Module F[G] M] [Module F M]
    [IsScalarTower F F[G] M] [AddCommGroup N] [Module F[G] N] [Module F N]
    [IsScalarTower F F[G] N] (e : M ≃ₗ[F[G]] N) :
    (σ.asModule →ₗ[F[G]] M) ≃ₗ[F] (σ.asModule →ₗ[F[G]] N) where
  toFun f := e.toLinearMap.comp f
  invFun f := e.symm.toLinearMap.comp f
  left_inv f := by ext x; exact e.symm_apply_apply (f x)
  right_inv f := by ext x; exact e.apply_symm_apply (f x)
  map_add' f g := by ext x; exact e.map_add _ _
  map_smul' a f := by ext x; exact e.map_smul_of_tower a (f x)

private theorem homogeneous_dimension (ρ : Representation F G V)
    (σ : Representation F G E) [FiniteDimensional F E] [IsIrreducible σ]
    [IsAbsolutelyIrreducible σ] {n : ℕ}
    (B : Fin n → Subrepresentation ρ)
    (hint : DirectSum.IsInternal (fun i => (B i).asSubmodule))
    (e : ∀ i, (B i).toRepresentation ≃ₗ σ) :
    Module.finrank F E * Module.finrank F (σ →ₗ ρ) = Module.finrank F V := by
  classical
  let : Nontrivial E := Subrepresentation.irreducible_module_nontrivial σ
  let c : ρ.asModule ≃ₗ[F[G]] (Fin n → σ.asModule) :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun i => (B i).asSubmodule)) hint).symm |>.trans
      ((DirectSum.linearEquivFunOnFintype F[G] (Fin n) _).trans
        (LinearEquiv.piCongrRight fun i => submoduleEquiv ρ σ (B i) (e i)))
  let h : (σ →ₗ ρ) ≃ₗ[F] (Fin n → End σ) :=
    (RepMap.equivLinearMapAsModule σ ρ).trans
      ((postcompEquiv σ c).trans
        ((LinearEquiv.linearMapPi F).symm.trans
          (LinearEquiv.piCongrRight fun _ => (RepMap.equivLinearMapAsModule σ σ).symm)))
  let s : F ≃ₗ[F] End σ := LinearEquiv.ofBijective (Algebra.linearMap F (End σ))
    ⟨(algebraMap F (End σ)).injective,
      (isAbsolutelyIrreducible_iff_surjective σ).mp inferInstance⟩
  have hd : Module.finrank F (σ →ₗ ρ) = n := by
    rw [h.finrank_eq, ← (LinearEquiv.piCongrRight (fun _ : Fin n => s)).finrank_eq]
    simp
  rw [hd]
  have hc := (c.restrictScalars F).finrank_eq
  have hs := σ.asModuleEquiv.finrank_eq
  have hr := ρ.asModuleEquiv.finrank_eq
  simpa [Module.finrank_pi_fintype, hs, hr, Nat.mul_comm] using hc.symm

private def extensionConjugateEquiv {H : Type*} [Group H] (K : Subgroup H) [K.Normal]
    (τ : Representation F H E) (x : H) :
    τ.comp K.subtype ≃ₗ conjugateRep (τ.comp K.subtype) x := by
  refine RepEquiv.mk (LinearEquiv.ofBijective (τ x) (Representation.apply_bijective τ x)) ?_
  intro k
  ext v
  change τ x (τ (k : H) v) = τ (x * (k : H) * x⁻¹) (τ x v)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp [mul_assoc]

variable {H : Type*} [Group H] [Finite H] (Ksub : Subgroup H) [Ksub.Normal]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- An extending absolutely irreducible constituent forces the evaluation source
to have exactly the dimension of the ambient irreducible representation. The
occurrence is an actual subrepresentation of the restriction to `Ksub`. -/
theorem homogeneous_finrank
    (τ : Representation (ZMod 2) H E) (ρ : Representation (ZMod 2) H V)
    [IsIrreducible ρ] [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V]
    (hσabs : IsAbsolutelyIrreducible (τ.comp Ksub.subtype))
    (A : Subrepresentation (ρ.comp Ksub.subtype))
    (hA : Nonempty (A.toRepresentation ≃ₗ τ.comp Ksub.subtype)) :
    Module.finrank (ZMod 2) (E ⊗[ZMod 2] homSpace Ksub τ ρ) =
      Module.finrank (ZMod 2) V := by
  classical
  let σ := τ.comp Ksub.subtype
  let : IsAbsolutelyIrreducible σ := hσabs
  let : IsIrreducible σ := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible σ
  have hAirr : IsIrreducible A.toRepresentation := hA.some.irreducible_of_euqiv inferInstance
  obtain ⟨n, t, hint, _, he, _⟩ := isaacs_theorem_6_5.{_, _, _, 0} ρ Ksub inferInstance A hAirr
  have ec (i : Fin n) :
      (conjugateSubrepresentation ρ Ksub A (t i)).toRepresentation ≃ₗ σ :=
    (he i).some.trans ((conjugateRepEquiv hA.some (t i)).trans
      (extensionConjugateEquiv Ksub τ (t i)).symm)
  have hd := homogeneous_dimension (ρ.comp Ksub.subtype) σ
    (fun i => conjugateSubrepresentation ρ Ksub A (t i)) hint ec
  let hh : homSpace Ksub τ ρ ≃ₗ[ZMod 2] (σ →ₗ ρ.comp Ksub.subtype) :=
    invariantsEquivIntertwiningMap σ (ρ.comp Ksub.subtype)
  rw [Module.finrank_tensorProduct, hh.finrank_eq]
  exact hd

/-- The actual multiplicity representation of an extending absolutely irreducible
constituent is irreducible. This follows from the evaluation equivalence obtained
using `homogeneous_finrank`. -/
theorem homRepresentation_irreducible
    (τ : Representation (ZMod 2) H E) (ρ : Representation (ZMod 2) H V)
    [IsIrreducible ρ] [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V]
    (hσabs : IsAbsolutelyIrreducible (τ.comp Ksub.subtype))
    (A : Subrepresentation (ρ.comp Ksub.subtype))
    (hA : Nonempty (A.toRepresentation ≃ₗ τ.comp Ksub.subtype)) :
    IsIrreducible (homRepresentation Ksub τ ρ) := by
  let μ := homRepresentation Ksub τ ρ
  have hd := homogeneous_finrank Ksub τ ρ hσabs A hA
  let e := (evaluation_repEquiv_of_finrank_eq Ksub τ ρ hσabs A hA hd).some
  let : IsIrreducible (τ.tprod μ) :=
    (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv inferInstance
  let : Nontrivial (E ⊗[ZMod 2] homSpace Ksub τ ρ) :=
    Subrepresentation.irreducible_module_nontrivial (τ.tprod μ)
  let : Nontrivial (homSpace Ksub τ ρ) := by
    by_contra h
    let : Subsingleton (homSpace Ksub τ ρ) := not_nontrivial_iff_subsingleton.mp h
    exact not_subsingleton (E ⊗[ZMod 2] homSpace Ksub τ ρ) inferInstance
  let : IsAbsolutelyIrreducible (τ.comp Ksub.subtype) := hσabs
  let : IsIrreducible (τ.comp Ksub.subtype) :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible (τ.comp Ksub.subtype)
  let : Nontrivial E := Subrepresentation.irreducible_module_nontrivial (τ.comp Ksub.subtype)
  refine ⟨fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hSne : S.toSubmodule ≠ ⊥ := by
    intro hz
    exact hS (Subrepresentation.toSubmodule_injective hz)
  obtain ⟨f, hf, hf0⟩ := S.toSubmodule.ne_bot_iff.mp hSne
  have hfmap : (f.1 : E →ₗ[ZMod 2] V) ≠ 0 := by
    intro hz
    exact hf0 (Subtype.ext hz)
  obtain ⟨v, hv⟩ : ∃ v : E, f.1 v ≠ 0 := by
    by_contra! h
    exact hfmap (LinearMap.ext h)
  let inc : S.toRepresentation.IntertwiningMap μ :=
    .mk S.toSubmodule.subtype (fun _ => by ext; rfl)
  let j : (τ.tprod S.toRepresentation).IntertwiningMap (τ.tprod μ) :=
    inc.lTensor τ
  have hj : j ≠ 0 := by
    intro hz
    have hz' := congrArg (fun q : (τ.tprod S.toRepresentation).IntertwiningMap (τ.tprod μ) =>
      evaluation Ksub τ ρ (q (v ⊗ₜ[ZMod 2] (⟨f, hf⟩ : S.toSubmodule)))) hz
    exact hv (by simpa [j, inc, Representation.IntertwiningMap.lTensor_apply] using hz')
  have hsurj := (Representation.IsIrreducible.surjective_or_eq_zero j).resolve_right hj
  have hle := LinearMap.finrank_le_finrank_of_surjective hsurj
  change Module.finrank (ZMod 2) (E ⊗[ZMod 2] homSpace Ksub τ ρ) ≤
    Module.finrank (ZMod 2) (E ⊗[ZMod 2] S.toSubmodule) at hle
  simp only [Module.finrank_tensorProduct] at hle
  have hm := Nat.le_of_mul_le_mul_left hle (Module.finrank_pos (R := ZMod 2) (M := E))
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.eq_top_of_finrank_eq (le_antisymm S.toSubmodule.finrank_le hm)

end Representation.CubicClifford
