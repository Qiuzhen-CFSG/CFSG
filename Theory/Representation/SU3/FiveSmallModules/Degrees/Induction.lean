module

public import Theory.Representation.AbsolutelyIrreducible
public import Theory.Representation.Quotient
public import Mathlib.RepresentationTheory.Induced

/-!
# Induction from an actual Borel eigenline

An eigenvector for a subgroup character defines an explicit map out of the
induced representation. Evaluating it on the identity tensor recovers the
vector, so the map is nonzero, and it is surjective when the target is simple.
Surjective pullback also preserves absolute irreducibility on the same space.

The coinvariant formula follows Mathlib's `Rep.indResHomEquiv`, written here
without its common-carrier-universe restriction. Mathlib's implementation is
Copyright (c) 2025 Amelia Livingston, released under the Apache 2.0 license.
This is the Frobenius reciprocity step in the principal-series approach to
Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3, p.10.
-/

@[expose] public section

open scoped MonoidAlgebra
open Finsupp TensorProduct
namespace Representation.SU3.FiveSmallModules.Degrees

variable {K G U : Type*} [Field K] [Group G] [AddCommGroup U] [Module K U]

def scalarCharacter {B : Type*} [Group B] (χ : B →* Kˣ) : Representation K B K :=
  (algebraMap K (Module.End K K)).toMonoidHom.comp ((Units.coeHom K).comp χ)

@[simp] theorem scalarCharacter_apply {B : Type*} [Group B] (χ : B →* Kˣ) (b : B) (x : K) :
    scalarCharacter χ b x = (χ b : K) * x := rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def inductionLift {H A : Type*} [Group H] [AddCommGroup A] [Module K A]
    (f : H →* G) (α : Representation K H A) (τ : Representation K G U)
    (j : α.IntertwiningMap (τ.comp f)) : (ind f α).IntertwiningMap τ :=
  ⟨Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun g => τ g⁻¹ ∘ₗ j.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv K).toLinearMap)
    (fun h => by
      ext g a
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [ofMulAction_single, mul_inv_rev, j.isIntertwining]),
    fun g => by ext; simp⟩

@[simp] theorem inductionLift_mk {H A : Type*} [Group H] [AddCommGroup A] [Module K A]
    (f : H →* G) (α : Representation K H A) (τ : Representation K G U)
    (j : α.IntertwiningMap (τ.comp f)) (g : G) (a : A) :
    inductionLift f α τ j (IndV.mk f α g a) = τ g⁻¹ (j a) := by
  simp [inductionLift]

set_option backward.isDefEq.respectTransparency false in
noncomputable def inducedMap (B : Subgroup G) (χ : B →* Kˣ)
    (τ : Representation K G U) (v : U)
    (hv : ∀ b : B, τ b v = (χ b : K) • v) :
    (Representation.ind B.subtype (scalarCharacter χ)).IntertwiningMap τ := by
  let j : (scalarCharacter χ).IntertwiningMap (τ.comp B.subtype) :=
    ⟨(LinearMap.id : K →ₗ[K] K).smulRight v, by
      intro b
      apply LinearMap.ext
      intro x
      change ((χ b : K) * x) • v = τ b (x • v)
      rw [map_smul, hv, smul_smul, mul_comm]⟩
  exact inductionLift B.subtype (scalarCharacter χ) τ j

@[simp] theorem inducedMap_mk_one (B : Subgroup G) (χ : B →* Kˣ)
    (τ : Representation K G U) (v : U)
    (hv : ∀ b : B, τ b v = (χ b : K) • v) :
    inducedMap B χ τ v hv (IndV.mk B.subtype (scalarCharacter χ) 1 1) = v := by
  simp [inducedMap, inductionLift]

theorem inducedMap_surjective (B : Subgroup G) (χ : B →* Kˣ)
    (τ : Representation K G U) [IsIrreducible τ] (v : U) (hne : v ≠ 0)
    (hv : ∀ b : B, τ b v = (χ b : K) • v) :
    Function.Surjective (inducedMap B χ τ v hv) := by
  apply (IsIrreducible.surjective_or_eq_zero (inducedMap B χ τ v hv)).resolve_right
  intro hz
  apply hne
  have hh := inducedMap_mk_one B χ τ v hv
  rw [hz] at hh
  exact hh.symm

-- Pullback preserves absolute irreducibility on the same vector space.
theorem absolutelyIrreducible_comp_surjective
    {Q : Type*} [Group Q] (f : G →* Q) (hf : Function.Surjective f)
    (τ : Representation K Q U) (hi : τ.IsAbsolutelyIrreducible) :
    IsAbsolutelyIrreducible (τ.comp f) := by
  constructor
  have he : extendScalars (AlgebraicClosure K) (τ.comp f) =
      (τ.extendScalars (AlgebraicClosure K)).comp f := rfl
  rw [he]
  exact (irreducible_comp_surjective_iff f hf _).mpr hi.irreducible_of_closure

end Representation.SU3.FiveSmallModules.Degrees
