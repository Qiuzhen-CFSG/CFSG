module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.ProjectiveData
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

/-!
# Conjugation and descent to a simple quotient's endomorphism algebra

A conjugation preserving the canonical root generators restricts to an algebra
automorphism of their generated algebra. The actual simple quotient action is
surjective onto its full endomorphism algebra by Jacobson density. Two such
surjective actions with the same kernel induce an automorphism of the full
endomorphism algebra. Mathlib's theorem that these automorphisms are inner
then supplies the required linear implementer.

The preservation of the generated algebra and of the quotient action's kernel
remain explicit premises. Neither is deduced from simplicity of the quotient.
This module supplies the algebraic descent in Steinberg's equations 4.1–4.2,
not the Curtis theorem identifying a module with each of its twists.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), Curtis 2.7 and equations 4.1–4.2; DOI 10.1017/S0027763000011016.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

omit [IsAlgClosed F] in
set_option backward.isDefEq.respectTransparency false in
private theorem equivalent_of_same_kernel
    {A V : Type u} [Ring A] [Algebra F A]
    [AddCommGroup V] [Module F V]
    (f h : A →ₐ[F] Module.End F V)
    (hf : Function.Surjective f) (hh : Function.Surjective h)
    (hker : LinearMap.ker f.toLinearMap = LinearMap.ker h.toLinearMap) :
    ∃ T : V ≃ₗ[F] V, ∀ a x, T (f a x) = h a (T x) := by
  let e : Module.End F V ≃ₗ[F] Module.End F V :=
    (f.toLinearMap.quotKerEquivOfSurjective hf).symm |>.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans
        (h.toLinearMap.quotKerEquivOfSurjective hh))
  have he (a : A) : e (f a) = h a := by
    change (h.toLinearMap.quotKerEquivOfSurjective hh)
      ((Submodule.quotEquivOfEq _ _ hker)
        ((f.toLinearMap.quotKerEquivOfSurjective hf).symm (f.toLinearMap a))) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
    rfl
  let E : Module.End F V ≃ₐ[F] Module.End F V :=
    { e with
      map_mul' := by
        intro x y
        obtain ⟨a, rfl⟩ := hf x
        obtain ⟨b, rfl⟩ := hf y
        change e (f a * f b) = e (f a) * e (f b)
        rw [← map_mul, he, map_mul, he, he]
      commutes' := by
        intro c
        change e (algebraMap F (Module.End F V) c) = algebraMap F (Module.End F V) c
        calc
          _ = e (f (algebraMap F A c)) := congrArg e (f.commutes c).symm
          _ = h (algebraMap F A c) := he _
          _ = _ := h.commutes c }
  obtain ⟨T, hT⟩ := E.eq_linearEquivConjAlgEquiv
  refine ⟨T, fun a x => ?_⟩
  have hE : E (f a) = h a := he a
  rw [hT] at hE
  have hx := congrArg (fun z : Module.End F V => z (T x)) hE
  simpa only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hx

/-- Conjugation on the original factor endomorphisms by its actual group action. -/
@[expose] def ambientConjugation (B : AlgebraicFactor F) (g : PointGroup F) :
    Module.End F B.Space ≃ₐ[F] Module.End F B.Space :=
  (B.action.action g).toLinearEquiv.conjAlgEquiv F

/-- The conjugation uses the original action, including its actual inverse. -/
theorem ambientConjugation_apply (B : AlgebraicFactor F) (g : PointGroup F)
    (a : Module.End F B.Space) :
    ambientConjugation B g a =
      (B.action.action g : Module.End F B.Space) * a *
        (B.action.action g⁻¹ : Module.End F B.Space) := by
  ext w
  change (B.action.action g : Module.End F B.Space)
    (a ((((B.action.action g)⁻¹ : LinearMap.GeneralLinearGroup F B.Space) :
      Module.End F B.Space) w)) = _
  rw [map_inv]
  rfl

/-- Inversion of group elements gives inverse conjugation. -/
theorem ambientConjugation_inv (B : AlgebraicFactor F) (g : PointGroup F) :
    ambientConjugation B g⁻¹ = (ambientConjugation B g).symm := by
  rw [ambientConjugation, map_inv]
  rfl

/-- The generator-level normalization assertion still needed from the root relations. -/
@[expose] def RootConjugationStable (B : AlgebraicFactor F) : Prop :=
  ∀ (g : PointGroup F) (r : F4Chevalley.Root),
    ambientConjugation B g (EndNode.Multiplicity.rootOperator B r) ∈ rootAlgebra B

/-- Preservation of generators extends to the whole generated algebra. -/
theorem ambientConjugation_mem (B : AlgebraicFactor F) (hs : RootConjugationStable B)
    (g : PointGroup F) (a : rootAlgebra B) :
    ambientConjugation B g (a : Module.End F B.Space) ∈ rootAlgebra B := by
  have h : rootAlgebra B ≤ (rootAlgebra B).comap (ambientConjugation B g).toAlgHom := by
    apply Algebra.adjoin_le
    rintro _ ⟨r, rfl⟩
    exact hs g r
  exact h a.property

/-- Restrict actual conjugation to the root algebra once normalization is proved. -/
@[expose] def rootConjugate (B : AlgebraicFactor F) (hs : RootConjugationStable B)
    (g : PointGroup F) : rootAlgebra B ≃ₐ[F] rootAlgebra B where
  toFun a := ⟨ambientConjugation B g a, ambientConjugation_mem B hs g a⟩
  invFun a := ⟨ambientConjugation B g⁻¹ a, ambientConjugation_mem B hs g⁻¹ a⟩
  left_inv a := by
    apply Subtype.ext
    change ambientConjugation B g⁻¹ (ambientConjugation B g a) = a
    rw [ambientConjugation_inv, AlgEquiv.symm_apply_apply]
  right_inv a := by
    apply Subtype.ext
    change ambientConjugation B g (ambientConjugation B g⁻¹ a) = a
    rw [ambientConjugation_inv, AlgEquiv.apply_symm_apply]
  map_mul' a b := Subtype.ext ((ambientConjugation B g).map_mul a b)
  map_add' a b := Subtype.ext ((ambientConjugation B g).map_add a b)
  commutes' c := Subtype.ext ((ambientConjugation B g).commutes c)

/-- The restricted automorphism has the prescribed underlying operator. -/
theorem rootConjugate_eq (B : AlgebraicFactor F) (hs : RootConjugationStable B)
    (g : PointGroup F) (a : rootAlgebra B) :
    (rootConjugate B hs g a : Module.End F B.Space) =
      (B.action.action g : Module.End F B.Space) * (a : Module.End F B.Space) *
        (B.action.action g⁻¹ : Module.End F B.Space) :=
  ambientConjugation_apply B g a

namespace SimpleCyclicQuotient
variable {B : AlgebraicFactor F} {v : B.Space} (Q : SimpleCyclicQuotient B v)

/-- The algebra homomorphism for the actual quotient module structure. -/
@[expose] def rootAction : rootAlgebra B →ₐ[F] Module.End F Q.Space :=
  Representation.jacobson_density_mapping F (rootAlgebra B) Q.Space

/-- Evaluation of the quotient algebra action is its given scalar action. -/
theorem rootAction_apply (a : rootAlgebra B) (w : Q.Space) :
    Q.rootAction a w = a • w := rfl

/-- The quotient algebra action recovers exactly the published root operators. -/
theorem rootAction_rootGenerator (r : F4Chevalley.Root) :
    Q.rootAction (rootGenerator B r) = Q.operator r := rfl

/-- Every element of the root algebra commutes with the actual quotient map. -/
theorem rootAction_projection (a : rootAlgebra B) (w : cyclicSubmodule B v) :
    Q.rootAction a (Q.projection w) = Q.projection ((cyclicSubmodule B v).module.smul a w) :=
  (Q.projection.map_smul a w).symm

/-- Simplicity and the algebraically closed ground field give full endomorphism density. -/
theorem rootAction_surjective : Function.Surjective Q.rootAction :=
  Representation.jacobson_density_surjective_isAlgClosed

/-- Kernel preservation suffices for a linear implementer of the twisted action. -/
theorem implementer_of_kernel (c : rootAlgebra B ≃ₐ[F] rootAlgebra B)
    (hc : ∀ a, Q.rootAction (c a) = 0 ↔ Q.rootAction a = 0) :
    ∃ T : Q.Space ≃ₗ[F] Q.Space, ∀ (a : rootAlgebra B) (w : Q.Space),
      T (a • w) = c a • T w := by
  apply equivalent_of_same_kernel Q.rootAction (Q.rootAction.comp c.toAlgHom)
    Q.rootAction_surjective (Q.rootAction_surjective.comp c.surjective)
  ext a
  exact (hc a).symm

end SimpleCyclicQuotient

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
