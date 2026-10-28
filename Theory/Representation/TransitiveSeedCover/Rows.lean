module
public import Theory.Representation.TransitiveSeedCover.Kernel
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The two quotients of the binary three-point tensor cover

The permutation module on the three nonzero plane vectors splits as the
natural plane plus a trivial line, by sending a basis point x to (x,1).
Its natural projection has precisely the constant line as kernel. Tensor
right exactness identifies the corresponding constant tensor kernel.
The first isomorphism theorem then gives full equivariant coordinates for
either kernel alternative, preserving every marked basis slice.

Source application: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(4), printed p.964. Both alternatives use the supplied factor homomorphism,
so the literal quotient action and original conjugator survive the equivalence.
-/

@[expose] public noncomputable section
open scoped TensorProduct BigOperators
open Representation QuadraticFourGroup.TensorClassification CyclicSeedTensor
namespace Representation.TransitiveSeedCover

abbrev Plane := Fin 2 → ZMod 2

def planeProjection : (PlanePoint → ZMod 2) →ₗ[ZMod 2] Plane where
  toFun w := ∑ x, w x • (x : Plane)
  map_add' w z := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a w := by simp only [Pi.smul_apply,smul_smul,Finset.smul_sum,RingHom.id_apply,smul_eq_mul]

def planeAugmentation : (PlanePoint → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ x, LinearMap.proj x

def planeSplit : (PlanePoint → ZMod 2) →ₗ[ZMod 2] Plane × ZMod 2 :=
  planeProjection.prod planeAugmentation

private def planeSplitInverse : Plane × ZMod 2 → (PlanePoint → ZMod 2) :=
  fun v x => v.2 + v.1 0 * x.val 1 + v.1 1 * x.val 0

private theorem planeSplit_left : Function.LeftInverse planeSplitInverse planeSplit := by decide
private theorem planeSplit_right : Function.RightInverse planeSplitInverse planeSplit := by decide

theorem planeSplit_bijective : Function.Bijective planeSplit :=
  ⟨planeSplit_left.injective,planeSplit_right.surjective⟩

theorem planeSplit_single (x : PlanePoint) : planeSplit (Pi.single x 1) = ((x : Plane),1) := by
  ext j
  · simp [planeSplit,planeProjection]
  · simp [planeSplit,planeAugmentation]

theorem planeSplit_constant : planeSplit (fun _ => 1) = (0,1) := by decide

variable {I : Type*} [Group I] (β : I →* (Plane ≃ₗ[ZMod 2] Plane))

def planeNatural : Representation (ZMod 2) I Plane where
  toFun i := (β i).toLinearMap
  map_one' := by ext v j; simp
  map_mul' i j := by ext v a; simp

theorem planeProjection_intertwines (i : I) (w : PlanePoint → ZMod 2) :
    planeProjection (permutation (pointAction β) i w) = planeNatural β i (planeProjection w) := by
  change (∑ x, w (pointAction β i⁻¹ x) • (x : Plane)) =
    β i (∑ x, w x • (x : Plane))
  rw [map_sum]
  simp only [map_smul]
  apply Fintype.sum_equiv (pointAction β i)⁻¹
  intro x
  congr 1
  change (x : Plane) = β i (β i⁻¹ x)
  simp

def planeSplitEquiv : (permutation (k:=ZMod 2) (pointAction β)).Equiv
    ((planeNatural β).prod (Representation.trivial (ZMod 2) I (ZMod 2))) :=
  .mk (LinearEquiv.ofBijective planeSplit planeSplit_bijective) (by
    intro i
    apply LinearMap.ext
    intro w
    apply Prod.ext
    · exact planeProjection_intertwines β i w
    · change (∑ x, w (pointAction β i⁻¹ x)) = ∑ x, w x
      exact Fintype.sum_equiv (pointAction β i)⁻¹ _ _ (fun _ => rfl))

theorem planeProjection_surjective : Function.Surjective planeProjection := by
  intro v
  obtain ⟨w,hw⟩ := planeSplit_bijective.2 (v,0)
  exact ⟨w,congrArg Prod.fst hw⟩

private theorem planeProjection_exact : Function.Exact
    (LinearMap.const : ZMod 2 →ₗ[ZMod 2] PlanePoint → ZMod 2) planeProjection := by
  change ∀ w, planeProjection w = 0 ↔ ∃ a : ZMod 2, (fun _ : PlanePoint => a) = w
  decide

variable {K U Y : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  (σ : Representation (ZMod 2) K U)

def tensorPlaneProjection :
    (externalTensor σ (permutation (pointAction β))).IntertwiningMap
      (externalTensor σ (planeNatural β)) :=
  .mk (planeProjection.lTensor U) (by
    intro g
    apply TensorProduct.ext'
    intro u v
    change σ g.1 u ⊗ₜ[ZMod 2] planeProjection (permutation (pointAction β) g.2 v) =
      σ g.1 u ⊗ₜ[ZMod 2] planeNatural β g.2 (planeProjection v)
    rw [planeProjection_intertwines])

theorem tensorPlaneProjection_surjective : Function.Surjective (tensorPlaneProjection β σ) :=
  LinearMap.lTensor_surjective U planeProjection_surjective

theorem tensorPlaneProjection_kernel : (tensorPlaneProjection β σ).ker.toSubmodule =
    LinearMap.range (constantTensor (k:=ZMod 2) (U:=U) (X:=PlanePoint)) := by
  change LinearMap.ker (planeProjection.lTensor U) = _
  rw [(lTensor_exact U planeProjection_exact planeProjection_surjective).linearMap_ker_eq]
  have he : (LinearMap.const : ZMod 2 →ₗ[ZMod 2] PlanePoint → ZMod 2).lTensor U =
      (constantTensor (k:=ZMod 2) (U:=U) (X:=PlanePoint)).comp
        (_root_.TensorProduct.rid (ZMod 2) U).toLinearMap := by
    apply TensorProduct.ext'
    intro u a
    change u ⊗ₜ[ZMod 2] (fun _ => a) = constantTensor (a • u)
    rw [constantTensor_apply,TensorProduct.smul_tmul]
    congr 1
    ext x
    exact (mul_one a).symm
  rw [he,LinearMap.range_comp,LinearEquiv.range,Submodule.map_top]

private theorem equiv_of_same_kernel {k J V W Z : Type*} [Field k] [Group J]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup Z] [Module k Z]
    {ρ : Representation k J V} {τ : Representation k J W} {ν : Representation k J Z}
    (F : ρ.IntertwiningMap τ) (P : ρ.IntertwiningMap ν)
    (hF : Function.Surjective F) (hP : Function.Surjective P)
    (hker : P.ker.toSubmodule = F.ker.toSubmodule) :
    ∃ e : ν.Equiv τ, ∀ z, e (P z) = F z := by
  have hk : LinearMap.ker P.toLinearMap = LinearMap.ker F.toLinearMap := hker
  let e₁ := P.toLinearMap.quotKerEquivOfSurjective hP
  let e₂ := F.toLinearMap.quotKerEquivOfSurjective hF
  let e := e₁.symm.trans ((Submodule.quotEquivOfEq _ _ hk).trans e₂)
  have he (z : V) : e (P z) = F z := by
    change F.toLinearMap.quotKerEquivOfSurjective hF
      (Submodule.quotEquivOfEq _ _ hk
        ((P.toLinearMap.quotKerEquivOfSurjective hP).symm (P.toLinearMap z))) = F z
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply,Submodule.quotEquivOfEq_mk]
    rfl
  refine ⟨.mk e ?_,he⟩
  intro g
  apply LinearMap.ext
  intro w
  obtain ⟨z,rfl⟩ := hP w
  change e (ν g (P z)) = τ g (e (P z))
  rw [←IntertwiningMap.isIntertwining _ _ P,he,he,IntertwiningMap.isIntertwining]

/-- A constant kernel gives the full natural tensor, with every marked slice retained. -/
theorem natural_row_of_kernel
    (τ : Representation (ZMod 2) (K × I) Y)
    (F : (externalTensor σ (permutation (pointAction β))).IntertwiningMap τ)
    (hF : Function.Surjective F)
    (hker : F.ker.toSubmodule =
      LinearMap.range (constantTensor (k:=ZMod 2) (U:=U) (X:=PlanePoint))) :
    ∃ e : (externalTensor σ (planeNatural β)).Equiv τ,
      ∀ u (x : PlanePoint), e (u ⊗ₜ[ZMod 2] (x : Plane)) = F (u ⊗ₜ[ZMod 2] Pi.single x 1) := by
  obtain ⟨e,he⟩ := equiv_of_same_kernel F (tensorPlaneProjection β σ) hF
    (tensorPlaneProjection_surjective β σ) ((tensorPlaneProjection_kernel β σ).trans hker.symm)
  refine ⟨e,?_⟩
  intro u x
  have hh := he (u ⊗ₜ[ZMod 2] Pi.single x 1)
  change e (u ⊗ₜ[ZMod 2] planeProjection (Pi.single x 1)) = _ at hh
  have hp := congrArg Prod.fst (planeSplit_single x)
  change planeProjection (Pi.single x 1) = x at hp
  rwa [hp] at hh

/-- A zero kernel gives the natural-plus-trivial tensor, with its exact marked slice. -/
theorem extra_row_of_kernel
    (τ : Representation (ZMod 2) (K × I) Y)
    (F : (externalTensor σ (permutation (pointAction β))).IntertwiningMap τ)
    (hF : Function.Surjective F) (hker : F.ker.toSubmodule = ⊥) :
    ∃ e : (externalTensor σ
      ((planeNatural β).prod (Representation.trivial (ZMod 2) I (ZMod 2)))).Equiv τ,
      ∀ u (x : PlanePoint), e (u ⊗ₜ[ZMod 2] ((x : Plane),1)) = F (u ⊗ₜ[ZMod 2] Pi.single x 1) := by
  let E := externalTensorEquiv (Representation.Equiv.refl σ) (planeSplitEquiv β)
  let F' := F.ofBijective ⟨LinearMap.ker_eq_bot.mp hker,hF⟩
  refine ⟨E.symm.trans F',?_⟩
  intro u x
  change F (E.symm (u ⊗ₜ[ZMod 2] ((x : Plane),1))) = _
  congr 1
  apply E.toLinearEquiv.injective
  change E (E.symm (u ⊗ₜ[ZMod 2] ((x : Plane),1))) = E (u ⊗ₜ[ZMod 2] Pi.single x 1)
  rw [Representation.Equiv.apply_symm_apply]
  change u ⊗ₜ[ZMod 2] ((x : Plane),1) = u ⊗ₜ[ZMod 2] planeSplit (Pi.single x 1)
  rw [planeSplit_single]

end Representation.TransitiveSeedCover
