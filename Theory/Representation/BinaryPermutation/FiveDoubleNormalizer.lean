module
public import Theory.Representation.BinaryPermutation.FiveTensorNormalizer

/-!
# Extending two orthogonal A₅ copies to their ambient tensor normalizer

The normal A₅ acts on two copies of its binary augmentation core. Transporting
ambient conjugation through the fixed component isomorphism puts every ambient
operator in the proved tensor normalizer. Its unique S₅ × S₃ coordinates form a
faithful homomorphism and retain the original A₅ marking pointwise.

The second theorem constructs the tensor coordinates from the double-module
coordinates. The normalizer argument follows the existing Chapter13
FiveReconstruction/FullAction proof, without its separate S₃ marking premise.
Source: Aschbacher--Smith G.11.7--8, printed pp.366--368.
-/

public section
open Subgroup Representation
open scoped TensorProduct
namespace BinaryPermutation.FiveTensorNormalizer
abbrev TensorSpace := core (Fin 5) ⊗[ZMod 2] core (Fin 3)
abbrev TensorGroup := Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A faithful action whose restriction to a normal A₅ is two orthogonal
copies embeds in the actual tensor normalizer, with the same coordinates. -/
theorem exists_tensor_embedding
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (H : Subgroup G) [H.Normal] (e : H ≃* alternatingGroup (Fin 5))
    (f : V ≃ₗ[ZMod 2] TensorSpace)
    (he : ∀ (h : H) v, f (ρ h v) =
      ThreeTensor.action (coreRepresentation (Fin 5)) ((e h).val,1) (f v)) :
    ∃ j : G →* TensorGroup, Function.Injective j ∧
      (∀ g v, f (ρ g v) = ThreeTensor.action (coreRepresentation (Fin 5)) (j g) (f v)) ∧
      ∀ h : H, j h = ((e h).val,1) := by
  classical
  let τ := ThreeTensor.action (coreRepresentation (Fin 5))
  have exists_coordinates (g : G) : ∃ p : TensorGroup,
      ∀ v, f (ρ g v) = τ p (f v) := by
    let φ : MulAut (alternatingGroup (Fin 5)) :=
      e.symm.trans ((MulAut.conjNormal g).trans e)
    let t : TensorSpace ≃ₗ[ZMod 2] TensorSpace :=
      f.symm.trans ((LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)).trans f)
    have ht (a : alternatingGroup (Fin 5)) (w : TensorSpace) :
        t (τ (a.val,1) w) = τ ((φ a).val,1) (t w) := by
      obtain ⟨v,rfl⟩ := f.surjective w
      let h := e.symm a
      have hh : (e h).val = a.val := congrArg Subtype.val (e.apply_symm_apply a)
      change f (ρ g (f.symm (τ (a.val,1) (f v)))) = _
      rw [← hh, ← he h v, f.symm_apply_apply]
      have hc : e (MulAut.conjNormal g h) = φ a := rfl
      rw [show τ ((φ a).val,1) (t (f v)) =
          f (ρ (MulAut.conjNormal g h : H) (ρ g v)) by
        simpa only [t, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
          f.symm_apply_apply, hc] using (he (MulAut.conjNormal g h) (ρ g v)).symm]
      simp only [MulAut.conjNormal_apply, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    obtain ⟨p,hp⟩ := tensor_normalizer t φ ht
    exact ⟨p, fun v => by simpa only [t, LinearEquiv.trans_apply,
      LinearEquiv.ofBijective_apply, f.symm_apply_apply] using hp (f v)⟩
  choose p hp using exists_coordinates
  have unique (a b : TensorGroup) (hh : ∀ v, τ a (f v) = τ b (f v)) : a = b := by
    apply tensor_coordinates_unique
    intro w
    obtain ⟨v,rfl⟩ := f.surjective w
    exact hh v
  let j : G →* TensorGroup := {
    toFun := p
    map_one' := unique _ _ (fun v => by rw [← hp,map_one,map_one]; rfl)
    map_mul' := fun a b => unique _ _ (fun v => by
      rw [← hp,map_mul,Module.End.mul_apply,hp,hp,map_mul,Module.End.mul_apply]) }
  have hj (g : G) (v : V) : f (ρ g v) = τ (j g) (f v) := hp g v
  refine ⟨j,?_,hj,?_⟩
  · intro a b hab
    apply hf
    ext v
    apply f.injective
    rw [hj,hj,hab]
  · intro h
    apply unique
    intro v
    rw [← hj,he]

/-- Two constituent coordinates give the tensor coordinates used in the
normalizer theorem, retaining the component isomorphism. -/
theorem exists_tensor_embedding_of_double
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (H : Subgroup G) [H.Normal] (e : H ≃* alternatingGroup (Fin 5))
    (f : V ≃ₗ[ZMod 2] (core (Fin 5) × core (Fin 5)))
    (he : ∀ (h : H) v, f (ρ h v) =
      (alternatingCoreRepresentation (Fin 5) (e h) (f v).1,
       alternatingCoreRepresentation (Fin 5) (e h) (f v).2)) :
    ∃ j : G →* TensorGroup, ∃ t : V ≃ₗ[ZMod 2] TensorSpace,
      Function.Injective j ∧
      (∀ g v, t (ρ g v) = ThreeTensor.action (coreRepresentation (Fin 5)) (j g) (t v)) ∧
      ∀ h : H, j h = ((e h).val,1) := by
  let t := f.trans ThreeTensor.pairEquiv.symm
  have ht (h : H) (v : V) : t (ρ h v) =
      ThreeTensor.action (coreRepresentation (Fin 5)) ((e h).val,1) (t v) := by
    apply ThreeTensor.pairEquiv.injective
    change ThreeTensor.pairEquiv (ThreeTensor.pairEquiv.symm (f (ρ h v))) = _
    rw [ThreeTensor.pairEquiv.apply_symm_apply,ThreeTensor.pairEquiv_equivariant]
    dsimp only [t,LinearEquiv.trans_apply]
    rw [ThreeTensor.pairEquiv.apply_symm_apply]
    exact he h v
  obtain ⟨j,hj,hjt,hje⟩ := exists_tensor_embedding ρ hf H e t ht
  exact ⟨j,t,hj,hjt,hje⟩
end BinaryPermutation.FiveTensorNormalizer
