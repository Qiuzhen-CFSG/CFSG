module
public import Theory.LinearAlgebra.BinaryLagrangianDualPair
public import Theory.Representation.BinaryPairedTransvections.Exchange
public import Theory.Representation.BinaryOffender.SubspaceAction
/-!
# The full actor in polar coordinates

Restriction to complementary singular subspaces gives the natural and dual
representations simultaneously. Full center transvections on the first
subspace therefore identify the literal image in the paired model.
-/
@[expose] public noncomputable section
namespace BinaryLagrangianDualPair
open Representation.BinaryOffender BinaryPairedTransvections
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) A V)

/-- The representation in a specified coordinate system, as a group homomorphism. -/
def coordinateActor {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (b : V ≃ₗ[ZMod 2] W) : A →* (W ≃ₗ[ZMod 2] W) where
  toFun a := b.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv
    (ρ.asGroupHom a)).trans b)
  map_one' := by ext w; simp
  map_mul' a a' := by ext w; simp

@[simp] theorem coordinateActor_apply {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (b : V ≃ₗ[ZMod 2] W) (a : A) (w : W) :
    coordinateActor ρ b a w=b (ρ a (b.symm w)) := rfl

theorem coordinateActor_injective {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (b : V ≃ₗ[ZMod 2] W) (hρ : Function.Injective ρ) :
    Function.Injective (coordinateActor ρ b) := by
  intro a a' h
  apply hρ
  ext v
  apply b.injective
  have hh := congrArg (fun f : W ≃ₗ[ZMod 2] W => f (b v)) h
  simpa only [coordinateActor_apply,b.symm_apply_apply] using hh

/-- The actual restriction of a subgroup preserving a subspace. -/
def restrictedActor (W : Submodule (ZMod 2) V) (K : Subgroup A)
    (hK : K ≤ subspaceStabilizer ρ W) : K →* (W ≃ₗ[ZMod 2] W) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp
    ((stabilizerRepresentation ρ W).asGroupHom.comp (Subgroup.inclusion hK))

@[simp] theorem restrictedActor_apply (W : Submodule (ZMod 2) V) (K : Subgroup A)
    (hK : K ≤ subspaceStabilizer ρ W) (k : K) (w : W) :
    (restrictedActor ρ W K hK k w:V)=ρ k w := rfl

variable [FiniteDimensional (ZMod 2) V]
  (q : QuadraticForm (ZMod 2) V) (E F : Submodule (ZMod 2) V)
  (hB : q.polarBilin.Nondegenerate) (hEF : IsCompl E F)
  (hE : ∀ e ∈ E, q e=0) (hF : ∀ f ∈ F, q f=0)
  (hdim : Module.finrank (ZMod 2) F=Module.finrank (ZMod 2) E)

omit [FiniteDimensional (ZMod 2) V] in
include hF in
theorem singular_polar_zero (x y : V) (hx : x∈F) (hy : y∈F) :
    q.polarBilin x y=0 := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    hF _ (F.add_mem hx hy),hF _ hx,hF _ hy,sub_zero]

def quadraticCoordinates : V ≃ₗ[ZMod 2] E × Module.Dual (ZMod 2) E :=
  coordinates q.polarBilin E F hB hEF (fun f hf f' hf' =>
    singular_polar_zero q F hF f f' hf hf') hdim

@[simp] theorem quadraticCoordinates_E (e : E) :
    quadraticCoordinates q E F hB hEF hF hdim e=(e,0) :=
  coordinates_E _ _ _ _ _ _ _ e

include hE in
theorem quadraticCoordinates_quadratic (v : V) :
    BinaryNaturalDual.quadratic (quadraticCoordinates q E F hB hEF hF hdim v)=q v := by
  obtain ⟨p,rfl⟩ := (Submodule.prodEquivOfIsCompl E F hEF).surjective v
  change BinaryNaturalDual.quadratic
    (coordinates q.polarBilin E F hB hEF _ hdim ((p.1:V)+(p.2:V)))=_
  rw [map_add,coordinates_E,coordinates_F]
  simp only [Prod.mk_add_mk,add_zero,zero_add]
  change q.polarBilin p.2 p.1=q ((p.1:V)+(p.2:V))
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    hF _ p.2.property,hE _ p.1.property,sub_zero,add_comm]

theorem quadraticCoordinates_equivariant (K : Subgroup A)
    (hKE : K ≤ subspaceStabilizer ρ E) (hKF : K ≤ subspaceStabilizer ρ F)
    (hqi : ∀ a v, q (ρ a v)=q v) (k : K) (v : V) :
    quadraticCoordinates q E F hB hEF hF hdim (ρ k v)=
      pairedAction (restrictedActor ρ E K hKE k)
        (quadraticCoordinates q E F hB hEF hF hdim v) := by
  apply coordinates_equivariant
    q.polarBilin E F hB hEF _ hdim
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom k))
    (restrictedActor ρ E K hKE k) (restrictedActor ρ F K hKF k)
    (fun _ => rfl) (fun _ => rfl) _ v
  intro x y
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  change q (ρ k x+ρ k y)-q (ρ k x)-q (ρ k y)=_
  rw [← map_add,hqi,hqi,hqi]

/-- Surjectivity of the actual transvection action identifies its whole image. -/
theorem coordinateActor_image_center (K : Subgroup A)
    (hKE : K ≤ subspaceStabilizer ρ E) (hKF : K ≤ subspaceStabilizer ρ F)
    (hqi : ∀ a v, q (ρ a v)=q v) (c : E) (hc : c≠0)
    (htrans : ∀ k : K, ∃ φ : Module.Dual (ZMod 2) E, φ c=0 ∧
      ∀ e : E, ρ k e=(e:V)+φ e • (c:V))
    (hfull : ∀ φ : Module.Dual (ZMod 2) E, φ c=0 → ∃ k : K,
      ∀ e : E, ρ k e=(e:V)+φ e • (c:V)) :
    K.map (coordinateActor ρ (quadraticCoordinates q E F hB hEF hF hdim))=
      (centerGroup c).map pairedAction := by
  have hr (k : K) : restrictedActor ρ E K hKE k∈centerGroup c := by
    obtain ⟨φ,hφ,he⟩ := htrans k
    apply (mem_centerGroup_iff c hc _).mpr
    refine ⟨φ,hφ,?_⟩
    ext e
    exact he e
  have hs : ∀ a ∈ centerGroup c, ∃ k : K, restrictedActor ρ E K hKE k=a := by
    intro a ha
    obtain ⟨φ,hφ,rfl⟩ := (mem_centerGroup_iff c hc a).mp ha
    obtain ⟨k,hk⟩ := hfull φ hφ
    exact ⟨k,by ext e; exact hk e⟩
  have heq (k : K) : coordinateActor ρ (quadraticCoordinates q E F hB hEF hF hdim) k=
      pairedAction (restrictedActor ρ E K hKE k) := by
    apply LinearEquiv.ext
    intro v
    rw [coordinateActor_apply,quadraticCoordinates_equivariant ρ q E F hB hEF hF hdim
      K hKE hKF hqi,LinearEquiv.apply_symm_apply]
  apply le_antisymm
  · rintro _ ⟨k,hk,rfl⟩
    rw [heq ⟨k,hk⟩]
    exact Subgroup.mem_map_of_mem _ (hr ⟨k,hk⟩)
  · rintro _ ⟨a,ha,rfl⟩
    obtain ⟨k,rfl⟩ := hs a ha
    rw [← heq]
    exact Subgroup.mem_map_of_mem _ k.property

end BinaryLagrangianDualPair
