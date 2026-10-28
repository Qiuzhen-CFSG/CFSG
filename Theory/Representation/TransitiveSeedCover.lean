module
public import Theory.Representation.CyclicSeedTensor
public import Theory.LinearAlgebra.BinaryTwoTransitivity

/-!
# A permutation tensor cover from a transitive seed

Let commuting groups K and I act on a vector space. An equivariant K-seed
fixed pointwise by an I-point stabilizer extends to a map from its tensor
product with the permutation module of that orbit. Transport between two
choices differs by a stabilizer element, so the slice maps are well-defined.
The map is onto when the original product orbit generates the whole space.

For the binary natural plane the orbit is its three nonzero vectors. The
marked basis slice is the original seed, and all group elements act through
the supplied maps. This is the permutation cover used to recognize the two
second-tensor rows in Aschbacher--Smith 13.8.29(4), printed p.964.
-/

@[expose] public noncomputable section
open scoped TensorProduct BigOperators
namespace Representation.TransitiveSeedCover
open QuadraticFourGroup.TensorClassification
variable {k K I U W X : Type*} [Field k] [Group K] [Group I]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (ρ : Representation k (K × I) W) (σ : Representation k K U)
  (α : I →* Equiv.Perm X) (x₀ : X)
  (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
  (htrans : ∀ x, ∃ i, α i x₀ = x)
  (hfix : ∀ i, α i x₀ = x₀ → ∀ u, ρ (1,i) (f u) = f u)

def permutation : Representation k I (X → k) where
  toFun i := {
    toFun v x := v (α i⁻¹ x)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by ext v x; simp
  map_mul' i j := by ext v x; simp [mul_inv_rev]

def slice (x : X) : U →ₗ[k] W :=
  (ρ (1,Classical.choose (htrans x))).comp f.toLinearMap

include hfix in
private theorem same_slice (i j : I) (h : α i x₀ = α j x₀) (u : U) :
    ρ (1,i) (f u) = ρ (1,j) (f u) := by
  have hji : α (j⁻¹*i) x₀ = x₀ := by
    simp only [map_mul,Equiv.Perm.mul_apply,h]
    simp
  have hh := congrArg (ρ (1,j)) (hfix (j⁻¹*i) hji u)
  simpa only [←Module.End.mul_apply,←map_mul,Prod.mk_mul_mk,one_mul,
    mul_inv_cancel_left] using hh

include hfix in
theorem slice_eq (i : I) (x : X) (hi : α i x₀ = x) (u : U) :
    slice ρ σ α x₀ f htrans x u = ρ (1,i) (f u) := by
  apply same_slice ρ σ α x₀ f hfix
  exact (Classical.choose_spec (htrans x)).trans hi.symm

include hfix in
theorem slice_base (u : U) : slice ρ σ α x₀ f htrans x₀ u = f u := by
  have hh := slice_eq ρ σ α x₀ f htrans hfix 1 x₀ (by simp) u
  change slice ρ σ α x₀ f htrans x₀ u = ρ (1 : K × I) (f u) at hh
  simpa only [map_one,Module.End.one_apply] using hh

include hfix in
theorem slice_right (i : I) (x : X) (u : U) :
    ρ (1,i) (slice ρ σ α x₀ f htrans x u) =
      slice ρ σ α x₀ f htrans (α i x) u := by
  let j := Classical.choose (htrans x)
  have hj : α j x₀ = x := Classical.choose_spec (htrans x)
  rw [slice_eq ρ σ α x₀ f htrans hfix j x hj,
    slice_eq ρ σ α x₀ f htrans hfix (i*j) (α i x) (by simp [hj])]
  simp only [←Module.End.mul_apply,←map_mul,Prod.mk_mul_mk,one_mul]

theorem slice_left (a : K) (x : X) (u : U) :
    slice ρ σ α x₀ f htrans x (σ a u) =
      ρ (a,1) (slice ρ σ α x₀ f htrans x u) := by
  change ρ (1,_) (f (σ a u)) = ρ (a,1) (ρ (1,_) (f u))
  rw [IntertwiningMap.isIntertwining]
  change ρ (1,_) (ρ (a,1) (f u)) = _
  simp only [←Module.End.mul_apply,←map_mul,Prod.mk_mul_mk,one_mul,mul_one]

variable [Fintype X] [DecidableEq X]

def coordinateMap : (X → U) →ₗ[k] W :=
  ∑ x, (slice ρ σ α x₀ f htrans x).comp (LinearMap.proj x)

omit [DecidableEq X] in
theorem coordinateMap_apply (v : X → U) :
    coordinateMap ρ σ α x₀ f htrans v = ∑ x, slice ρ σ α x₀ f htrans x (v x) := by
  simp [coordinateMap]

def tensorMap : U ⊗[k] (X → k) →ₗ[k] W :=
  (coordinateMap ρ σ α x₀ f htrans).comp (TensorProduct.piScalarRight k k U X).toLinearMap

theorem tensorMap_tmul (u : U) (v : X → k) :
    tensorMap ρ σ α x₀ f htrans (u ⊗ₜ[k] v) =
      ∑ x, v x • slice ρ σ α x₀ f htrans x u := by
  change coordinateMap ρ σ α x₀ f htrans (fun x => v x • u) = _
  simp only [coordinateMap_apply,map_smul]

theorem tensorMap_single (u : U) (x : X) :
    tensorMap ρ σ α x₀ f htrans (u ⊗ₜ[k] Pi.single x 1) =
      slice ρ σ α x₀ f htrans x u := by
  rw [tensorMap_tmul]
  simp

include hfix in
theorem tensorMap_intertwines (g : K × I) :
    (tensorMap ρ σ α x₀ f htrans).comp (externalTensor σ (permutation (k:=k) α) g) =
      (ρ g).comp (tensorMap ρ σ α x₀ f htrans) := by
  apply TensorProduct.ext'
  intro u v
  change tensorMap ρ σ α x₀ f htrans (σ g.1 u ⊗ₜ[k] permutation α g.2 v) =
    ρ g (tensorMap ρ σ α x₀ f htrans (u ⊗ₜ[k] v))
  rw [tensorMap_tmul,tensorMap_tmul,map_sum]
  calc
    _ = ∑ x, v x • slice ρ σ α x₀ f htrans (α g.2 x) (σ g.1 u) := by
      apply Fintype.sum_equiv (α g.2)⁻¹
      intro x
      simp [permutation]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [←slice_right ρ σ α x₀ f htrans hfix,slice_left,map_smul]
      simp only [←Module.End.mul_apply,←map_mul,Prod.mk_mul_mk,one_mul,mul_one,Prod.mk.eta]

include hfix in
theorem tensorMap_surjective
    (hgen : (⨆ g : K × I, f.range.toSubmodule.map (ρ g)) = ⊤) :
    Function.Surjective (tensorMap ρ σ α x₀ f htrans) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [←hgen]
  apply iSup_le
  rintro g _ ⟨_,⟨u,rfl⟩,rfl⟩
  refine ⟨externalTensor σ (permutation (k:=k) α) g (u ⊗ₜ[k] Pi.single x₀ 1),?_⟩
  have hh := LinearMap.congr_fun (tensorMap_intertwines ρ σ α x₀ f htrans hfix g)
    (u ⊗ₜ[k] Pi.single x₀ 1)
  change tensorMap ρ σ α x₀ f htrans
    (externalTensor σ (permutation (k:=k) α) g (u ⊗ₜ[k] Pi.single x₀ 1)) = ρ g (f u)
  simpa only [LinearMap.comp_apply,tensorMap_single,slice_base ρ σ α x₀ f htrans hfix] using hh

end Representation.TransitiveSeedCover


namespace Representation.TransitiveSeedCover
open CyclicSeedTensor QuadraticFourGroup.TensorClassification

/-- The three nonzero vectors of the binary natural plane. -/
abbrev PlanePoint := {v : Fin 2 → ZMod 2 // v ≠ 0}

def basePoint : PlanePoint := ⟨first, by decide⟩

variable {I : Type*} [Group I]
  (β : I →* ((Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)))

def pointAction : I →* Equiv.Perm PlanePoint where
  toFun i := {
    toFun v := ⟨β i v,(β i).map_ne_zero_iff.mpr v.property⟩
    invFun v := ⟨β i⁻¹ v,(β i⁻¹).map_ne_zero_iff.mpr v.property⟩
    left_inv v := by apply Subtype.ext; change β i⁻¹ (β i v) = v; simp
    right_inv v := by apply Subtype.ext; change β i (β i⁻¹ v) = v; simp }
  map_one' := by ext v j; simp
  map_mul' i j := by ext v a; simp

theorem pointAction_transitive (hβ : Function.Surjective β) :
    ∀ x, ∃ i, pointAction β i basePoint = x := by
  intro x
  by_cases hx : (x : Fin 2 → ZMod 2) = first
  · refine ⟨1,?_⟩
    apply Subtype.ext
    simpa [pointAction,basePoint] using hx.symm
  · obtain ⟨r,hr,_⟩ := BinaryLinear.exists_linearEquiv_pair
      (first : Fin 2 → ZMod 2) second x first (by decide) (by decide) x.property
      (by decide) (by decide) hx
    obtain ⟨i,hi⟩ := hβ r
    refine ⟨i,?_⟩
    apply Subtype.ext
    change β i first = x
    rw [hi,hr]

theorem planePoint_card : Fintype.card PlanePoint = 3 := by decide

variable {K U Y : Type*} [Group K]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  (τ : Representation (ZMod 2) (K × I) Y) (σ : Representation (ZMod 2) K U)
  (f : σ.IntertwiningMap (τ.comp (MonoidHom.inl K I)))

/-- A seed fixed by the natural-point stabilizer constructs the permutation
tensor cover. Its marked basis slice is the supplied seed map. -/
theorem exists_binary_plane_cover (hβ : Function.Surjective β)
    (hfix : ∀ i, β i first = first → ∀ u, τ (1,i) (f u) = f u)
    (hgen : (⨆ g : K × I, f.range.toSubmodule.map (τ g)) = ⊤) :
    ∃ F : (externalTensor σ (permutation (k:=ZMod 2) (pointAction β))).IntertwiningMap τ,
      Function.Surjective F ∧ ∀ u, F (u ⊗ₜ[ZMod 2] Pi.single basePoint 1) = f u := by
  have hf (i : I) (hi : pointAction β i basePoint = basePoint) (u : U) :
      τ (1,i) (f u) = f u := hfix i (congrArg Subtype.val hi) u
  let F : (externalTensor σ (permutation (k:=ZMod 2) (pointAction β))).IntertwiningMap τ :=
    .mk (tensorMap τ σ (pointAction β) basePoint f (pointAction_transitive β hβ))
      (tensorMap_intertwines τ σ (pointAction β) basePoint f (pointAction_transitive β hβ) hf)
  refine ⟨F,tensorMap_surjective τ σ (pointAction β) basePoint f
    (pointAction_transitive β hβ) hf hgen,?_⟩
  intro u
  change tensorMap τ σ (pointAction β) basePoint f (pointAction_transitive β hβ)
    (u ⊗ₜ[ZMod 2] Pi.single basePoint 1) = f u
  rw [tensorMap_single,slice_base τ σ (pointAction β) basePoint f (pointAction_transitive β hβ) hf]

end Representation.TransitiveSeedCover
