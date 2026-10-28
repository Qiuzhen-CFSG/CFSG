module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Interface

/-!
# Invariant flags and coordinates on their literal successive quotients

An adapted linear equivalence transports initial coordinate segments to
subspaces of the actual permutation representation. Upper block triangularity
makes them invariant under the two generators. Injectivity on each finite
subspace gives invariance under inverse generators, and free-group induction
then gives the full invariant flag.

Projection onto a successive coordinate block is surjective and has kernel
exactly the preceding stage, viewed inside the next stage. The first
isomorphism theorem therefore provides coordinates on the literal quotient.
Removing the zero terms outside that block proves generator equivariance.

This constructs the coordinate ingredient used in Aschbacher–Smith G.7.2(3),
printed pp.347–348, from matrix identities; `AdaptedFlag` supplies those identities.
-/

@[expose] public section

open G2DerivedPermutationFiltration.VertexCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
open Representation

namespace G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.AdaptedFlag

variable (i : Fin 2) (e : Space ≃ₗ[ZMod 2] (Fin 63 → ZMod 2))

def space (m : ℕ) : Submodule (ZMod 2) Space where
  carrier := {v | ∀ x : Fin 63, cut i m ≤ x.val → e v x = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw x hx; simp [hv x hx, hw x hx]
  smul_mem' := by intro a v hv x hx; simp [hv x hx]

variable (he : ∀ j v, e (representation i (FreeGroup.of j) v) =
  (actionMatrix i j).mulVec (e v))
  (ht : ∀ m j (x y : Fin 63), cut i m ≤ x.val → y.val < cut i m →
    actionMatrix i j x y = 0)

include he ht

theorem generator_mem (m : ℕ) (j : Fin 2) {v : Space} (hv : v ∈ space i e m) :
    representation i (FreeGroup.of j) v ∈ space i e m := by
  intro x hx
  rw [he]
  change (∑ y : Fin 63, actionMatrix i j x y * e v y) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y.val < cut i m
  · rw [ht m j x y hx hy, zero_mul]
  · rw [hv y (by omega), mul_zero]

theorem word_mem (m : ℕ) (g : WordGroup) :
    ∀ v, v ∈ space i e m → representation i g v ∈ space i e m := by
  induction g using FreeGroup.induction_on with
  | C1 => intro v hv; simpa using hv
  | of j => intro v hv; exact generator_mem i e he ht m j hv
  | inv_of j ih =>
    let f : space i e m → space i e m := fun v => ⟨_, ih v v.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact (Representation.apply_bijective (representation i) (FreeGroup.of j)).1
        (congrArg Subtype.val h)
    intro v hv
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
    have hw' : representation i (FreeGroup.of j) w = v := congrArg Subtype.val hw
    rw [← hw', Representation.inv_self_apply]
    exact w.property
  | mul g h hg hh =>
    intro v hv
    exact (by simpa only [map_mul, Module.End.mul_apply] using hg _ (hh v hv))

def stage (m : ℕ) : Subrepresentation (representation i) where
  toSubmodule := space i e m
  apply_mem_toSubmodule g _ hv := word_mem i e he ht m g _ hv

theorem stage_zero : stage i e he ht 0 = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · intro v hv
    change v = 0
    apply e.injective
    ext x
    simpa using hv x (by rw [cut_zero]; omega)
  · exact bot_le

theorem stage_last : stage i e he ht (length i) = ⊤ := by
  apply top_unique
  intro v _ x hx
  rw [cut_last] at hx
  omega

theorem stage_mono (m : ℕ) (hm : m < length i) :
    stage i e he ht m ≤ stage i e he ht (m + 1) := by
  intro v hv x hx
  exact hv x (le_trans (cut_step i ⟨m, hm⟩).1.le hx)

def projection (t : Factor i) :
    (stage i e he ht (t.val + 1)).toSubmodule →ₗ[ZMod 2]
      (Fin (degree i t) → ZMod 2) where
  toFun v x := e v.val (blockIndex i t x)
  map_add' v w := by ext x; simp
  map_smul' a v := by ext x; simp

theorem projection_surjective (t : Factor i) :
    Function.Surjective (projection i e he ht t) := by
  intro v
  let w : Fin 63 → ZMod 2 := fun x =>
    if h : cut i t.val ≤ x.val ∧ x.val < cut i (t.val + 1) then
      v ⟨x.val - cut i t.val, by dsimp [degree]; omega⟩ else 0
  have hw : e.symm w ∈ space i e (t.val + 1) := by
    intro x hx
    simp only [e.apply_symm_apply]
    dsimp [w]
    rw [dif_neg (by omega)]
  refine ⟨⟨e.symm w, hw⟩, ?_⟩
  ext x
  change e (e.symm w) (blockIndex i t x) = v x
  rw [e.apply_symm_apply]
  dsimp [w]
  have hx := x.isLt
  dsimp [degree] at hx
  rw [dif_pos (by dsimp [blockIndex]; constructor <;> omega)]
  congr 1
  apply Fin.ext
  simp [blockIndex]

theorem projection_kernel (t : Factor i) :
    LinearMap.ker (projection i e he ht t) =
      (within (stage i e he ht t.val) (stage i e he ht (t.val + 1))).toSubmodule := by
  ext v
  constructor
  · intro hv
    change ∀ x : Fin 63, cut i t.val ≤ x.val → e v.val x = 0
    intro x hx
    by_cases hx' : x.val < cut i (t.val + 1)
    · let y : Fin (degree i t) := ⟨x.val - cut i t.val, by dsimp [degree]; omega⟩
      have hy : blockIndex i t y = x := by apply Fin.ext; dsimp [blockIndex, y]; omega
      have h := congrFun (LinearMap.mem_ker.mp hv) y
      change e v.val (blockIndex i t y) = 0 at h
      rwa [hy] at h
    · exact v.property x (by omega)
  · intro hv
    apply LinearMap.mem_ker.mpr
    ext x
    exact hv (blockIndex i t x) (by dsimp [blockIndex]; omega)

noncomputable def coordinates (t : Factor i) :
    ((stage i e he ht (t.val + 1)).toSubmodule ⧸
      (within (stage i e he ht t.val) (stage i e he ht (t.val + 1))).toSubmodule)
      ≃ₗ[ZMod 2] (Fin (degree i t) → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ (projection_kernel i e he ht t).symm).trans
    ((projection i e he ht t).quotKerEquivOfSurjective (projection_surjective i e he ht t))

theorem coordinates_mk (t : Factor i) (v : (stage i e he ht (t.val + 1)).toSubmodule) :
    coordinates i e he ht t (Submodule.Quotient.mk v) = projection i e he ht t v := by
  simp [coordinates]

theorem projection_generator (t : Factor i) (j : Fin 2)
    (v : (stage i e he ht (t.val + 1)).toSubmodule) :
    projection i e he ht t ((stage i e he ht (t.val + 1)).toRepresentation
      (FreeGroup.of j) v) =
    (factorMatrix i t j).mulVec (projection i e he ht t v) := by
  ext x
  change e (representation i (FreeGroup.of j) v.val) (blockIndex i t x) = _
  rw [he]
  change (∑ y : Fin 63, actionMatrix i j (blockIndex i t x) y * e v.val y) =
    ∑ y : Fin (degree i t), actionMatrix i j (blockIndex i t x) (blockIndex i t y) *
      e v.val (blockIndex i t y)
  have hinj : Function.Injective (blockIndex i t) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    dsimp [blockIndex] at h
    omega
  rw [← Finset.sum_image (f := fun y : Fin 63 =>
    actionMatrix i j (blockIndex i t x) y * e v.val y) hinj.injOn]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  by_cases hlo : y.val < cut i t.val
  · rw [ht t.val j _ y (by dsimp [blockIndex]; omega) hlo, zero_mul]
  · have hhi : cut i (t.val + 1) ≤ y.val := by
      by_contra h
      have hy' : y ∈ Finset.image (blockIndex i t) Finset.univ := by
        apply Finset.mem_image.mpr
        refine ⟨⟨y.val - cut i t.val, ?_⟩, Finset.mem_univ _, ?_⟩
        · dsimp [degree]; omega
        · apply Fin.ext; dsimp [blockIndex]; omega
      exact hy hy'
    rw [v.property y hhi, mul_zero]

theorem coordinates_generator (t : Factor i) (j : Fin 2) v :
    coordinates i e he ht t
      ((within (stage i e he ht t.val) (stage i e he ht (t.val + 1))).quotientRepresentation
        (FreeGroup.of j) v) =
      (factorMatrix i t j).mulVec (coordinates i e he ht t v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [show Submodule.Quotient.mk v =
      (within (stage i e he ht t.val) (stage i e he ht (t.val + 1))).toSubmodule.mkQ v from rfl,
      Subrepresentation.quotientRepresentation_mk]
    exact (coordinates_mk i e he ht t _).trans
      ((projection_generator i e he ht t j v).trans
        (congrArg (factorMatrix i t j).mulVec (coordinates_mk i e he ht t v).symm))

noncomputable def flagCoordinates : FlagCoordinates i where
  stage := stage i e he ht
  zero := stage_zero i e he ht
  last := stage_last i e he ht
  mono := stage_mono i e he ht
  coordinates := coordinates i e he ht
  generator_coordinates := coordinates_generator i e he ht

end G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.AdaptedFlag
