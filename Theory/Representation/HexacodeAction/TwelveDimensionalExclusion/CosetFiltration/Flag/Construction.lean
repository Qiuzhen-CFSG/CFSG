module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Interface

/-!
# Prefix subspaces and literal quotient coordinates over F₄

An adapted linear equivalence carries initial coordinate segments to invariant
subspaces. Generator invariance extends to inverse generators by finiteness,
and then to every word. Projection onto each successive block is surjective
and has kernel equal to the preceding stage, giving coordinates on the literal
quotient by the first isomorphism theorem.

This adapts the construction in `CoordinateFiltrations.AdaptedFlag.Construction`
to the central coset module for Aschbacher–Smith K.1.3, printed p.453 / PDF p.464.
The matrix identities are explicit inputs here and are discharged in `Flag`.
-/

@[expose] public section

open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
open Representation

namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.Flag

variable (e : Space ≃ₗ[F] (Fin 45 → F))

def space (m : ℕ) : Submodule F Space where
  carrier := {v | ∀ x : Fin 45, cut m ≤ x.val → e v x = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw x hx; simp [hv x hx, hw x hx]
  smul_mem' := by intro a v hv x hx; simp [hv x hx]

variable (he : ∀ j v, e (representation (FreeGroup.of j) v) =
  (adaptedMatrix j).mulVec (e v))
  (ht : ∀ m j (x y : Fin 45), cut m ≤ x.val → y.val < cut m →
    adaptedMatrix j x y = 0)

include he ht

theorem generator_mem (m : ℕ) (j : Fin 2) {v : Space} (hv : v ∈ space e m) :
    representation (FreeGroup.of j) v ∈ space e m := by
  intro x hx
  rw [he]
  change (∑ y : Fin 45, adaptedMatrix j x y * e v y) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y.val < cut m
  · rw [ht m j x y hx hy, zero_mul]
  · rw [hv y (by omega), mul_zero]

theorem word_mem (m : ℕ) (g : WordGroup) :
    ∀ v, v ∈ space e m → representation g v ∈ space e m := by
  induction g using FreeGroup.induction_on with
  | C1 => intro v hv; simpa using hv
  | of j => intro v hv; exact generator_mem e he ht m j hv
  | inv_of j ih =>
    let f : space e m → space e m := fun v => ⟨_, ih v v.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact (Representation.apply_bijective representation (FreeGroup.of j)).1
        (congrArg Subtype.val h)
    intro v hv
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
    have hw' : representation (FreeGroup.of j) w = v := congrArg Subtype.val hw
    rw [← hw', Representation.inv_self_apply]
    exact w.property
  | mul g h hg hh =>
    intro v hv
    exact (by simpa only [map_mul, Module.End.mul_apply] using hg _ (hh v hv))

def stage (m : ℕ) : Subrepresentation representation where
  toSubmodule := space e m
  apply_mem_toSubmodule g _ hv := word_mem e he ht m g _ hv

theorem stage_zero : stage e he ht 0 = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · intro v hv
    change v = 0
    apply e.injective
    funext x
    simpa using hv x (by rw [cut_zero]; omega)
  · exact bot_le

theorem stage_last : stage e he ht 9 = ⊤ := by
  apply top_unique
  intro v _ x hx
  rw [cut_last] at hx
  omega

theorem stage_mono (m : ℕ) (hm : m < 9) :
    stage e he ht m ≤ stage e he ht (m + 1) := by
  intro v hv x hx
  exact hv x (le_trans (cut_step ⟨m, hm⟩).1.le hx)

def projection (t : Factor) :
    (stage e he ht (t.val + 1)).toSubmodule →ₗ[F]
      (Fin (degree t) → F) where
  toFun v x := e v.val (blockIndex t x)
  map_add' v w := by funext x; simp
  map_smul' a v := by funext x; simp

theorem projection_surjective (t : Factor) :
    Function.Surjective (projection e he ht t) := by
  intro v
  let w : Fin 45 → F := fun x =>
    if h : cut t.val ≤ x.val ∧ x.val < cut (t.val + 1) then
      v ⟨x.val - cut t.val, by dsimp [degree]; omega⟩ else 0
  have hw : e.symm w ∈ space e (t.val + 1) := by
    intro x hx
    simp only [e.apply_symm_apply]
    dsimp [w]
    rw [dif_neg (by omega)]
  refine ⟨⟨e.symm w, hw⟩, ?_⟩
  funext x
  change e (e.symm w) (blockIndex t x) = v x
  rw [e.apply_symm_apply]
  dsimp [w]
  have hx := x.isLt
  dsimp [degree] at hx
  rw [dif_pos (by dsimp [blockIndex]; constructor <;> omega)]
  congr 1
  apply Fin.ext
  simp [blockIndex]

theorem projection_kernel (t : Factor) :
    LinearMap.ker (projection e he ht t) =
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule := by
  ext v
  constructor
  · intro hv
    change ∀ x : Fin 45, cut t.val ≤ x.val → e v.val x = 0
    intro x hx
    by_cases hx' : x.val < cut (t.val + 1)
    · let y : Fin (degree t) := ⟨x.val - cut t.val, by dsimp [degree]; omega⟩
      have hy : blockIndex t y = x := by apply Fin.ext; dsimp [blockIndex, y]; omega
      have h := congrFun (LinearMap.mem_ker.mp hv) y
      change e v.val (blockIndex t y) = 0 at h
      rwa [hy] at h
    · exact v.property x (by omega)
  · intro hv
    apply LinearMap.mem_ker.mpr
    funext x
    exact hv (blockIndex t x) (by dsimp [blockIndex]; omega)

noncomputable def coordinates (t : Factor) :
    ((stage e he ht (t.val + 1)).toSubmodule ⧸
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule)
      ≃ₗ[F] (Fin (degree t) → F) :=
  (Submodule.quotEquivOfEq _ _ (projection_kernel e he ht t).symm).trans
    ((projection e he ht t).quotKerEquivOfSurjective (projection_surjective e he ht t))

theorem coordinates_mk (t : Factor) (v : (stage e he ht (t.val + 1)).toSubmodule) :
    coordinates e he ht t (Submodule.Quotient.mk v) = projection e he ht t v := by
  simp [coordinates]

theorem projection_generator (t : Factor) (j : Fin 2)
    (v : (stage e he ht (t.val + 1)).toSubmodule) :
    projection e he ht t ((stage e he ht (t.val + 1)).toRepresentation
      (FreeGroup.of j) v) =
    (factorMatrix t j).mulVec (projection e he ht t v) := by
  funext x
  change e (representation (FreeGroup.of j) v.val) (blockIndex t x) = _
  rw [he]
  change (∑ y : Fin 45, adaptedMatrix j (blockIndex t x) y * e v.val y) =
    ∑ y : Fin (degree t), adaptedMatrix j (blockIndex t x) (blockIndex t y) *
      e v.val (blockIndex t y)
  have hinj : Function.Injective (blockIndex t) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    dsimp [blockIndex] at h
    omega
  rw [← Finset.sum_image (f := fun y : Fin 45 =>
    adaptedMatrix j (blockIndex t x) y * e v.val y) hinj.injOn]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  by_cases hlo : y.val < cut t.val
  · rw [ht t.val j _ y (by dsimp [blockIndex]; omega) hlo, zero_mul]
  · have hhi : cut (t.val + 1) ≤ y.val := by
      by_contra h
      have hy' : y ∈ Finset.image (blockIndex t) Finset.univ := by
        apply Finset.mem_image.mpr
        refine ⟨⟨y.val - cut t.val, ?_⟩, Finset.mem_univ _, ?_⟩
        · dsimp [degree]; omega
        · apply Fin.ext; dsimp [blockIndex]; omega
      exact hy hy'
    rw [v.property y hhi, mul_zero]

theorem coordinates_generator (t : Factor) (j : Fin 2) v :
    coordinates e he ht t
      ((within (stage e he ht t.val) (stage e he ht (t.val + 1))).quotientRepresentation
        (FreeGroup.of j) v) =
      (factorMatrix t j).mulVec (coordinates e he ht t v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [show Submodule.Quotient.mk v =
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule.mkQ v from rfl,
      Subrepresentation.quotientRepresentation_mk]
    exact (coordinates_mk e he ht t _).trans
      ((projection_generator e he ht t j v).trans
        (congrArg (factorMatrix t j).mulVec (coordinates_mk e he ht t v).symm))

noncomputable def flagCoordinates : FlagCoordinates where
  stage := stage e he ht
  zero := stage_zero e he ht
  last := stage_last e he ht
  mono := stage_mono e he ht
  coordinates := coordinates e he ht
  generator_coordinates := coordinates_generator e he ht

end Representation.Hexacode.TwelveDimensional.CosetCertificate.Flag
