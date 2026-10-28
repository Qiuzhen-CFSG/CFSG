module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.Model

/-!
# Invariant subspaces and literal quotients of the native M₁₁ coset module

Initial segments in an adapted basis give the 33 stages. The actual native
A and B generate M₁₁ as a monoid, so their upper block triangular matrices
make every stage invariant. Projection to a successive block is surjective
with kernel the preceding stage inside the next one. The first isomorphism
theorem gives the requested quotient coordinates and their generator equations.

This specializes the proved construction in G2DerivedPermutationFiltration's
`AdaptedFlag.Construction`, retaining the actual coset representation.
Source: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
open Sporadic.Mathieu
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.Construction
open Data CosetFlag

theorem generators_monoid_closure :
    Submonoid.closure (Set.range generator) = ⊤ := by
  have hr : Set.range generator = {m11GeneratorAInM11, m11GeneratorBInM11} := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      fin_cases s <;> simp [generator]
    · intro hg
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · exact ⟨0, by simp [generator]⟩
      · obtain rfl := Set.mem_singleton_iff.mp hg
        exact ⟨1, by simp [generator]⟩
  rw [hr, ← Subgroup.closure_toSubmonoid_of_finite, m11_generators_closure_eq_top]
  rfl

variable (e : (ElevenCoset → ZMod 2) ≃ₗ[ZMod 2] Space)

def space (m : ℕ) : Submodule (ZMod 2) (ElevenCoset → ZMod 2) where
  carrier := {v | ∀ x : Fin 720, cut m ≤ x.val → e v x = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw x hx; simp [hv x hx, hw x hx]
  smul_mem' := by intro a v hv x hx; simp [hv x hx]

variable (he : ∀ j v, e (cosetRepresentation (generator j) v) =
  (actionMatrix j).mulVec (e v))
  (ht : ∀ m j (x y : Fin 720), cut m ≤ x.val → y.val < cut m →
    actionMatrix j x y = 0)

include he ht

theorem generator_mem (m : ℕ) (j : Fin 2) {v : ElevenCoset → ZMod 2} (hv : v ∈ space e m) :
    cosetRepresentation (generator j) v ∈ space e m := by
  intro x hx
  rw [he]
  change (∑ y : Fin 720, actionMatrix j x y * e v y) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y.val < cut m
  · rw [ht m j x y hx hy, zero_mul]
  · rw [hv y (by omega), mul_zero]

theorem word_mem (m : ℕ) (g : M11) :
    ∀ v, v ∈ space e m → cosetRepresentation g v ∈ space e m := by
  apply Submonoid.induction_of_closure_eq_top_left
    (motive := fun g => ∀ v, v ∈ space e m → cosetRepresentation g v ∈ space e m)
    generators_monoid_closure g
  · intro v hv
    simpa only [map_one, Module.End.one_apply] using hv
  · rintro _ ⟨s, rfl⟩ h ih v hv
    simpa only [map_mul, Module.End.mul_apply] using
      generator_mem e he ht m s (ih v hv)

def stage (m : ℕ) : Subrepresentation (cosetRepresentation) where
  toSubmodule := space e m
  apply_mem_toSubmodule g _ hv := word_mem e he ht m g _ hv

theorem stage_zero : stage e he ht 0 = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · intro v hv
    change v = 0
    apply e.injective
    ext x
    simpa using hv x (by rw [cut_zero]; omega)
  · exact bot_le

theorem stage_last : stage e he ht 33 = ⊤ := by
  apply top_unique
  intro v _ x hx
  rw [cut_last] at hx
  omega

theorem stage_mono (m : ℕ) (hm : m < 33) :
    stage e he ht m ≤ stage e he ht (m + 1) := by
  intro v hv x hx
  have hstep := (cut_step ⟨m, hm⟩).1
  change cut m + degree ⟨m, hm⟩ = cut (m + 1) at hstep
  exact hv x (by omega)

def projection (t : Factor) :
    (stage e he ht (t.val + 1)).toSubmodule →ₗ[ZMod 2]
      (Fin (degree t) → ZMod 2) where
  toFun v x := e v.val (blockIndex t x)
  map_add' v w := by ext x; simp
  map_smul' a v := by ext x; simp

theorem projection_surjective (t : Factor) :
    Function.Surjective (projection e he ht t) := by
  intro v
  let w : Fin 720 → ZMod 2 := fun x =>
    if h : cut t.val ≤ x.val ∧ x.val < cut (t.val + 1) then
      v ⟨x.val - cut t.val, by have hstep := (cut_step t).1; omega⟩ else 0
  have hw : e.symm w ∈ space e (t.val + 1) := by
    intro x hx
    simp only [e.apply_symm_apply]
    dsimp [w]
    rw [dif_neg (by omega)]
  refine ⟨⟨e.symm w, hw⟩, ?_⟩
  ext x
  change e (e.symm w) (blockIndex t x) = v x
  rw [e.apply_symm_apply]
  dsimp [w]
  have hx := x.isLt
  have hstep := (cut_step t).1
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
    change ∀ x : Fin 720, cut t.val ≤ x.val → e v.val x = 0
    intro x hx
    by_cases hx' : x.val < cut (t.val + 1)
    · let y : Fin (degree t) := ⟨x.val - cut t.val, by have hstep := (cut_step t).1; omega⟩
      have hy : blockIndex t y = x := by apply Fin.ext; dsimp [blockIndex, y]; omega
      have h := congrFun (LinearMap.mem_ker.mp hv) y
      change e v.val (blockIndex t y) = 0 at h
      rwa [hy] at h
    · exact v.property x (by omega)
  · intro hv
    apply LinearMap.mem_ker.mpr
    ext x
    exact hv (blockIndex t x) (by dsimp [blockIndex]; omega)

noncomputable def coordinates (t : Factor) :
    ((stage e he ht (t.val + 1)).toSubmodule ⧸
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule)
      ≃ₗ[ZMod 2] (Fin (degree t) → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ (projection_kernel e he ht t).symm).trans
    ((projection e he ht t).quotKerEquivOfSurjective (projection_surjective e he ht t))

theorem coordinates_mk (t : Factor) (v : (stage e he ht (t.val + 1)).toSubmodule) :
    coordinates e he ht t (Submodule.Quotient.mk v) = projection e he ht t v := by
  simp [coordinates]

variable (hd : ∀ (t : Factor) (s : Fin 2) (x y : Fin (degree t)),
  actionMatrix s (blockIndex t x) (blockIndex t y) = factorMatrix t s x y)

include hd

theorem projection_generator (t : Factor) (j : Fin 2)
    (v : (stage e he ht (t.val + 1)).toSubmodule) :
    projection e he ht t ((stage e he ht (t.val + 1)).toRepresentation
      (generator j) v) =
    (factorMatrix t j).mulVec (projection e he ht t v) := by
  ext x
  change e (cosetRepresentation (generator j) v.val) (blockIndex t x) = _
  rw [he]
  change (∑ y : Fin 720, actionMatrix j (blockIndex t x) y * e v.val y) =
    ∑ y : Fin (degree t), factorMatrix t j x y * e v.val (blockIndex t y)
  simp only [← hd]
  change (∑ y : Fin 720, actionMatrix j (blockIndex t x) y * e v.val y) =
    ∑ y : Fin (degree t), actionMatrix j (blockIndex t x) (blockIndex t y) *
      e v.val (blockIndex t y)
  have hinj : Function.Injective (blockIndex t) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    dsimp [blockIndex] at h
    omega
  rw [← Finset.sum_image (f := fun y : Fin 720 =>
    actionMatrix j (blockIndex t x) y * e v.val y) hinj.injOn]
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
        · have hstep := (cut_step t).1; omega
        · apply Fin.ext; dsimp [blockIndex]; omega
      exact hy hy'
    rw [v.property y hhi, mul_zero]

theorem coordinates_generator (t : Factor) (j : Fin 2) v :
    coordinates e he ht t
      ((within (stage e he ht t.val) (stage e he ht (t.val + 1))).quotientRepresentation
        (generator j) v) =
      (factorMatrix t j).mulVec (coordinates e he ht t v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [show Submodule.Quotient.mk v =
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule.mkQ v from rfl,
      Subrepresentation.quotientRepresentation_mk]
    exact (coordinates_mk e he ht t _).trans
      ((projection_generator e he ht hd t j v).trans
        (congrArg (factorMatrix t j).mulVec (coordinates_mk e he ht t v).symm))

noncomputable def flagCoordinates : FlagCoordinates where
  stage := stage e he ht
  zero := stage_zero e he ht
  last := stage_last e he ht
  mono := stage_mono e he ht
  coordinates := coordinates e he ht
  generator_coordinates := coordinates_generator e he ht hd

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.Construction
