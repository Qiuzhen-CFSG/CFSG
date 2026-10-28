module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeModel
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.MatrixChecks
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools

/-!
# Literal successive quotients of the M23 cocode flag

An adapted linear equivalence pulls back the coordinate flag. The checked
upper triangular blocks preserve it, and generation extends invariance to
all of M23. Projection onto a diagonal block has precisely the preceding
stage as kernel, giving coordinates on the literal quotient action.

This construction retains the native generator comparison and generation
as explicit premises. It does not assert irreducibility or the requested
unconditional filtration. The source application is Guralnick--Malle I,
Proposition 5.1, M23 paragraph. The flag proof is adapted from the project's
M23 HermitianFiltration/Flag.lean, preserving the off-diagonal blocks.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration

/-- Invariant stages and coordinates on their literal successive quotients.
No irreducibility assertion is included in this intermediate witness. -/
structure FlagCoordinates where
  stage : ℕ → Subrepresentation canonicalCocodeAction
  zero : stage 0 = ⊥
  last : stage 5 = ⊤
  mono : ∀ m, m < 5 → stage m ≤ stage (m + 1)
  coordinates (t : Factor) :
    ((stage (t.val + 1)).toSubmodule ⧸
      (within (stage t.val) (stage (t.val + 1))).toSubmodule) ≃ₗ[ZMod 2]
      (Fin (degree t) → ZMod 2)
  generator_coordinates : ∀ (t : Factor) (j : Fin 2) v,
    coordinates t
      ((within (stage t.val) (stage (t.val + 1))).quotientRepresentation (actor j) v) =
    (factorMatrix t j).mulVec (coordinates t v)

namespace Flag
variable (e : (Coordinates.Space false) ≃ₗ[ZMod 2] (Fin 230 → ZMod 2))

def space (m : ℕ) : Submodule (ZMod 2) (Coordinates.Space false) where
  carrier := {v | ∀ x : Fin 230, cut m ≤ x.val → e v x = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw x hx; simp [hv x hx, hw x hx]
  smul_mem' := by intro a v hv x hx; simp [hv x hx]

variable (he : ∀ j v, e (canonicalCocodeAction (actor j) v) =
  (actionMatrix j).mulVec (e v))
  (ht : ∀ m j (x y : Fin 230), cut m ≤ x.val → y.val < cut m →
    actionMatrix j x y = 0)

variable (hgeneration : Subgroup.closure
  ({m23GeneratorAInM23, m23GeneratorBInM23} : Set M23) = ⊤)

include he ht

theorem generator_mem (m : ℕ) (j : Fin 2) {v : (Coordinates.Space false)} (hv : v ∈ space e m) :
    canonicalCocodeAction (actor j) v ∈ space e m := by
  intro x hx
  rw [he]
  change (∑ y : Fin 230, actionMatrix j x y * e v y) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y.val < cut m
  · rw [ht m j x y hx hy, zero_mul]
  · rw [hv y (by omega), mul_zero]

include hgeneration

theorem word_mem (m : ℕ) (g : M23) :
    ∀ v, v ∈ space e m → canonicalCocodeAction g v ∈ space e m := by
  let : Finite (Coordinates.Space false) := Finite.of_injective e e.injective
  have hg : g ∈ Subgroup.closure
      ({m23GeneratorAInM23, m23GeneratorBInM23} : Set M23) := by
    rw [hgeneration]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact fun v hv => generator_mem e he ht m 0 hv
    · exact fun v hv => generator_mem e he ht m 1 hv
  | one => intro v hv; simpa using hv
  | inv g _ ih =>
    let f : space e m → space e m := fun v => ⟨_, ih v v.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact (Representation.apply_bijective canonicalCocodeAction g).1
        (congrArg Subtype.val h)
    intro v hv
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
    have hw' : canonicalCocodeAction g w = v := congrArg Subtype.val hw
    rw [← hw', Representation.inv_self_apply]
    exact w.property
  | mul g h _ _ hg hh =>
    intro v hv
    exact (by simpa only [map_mul, Module.End.mul_apply] using hg _ (hh v hv))

def stage (m : ℕ) : Subrepresentation canonicalCocodeAction where
  toSubmodule := space e m
  apply_mem_toSubmodule g _ hv := word_mem e he ht hgeneration m g _ hv

theorem stage_zero : stage e he ht hgeneration 0 = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · intro v hv
    change v = 0
    apply e.injective
    ext x
    simpa using hv x (by rw [cut_zero]; omega)
  · exact bot_le

theorem stage_last : stage e he ht hgeneration 5 = ⊤ := by
  apply top_unique
  intro v _ x hx
  rw [cut_last] at hx
  omega

theorem stage_mono (m : ℕ) (hm : m < 5) :
    stage e he ht hgeneration m ≤ stage e he ht hgeneration (m + 1) := by
  intro v hv x hx
  exact hv x (le_trans (cut_step ⟨m, hm⟩).1.le hx)

def projection (t : Factor) :
    (stage e he ht hgeneration (t.val + 1)).toSubmodule →ₗ[ZMod 2]
      (Fin (degree t) → ZMod 2) where
  toFun v x := e v.val (blockIndex t x)
  map_add' v w := by ext x; simp
  map_smul' a v := by ext x; simp

theorem projection_surjective (t : Factor) :
    Function.Surjective (projection e he ht hgeneration t) := by
  intro v
  let w : Fin 230 → ZMod 2 := fun x =>
    if h : cut t.val ≤ x.val ∧ x.val < cut (t.val + 1) then
      v ⟨x.val - cut t.val, by dsimp [degree]; omega⟩ else 0
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
  dsimp [degree] at hx
  rw [dif_pos (by dsimp [blockIndex]; constructor <;> omega)]
  congr 1
  apply Fin.ext
  simp [blockIndex]

theorem projection_kernel (t : Factor) :
    LinearMap.ker (projection e he ht hgeneration t) =
      (within (stage e he ht hgeneration t.val) (stage e he ht hgeneration (t.val + 1))).toSubmodule := by
  ext v
  constructor
  · intro hv
    change ∀ x : Fin 230, cut t.val ≤ x.val → e v.val x = 0
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
    ext x
    exact hv (blockIndex t x) (by dsimp [blockIndex]; omega)

noncomputable def coordinates (t : Factor) :
    ((stage e he ht hgeneration (t.val + 1)).toSubmodule ⧸
      (within (stage e he ht hgeneration t.val) (stage e he ht hgeneration (t.val + 1))).toSubmodule)
      ≃ₗ[ZMod 2] (Fin (degree t) → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ (projection_kernel e he ht hgeneration t).symm).trans
    ((projection e he ht hgeneration t).quotKerEquivOfSurjective (projection_surjective e he ht hgeneration t))

theorem coordinates_mk (t : Factor) (v : (stage e he ht hgeneration (t.val + 1)).toSubmodule) :
    coordinates e he ht hgeneration t (Submodule.Quotient.mk v) = projection e he ht hgeneration t v := by
  simp [coordinates]

theorem projection_generator (t : Factor) (j : Fin 2)
    (v : (stage e he ht hgeneration (t.val + 1)).toSubmodule) :
    projection e he ht hgeneration t ((stage e he ht hgeneration (t.val + 1)).toRepresentation
      (actor j) v) =
    (factorMatrix t j).mulVec (projection e he ht hgeneration t v) := by
  ext x
  change e (canonicalCocodeAction (actor j) v.val) (blockIndex t x) = _
  rw [he]
  change (∑ y : Fin 230, actionMatrix j (blockIndex t x) y * e v.val y) =
    ∑ y : Fin (degree t), actionMatrix j (blockIndex t x) (blockIndex t y) *
      e v.val (blockIndex t y)
  have hinj : Function.Injective (blockIndex t) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    dsimp [blockIndex] at h
    omega
  rw [← Finset.sum_image (f := fun y : Fin 230 =>
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
        · dsimp [degree]; omega
        · apply Fin.ext; dsimp [blockIndex]; omega
      exact hy hy'
    rw [v.property y hhi, mul_zero]

theorem coordinates_generator (t : Factor) (j : Fin 2) v :
    coordinates e he ht hgeneration t
      ((within (stage e he ht hgeneration t.val) (stage e he ht hgeneration (t.val + 1))).quotientRepresentation
        (actor j) v) =
      (factorMatrix t j).mulVec (coordinates e he ht hgeneration t v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [show Submodule.Quotient.mk v =
      (within (stage e he ht hgeneration t.val) (stage e he ht hgeneration (t.val + 1))).toSubmodule.mkQ v from rfl,
      Subrepresentation.quotientRepresentation_mk]
    exact (coordinates_mk e he ht hgeneration t _).trans
      ((projection_generator e he ht hgeneration t j v).trans
        (congrArg (factorMatrix t j).mulVec (coordinates_mk e he ht hgeneration t v).symm))


/-- Construct the actual flag from the two adapted generator equations. -/
def flagCoordinates : FlagCoordinates where
  stage := stage e he ht hgeneration
  zero := stage_zero e he ht hgeneration
  last := stage_last e he ht hgeneration
  mono := stage_mono e he ht hgeneration
  coordinates := coordinates e he ht hgeneration
  generator_coordinates := coordinates_generator e he ht hgeneration

end Flag

/-- Adapt raw coordinates by the checked basis change, then construct the flag. -/
def flagOfGeneratorCoordinates
    (e : (Coordinates.Space false) ≃ₗ[ZMod 2] Space)
    (he : ∀ j v, e (canonicalCocodeAction (actor j) v) =
      (generatorMatrix j).mulVec (e v))
    (hgeneration : Subgroup.closure
      ({m23GeneratorAInM23, m23GeneratorBInM23} : Set M23) = ⊤) : FlagCoordinates :=
  Flag.flagCoordinates (e.trans MatrixChecks.basisCoordinates)
    (fun j v => by
      change MatrixChecks.basisCoordinates (e (canonicalCocodeAction (actor j) v)) = _
      rw [he, MatrixChecks.basisCoordinates_generator]
      rfl)
    MatrixChecks.upper hgeneration

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration
