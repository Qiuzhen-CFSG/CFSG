module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.CertificateInterface

/-!
# Quotient coordinates from adapted native adjoint coordinates

Initial coordinate spaces of an upper triangular action give actual native
M22 subrepresentations. The projection onto each next block is surjective,
and its kernel is exactly `within` the preceding stage. The first isomorphism
theorem therefore supplies coordinates for the literal successive quotient,
with precisely the saved diagonal-block generator action.

The adapted coordinate identity is an explicit input here; `NativeFlag`
discharges it by comparing the saved columns with the native sparse action.
No splitting or simplicity is inferred. This specializes the block-projection
construction in `NineSubmodule.InducedHeads.HermitianFiltration.Flag`.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration
namespace NativeFlag
variable (e : GeneratorMatrices.BinaryCoordinates ≃ₗ[ZMod 2] Space)

def space (m : ℕ) : Submodule (ZMod 2) (GeneratorMatrices.BinaryCoordinates) where
  carrier := {v | ∀ x : Fin 352, cut m ≤ x.val → e v x = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw x hx; simp [hv x hx, hw x hx]
  smul_mem' := by intro a v hv x hx; simp [hv x hx]

variable (he : ∀ j v, e (GeneratorMatrices.binaryAdjoint (GeneratorMatrices.generator j) v) =
  (actionMatrix j).mulVec (e v))
  (ht : ∀ m j (x y : Fin 352), cut m ≤ x.val → y.val < cut m →
    actionMatrix j x y = 0)

include he ht

theorem generator_mem (m : ℕ) (j : Fin 2) {v : GeneratorMatrices.BinaryCoordinates} (hv : v ∈ space e m) :
    GeneratorMatrices.binaryAdjoint (GeneratorMatrices.generator j) v ∈ space e m := by
  intro x hx
  rw [he]
  change (∑ y : Fin 352, actionMatrix j x y * e v y) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y.val < cut m
  · rw [ht m j x y hx hy, zero_mul]
  · rw [hv y (by omega), mul_zero]

theorem word_mem (m : ℕ) (g : M22) :
    ∀ v, v ∈ space e m → GeneratorMatrices.binaryAdjoint g v ∈ space e m := by
  let : Finite (GeneratorMatrices.BinaryCoordinates) := Finite.of_injective e e.injective
  have hg : g ∈ Subgroup.closure
      ({m22GeneratorAInM22, m22GeneratorBInM22} : Set M22) := by
    rw [m22_generators_closure_eq_top]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact fun v hv => by simpa only [← GeneratorMatrices.generator_zero] using generator_mem e he ht m 0 hv
    · exact fun v hv => by simpa only [← GeneratorMatrices.generator_one] using generator_mem e he ht m 1 hv
  | one => intro v hv; simpa using hv
  | inv g _ ih =>
    let f : space e m → space e m := fun v => ⟨_, ih v v.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact (Representation.apply_bijective (GeneratorMatrices.binaryAdjoint) g).1
        (congrArg Subtype.val h)
    intro v hv
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
    have hw' : GeneratorMatrices.binaryAdjoint g w = v := congrArg Subtype.val hw
    rw [← hw', Representation.inv_self_apply]
    exact w.property
  | mul g h _ _ hg hh =>
    intro v hv
    exact (by simpa only [map_mul, Module.End.mul_apply] using hg _ (hh v hv))

def stage (m : ℕ) : Subrepresentation (GeneratorMatrices.binaryAdjoint) where
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

theorem stage_last : stage e he ht 8 = ⊤ := by
  apply top_unique
  intro v _ x hx
  rw [cut_last] at hx
  omega

theorem stage_mono (m : ℕ) (hm : m < 8) :
    stage e he ht m ≤ stage e he ht (m + 1) := by
  intro v hv x hx
  exact hv x (le_trans (cut_step ⟨m, hm⟩).1.le hx)

def projection (t : Factor) :
    (stage e he ht (t.val + 1)).toSubmodule →ₗ[ZMod 2]
      (Fin (degree t) → ZMod 2) where
  toFun v x := e v.val (blockIndex t x)
  map_add' v w := by ext x; simp
  map_smul' a v := by ext x; simp

theorem projection_surjective (t : Factor) :
    Function.Surjective (projection e he ht t) := by
  intro v
  let w : Fin 352 → ZMod 2 := fun x =>
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
    LinearMap.ker (projection e he ht t) =
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule := by
  ext v
  constructor
  · intro hv
    change ∀ x : Fin 352, cut t.val ≤ x.val → e v.val x = 0
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
    ((stage e he ht (t.val + 1)).toSubmodule ⧸
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule)
      ≃ₗ[ZMod 2] (Fin (degree t) → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ (projection_kernel e he ht t).symm).trans
    ((projection e he ht t).quotKerEquivOfSurjective (projection_surjective e he ht t))

theorem coordinates_mk (t : Factor) (v : (stage e he ht (t.val + 1)).toSubmodule) :
    coordinates e he ht t (Submodule.Quotient.mk v) = projection e he ht t v := by
  simp [coordinates]

theorem projection_generator (t : Factor) (j : Fin 2)
    (v : (stage e he ht (t.val + 1)).toSubmodule) :
    projection e he ht t ((stage e he ht (t.val + 1)).toRepresentation
      (GeneratorMatrices.generator j) v) =
    (factorMatrix t j).mulVec (projection e he ht t v) := by
  ext x
  change e (GeneratorMatrices.binaryAdjoint (GeneratorMatrices.generator j) v.val) (blockIndex t x) = _
  rw [he]
  change (∑ y : Fin 352, actionMatrix j (blockIndex t x) y * e v.val y) =
    ∑ y : Fin (degree t), actionMatrix j (blockIndex t x) (blockIndex t y) *
      e v.val (blockIndex t y)
  have hinj : Function.Injective (blockIndex t) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    dsimp [blockIndex] at h
    omega
  rw [← Finset.sum_image (f := fun y : Fin 352 =>
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
    coordinates e he ht t
      ((within (stage e he ht t.val) (stage e he ht (t.val + 1))).quotientRepresentation
        (GeneratorMatrices.generator j) v) =
      (factorMatrix t j).mulVec (coordinates e he ht t v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [show Submodule.Quotient.mk v =
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule.mkQ v from rfl,
      Subrepresentation.quotientRepresentation_mk]
    exact (coordinates_mk e he ht t _).trans
      ((projection_generator e he ht t j v).trans
        (congrArg (factorMatrix t j).mulVec (coordinates_mk e he ht t v).symm))


/-- Construct the actual flag from the two adapted generator equations. -/
def flagCoordinates : FlagCoordinates where
  stage := stage e he ht
  zero := stage_zero e he ht
  last := stage_last e he ht
  mono := stage_mono e he ht
  coordinates := coordinates e he ht
  generator_coordinates := coordinates_generator e he ht

end NativeFlag
end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration
