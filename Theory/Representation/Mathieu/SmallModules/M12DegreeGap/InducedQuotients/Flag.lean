module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.FlagInterface
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.MatrixChecks
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.Flag.Generation

/-!
# The invariant flag in the native M₁₂ induced-heart model

Pull the coordinate prefixes at 0, 10, 54, 55, 65, 109, 110 and 120 back
through the tensor coordinates and the checked adapted basis. The triangular
matrix equations give invariance under both native actors. Their generation
of M₁₂, together with injectivity on each finite subspace for inverses, gives
invariance under every native group element.

Each block projection is onto and has precisely the preceding stage as its
kernel. The resulting first-isomorphism equivalence identifies the literal
successive quotient action with the saved diagonal block, retaining the
extension blocks of the original action. Matrix density remains an explicit,
independent premise of the application to `filtration_of_flagCoordinates`.

The quotient construction adapts the M₂₂ Hermitian filtration's `Flag.lean`.
Source context: James, J. Algebra 27 (1973), 57–111; the ordinary degree input
in Aschbacher–Smith Chapter K, printed pp.451 and 457.
-/

noncomputable section
open Sporadic.Mathieu
namespace Representation.MathieuSmall.M12DegreeGap.InducedQuotients
open M12Recognition M12Recognition.PointExtension CertificateData
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Flag

-- Name the inherited ambient instances before forming the nested quotients.
-- This avoids constrained instance search through the heart's own quotient.
local instance : AddCommGroup TensorSpace := inferInstance
local instance : Module (ZMod 2) TensorSpace := inferInstance

variable (e : TensorSpace ≃ₗ[ZMod 2] (Fin 120 → ZMod 2))

private def space (m : ℕ) : Submodule (ZMod 2) TensorSpace where
  carrier := {v | ∀ x : Fin 120, cut m ≤ x.val → e v x = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw x hx; simp [hv x hx, hw x hx]
  smul_mem' := by intro a v hv x hx; simp [hv x hx]

variable (he : ∀ j v, e (tensorAction (actor j) v) =
  (actionMatrix j).mulVec (e v))
  (ht : ∀ m j (x y : Fin 120), cut m ≤ x.val → y.val < cut m →
    actionMatrix j x y = 0)

include he ht

private theorem generator_mem (m : ℕ) (j : Fin 2) {v : TensorSpace} (hv : v ∈ space e m) :
    tensorAction (actor j) v ∈ space e m := by
  intro x hx
  rw [he]
  change (∑ y : Fin 120, actionMatrix j x y * e v y) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y.val < cut m
  · rw [ht m j x y hx hy, zero_mul]
  · rw [hv y (by omega), mul_zero]

private theorem action_mem (m : ℕ) (g : M12) :
    ∀ v, v ∈ space e m → tensorAction g v ∈ space e m := by
  let : Finite TensorSpace := Finite.of_injective e e.injective
  have hg : g ∈ Subgroup.closure (Set.range actor) := by
    rw [actors_closure_eq_top]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, rfl⟩ := hg
    exact fun v hv => generator_mem e he ht m j hv
  | one => intro v hv; simpa using hv
  | inv g _ ih =>
    let f : space e m → space e m := fun v => ⟨_, ih v v.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact (Representation.apply_bijective tensorAction g).1
        (congrArg Subtype.val h)
    intro v hv
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
    have hw' : tensorAction g w = v := congrArg Subtype.val hw
    rw [← hw', Representation.inv_self_apply]
    exact w.property
  | mul g h _ _ hg hh =>
    intro v hv
    exact (by simpa only [map_mul, Module.End.mul_apply] using hg _ (hh v hv))

private def stage (m : ℕ) : Subrepresentation tensorAction where
  toSubmodule := space e m
  apply_mem_toSubmodule g _ hv := action_mem e he ht m g _ hv

private theorem stage_zero : stage e he ht 0 = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · intro v hv
    change v = 0
    apply e.injective
    ext x
    simpa using hv x (by rw [cut_zero]; omega)
  · exact bot_le

private theorem stage_last : stage e he ht 7 = ⊤ := by
  apply top_unique
  intro v _ x hx
  rw [cut_last] at hx
  omega

private theorem stage_mono (m : ℕ) (hm : m < 7) :
    stage e he ht m ≤ stage e he ht (m + 1) := by
  intro v hv x hx
  exact hv x (le_trans (cut_step ⟨m, hm⟩).1.le hx)

private def projection (t : Factor) :
    (stage e he ht (t.val + 1)).toSubmodule →ₗ[ZMod 2]
      (Fin (degree t) → ZMod 2) where
  toFun v x := e v.val (blockIndex t x)
  map_add' v w := by ext x; simp
  map_smul' a v := by ext x; simp

private theorem projection_surjective (t : Factor) :
    Function.Surjective (projection e he ht t) := by
  intro v
  let w : Fin 120 → ZMod 2 := fun x =>
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

private theorem projection_kernel (t : Factor) :
    LinearMap.ker (projection e he ht t) =
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule := by
  ext v
  constructor
  · intro hv
    change ∀ x : Fin 120, cut t.val ≤ x.val → e v.val x = 0
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

private def coordinates (t : Factor) :
    ((stage e he ht (t.val + 1)).toSubmodule ⧸
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule)
      ≃ₗ[ZMod 2] (Fin (degree t) → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ (projection_kernel e he ht t).symm).trans
    ((projection e he ht t).quotKerEquivOfSurjective (projection_surjective e he ht t))

private theorem coordinates_mk (t : Factor) (v : (stage e he ht (t.val + 1)).toSubmodule) :
    coordinates e he ht t (Submodule.Quotient.mk v) = projection e he ht t v := by
  simp [coordinates]

private theorem projection_generator (t : Factor) (j : Fin 2)
    (v : (stage e he ht (t.val + 1)).toSubmodule) :
    projection e he ht t ((stage e he ht (t.val + 1)).toRepresentation
      (actor j) v) =
    (factorMatrix t j).mulVec (projection e he ht t v) := by
  ext x
  change e (tensorAction (actor j) v.val) (blockIndex t x) = _
  rw [he]
  change (∑ y : Fin 120, actionMatrix j (blockIndex t x) y * e v.val y) =
    ∑ y : Fin (degree t), actionMatrix j (blockIndex t x) (blockIndex t y) *
      e v.val (blockIndex t y)
  have hinj : Function.Injective (blockIndex t) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    dsimp [blockIndex] at h
    omega
  rw [← Finset.sum_image (f := fun y : Fin 120 =>
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

private theorem coordinates_generator (t : Factor) (j : Fin 2) v :
    coordinates e he ht t
      ((within (stage e he ht t.val) (stage e he ht (t.val + 1))).quotientRepresentation
        (actor j) v) =
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
private def flagCoordinates : FlagCoordinates where
  stage := stage e he ht
  zero := stage_zero e he ht
  last := stage_last e he ht
  mono := stage_mono e he ht
  coordinates := coordinates e he ht
  generator_coordinates := coordinates_generator e he ht

end Flag

/-- The seven-stage invariant flag on the literal native tensor action. -/
public def nativeFlag : FlagCoordinates :=
  Flag.flagCoordinates (tensorCoordinates.trans MatrixChecks.basisCoordinates)
    (fun j v => by
      change MatrixChecks.basisCoordinates (tensorCoordinates (tensorAction (actor j) v)) = _
      rw [tensorCoordinates_generator, MatrixChecks.basisCoordinates_generator]
      rfl)
    MatrixChecks.upper

/-- The stages are exactly the pulled-back coordinate prefix spaces. -/
public theorem mem_nativeFlag_stage (m : ℕ) (v : TensorSpace) :
    v ∈ nativeFlag.stage m ↔ ∀ x : Fin 120, cut m ≤ x.val →
      MatrixChecks.basisCoordinates (tensorCoordinates v) x = 0 := Iff.rfl

/-- Density of the seven diagonal blocks makes this native flag a simple-factor filtration. -/
public theorem filtration_of_density
    (hspan : ∀ (t : Factor)
      (Q : Subalgebra (ZMod 2) (Matrix (Fin (degree t)) (Fin (degree t)) (ZMod 2))),
      (∀ j, factorMatrix t j ∈ Q) → Q = ⊤) :
    FactorDegreeFiltration ({1, 10, 44} : Set ℕ) tensorAction :=
  filtration_of_flagCoordinates nativeFlag hspan

end Representation.MathieuSmall.M12DegreeGap.InducedQuotients
