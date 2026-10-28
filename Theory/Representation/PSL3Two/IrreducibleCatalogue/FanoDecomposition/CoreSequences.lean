module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.Basic

/-!
# The two natural-dual Fano core exact sequences

Evaluation embeds the dual natural module in the point augmentation kernel;
weighted sum maps this kernel onto the natural module. Coordinate duality gives
the second sequence for tagged lines. All action identities hold for arbitrary
SL₃(2) elements. The finite binary linear identities are checked by the kernel.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.5.3(1–2)
and the two cores in H.6.2(1), printed pp.385–387.
-/

@[expose] public section
open Matrix Representation
namespace BinaryLinearThree.FanoDecomposition

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem evaluation_sum : ∀ v : Vector, ∑ p : Point, v ⬝ᵥ p.val = 0 := by
  decide +kernel

/-- Evaluation in covector coordinates, used to certify the core maps. -/
def coordinateEvaluation : Vector →ₗ[ZMod 2] Core where
  toFun v := ⟨fun p => v ⬝ᵥ p.val, by exact evaluation_sum v⟩
  map_add' v w := by
    apply Subtype.ext
    funext p
    exact add_dotProduct v w p.val
  map_smul' c v := by
    apply Subtype.ext
    funext p
    exact smul_dotProduct c v p.val

/-- The literal sum of point vectors with the given coefficients. -/
def coordinateSum : Core →ₗ[ZMod 2] Vector where
  toFun a := ∑ p : Point, a.val p • p.val
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_smul, Finset.smul_sum]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem evaluation_injective_certificate :
    ∀ v w : Vector, (∀ p : Point, v ⬝ᵥ p.val = w ⬝ᵥ p.val) → v = w := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem sum_surjective_certificate : ∀ v : Vector,
    ∃ a : Point → ZMod 2, (∑ p, a p) = 0 ∧ (∑ p, a p • p.val) = v := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
private theorem exact_certificate : ∀ a : Point → ZMod 2, (∑ p, a p) = 0 →
    ((∑ p, a p • p.val) = 0 ↔ ∃ v : Vector, ∀ p : Point, v ⬝ᵥ p.val = a p) := by
  decide +kernel

theorem coordinateEvaluation_injective : Function.Injective coordinateEvaluation := by
  intro v w h
  apply evaluation_injective_certificate v w
  intro p
  exact congrArg (fun a : Core => a.val p) h

theorem coordinateSum_surjective : Function.Surjective coordinateSum := by
  intro v
  obtain ⟨a, ha, hv⟩ := sum_surjective_certificate v
  exact ⟨⟨a, ha⟩, hv⟩

theorem coordinate_exact (a : Core) :
    coordinateSum a = 0 ↔ ∃ v : Vector, coordinateEvaluation v = a := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (exact_certificate a.val a.property).mp h
    exact ⟨v, Subtype.ext (funext hv)⟩
  · rintro ⟨v, rfl⟩
    exact (exact_certificate (coordinateEvaluation v).val
      (coordinateEvaluation v).property).mpr ⟨v, fun _ => rfl⟩

/-- The actual dual embeds in the point core by evaluation. -/
def pointEvaluation : Representation.IntertwiningMap W.dual U₂ where
  toLinearMap := coordinateEvaluation.comp (dotProductEquiv (ZMod 2) (Fin 3)).symm.toLinearMap
  isIntertwining' g := by
    ext φ p
    change dotProductEquiv (ZMod 2) (Fin 3)
        ((dotProductEquiv (ZMod 2) (Fin 3)).symm (W.dual g φ)) p.val =
      dotProductEquiv (ZMod 2) (Fin 3)
        ((dotProductEquiv (ZMod 2) (Fin 3)).symm φ) (g⁻¹ • p.val)
    simp only [LinearEquiv.apply_symm_apply]
    rfl

@[simp] theorem pointEvaluation_apply (φ : Dual) (p : Point) :
    (pointEvaluation φ).val p = φ p.val := by
  change dotProductEquiv (ZMod 2) (Fin 3)
      ((dotProductEquiv (ZMod 2) (Fin 3)).symm φ) p.val = _
  rw [LinearEquiv.apply_symm_apply]

/-- The point core maps to the actual natural representation by weighted sum. -/
def pointWeightedSum : Representation.IntertwiningMap U₂ W where
  toLinearMap := coordinateSum
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    change (∑ p : Point, a.val ((pointPerm g).symm p) • p.val) =
      W g (∑ p : Point, a.val p • p.val)
    rw [← Equiv.sum_comp (pointPerm g) (fun p : Point =>
      a.val ((pointPerm g).symm p) • p.val)]
    simp only [Equiv.symm_apply_apply, map_sum, map_smul]
    rfl

@[simp] theorem pointWeightedSum_apply (a : Core) :
    pointWeightedSum a = ∑ p : Point, a.val p • p.val := rfl

theorem pointEvaluation_injective : Function.Injective pointEvaluation :=
  coordinateEvaluation_injective.comp (dotProductEquiv (ZMod 2) (Fin 3)).symm.injective

theorem pointWeightedSum_surjective : Function.Surjective pointWeightedSum :=
  coordinateSum_surjective

theorem point_exact : LinearMap.range pointEvaluation.toLinearMap =
    LinearMap.ker pointWeightedSum.toLinearMap := by
  ext a
  constructor
  · rintro ⟨φ, rfl⟩
    exact (coordinate_exact _).mpr ⟨(dotProductEquiv (ZMod 2) (Fin 3)).symm φ, rfl⟩
  · intro h
    obtain ⟨v, hv⟩ := (coordinate_exact a).mp h
    refine ⟨dotProductEquiv (ZMod 2) (Fin 3) v, ?_⟩
    change coordinateEvaluation ((dotProductEquiv (ZMod 2) (Fin 3)).symm
      (dotProductEquiv (ZMod 2) (Fin 3) v)) = a
    simpa only [LinearEquiv.symm_apply_apply] using hv

/-- Evaluation of vectors on tagged covectors. -/
def lineEvaluation : Representation.IntertwiningMap W lineCoreRepresentation where
  toLinearMap := coreDuality.toLinearMap.comp coordinateEvaluation
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext l
    change (W g v) ⬝ᵥ l.normal.val =
      v ⬝ᵥ ((pointPerm (AutomorphismAction.graph g)).symm l.normal).val
    change (g.val *ᵥ v) ⬝ᵥ l.normal.val =
      v ⬝ᵥ (((AutomorphismAction.graph g)⁻¹).val *ᵥ l.normal.val)
    rw [← map_inv]
    change (g.val *ᵥ v) ⬝ᵥ l.normal.val = v ⬝ᵥ ((g⁻¹⁻¹.val)ᵀ *ᵥ l.normal.val)
    rw [inv_inv, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec]

@[simp] theorem lineEvaluation_apply (v : Vector) (l : Line) :
    (lineEvaluation v).val l = lineFunctional l v := dotProduct_comm v l.normal.val

/-- Coordinate sum transported to the actual module dual. -/
def lineSumLinear : LineCore →ₗ[ZMod 2] Dual :=
  (dotProductEquiv (ZMod 2) (Fin 3)).toLinearMap.comp
    (coordinateSum.comp coreDuality.symm.toLinearMap)

theorem lineSumLinear_apply (a : LineCore) :
    lineSumLinear a = ∑ l : Line, a.val l • lineFunctional l := by
  change dotProductEquiv (ZMod 2) (Fin 3)
    (∑ p : Point, a.val (Matrix.PSL3Two.Fano.duality p) • p.val) = _
  rw [map_sum]
  simp only [map_smul]
  exact Matrix.PSL3Two.Fano.duality.sum_comp (fun l : Line => a.val l • lineFunctional l)

/-- Weighted sum of tagged covectors, with values in the actual module dual. -/
def lineWeightedSum : Representation.IntertwiningMap lineCoreRepresentation W.dual where
  toLinearMap := lineSumLinear
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    change lineSumLinear (lineCoreRepresentation g a) = W.dual g (lineSumLinear a)
    rw [lineSumLinear_apply, lineSumLinear_apply]
    change (∑ l : Line, a.val ((linePerm g).symm l) • lineFunctional l) = _
    rw [← Equiv.sum_comp (linePerm g) (fun l : Line =>
      a.val ((linePerm g).symm l) • lineFunctional l)]
    simp only [Equiv.symm_apply_apply, lineFunctional_action, map_sum, map_smul]

@[simp] theorem lineWeightedSum_apply (a : LineCore) :
    lineWeightedSum a = ∑ l : Line, a.val l • lineFunctional l := lineSumLinear_apply a

theorem lineEvaluation_injective : Function.Injective lineEvaluation :=
  coreDuality.injective.comp coordinateEvaluation_injective

theorem lineWeightedSum_surjective : Function.Surjective lineWeightedSum :=
  (dotProductEquiv (ZMod 2) (Fin 3)).surjective.comp
    (coordinateSum_surjective.comp coreDuality.symm.surjective)

theorem line_exact : LinearMap.range lineEvaluation.toLinearMap =
    LinearMap.ker lineWeightedSum.toLinearMap := by
  ext a
  constructor
  · rintro ⟨v, rfl⟩
    change dotProductEquiv (ZMod 2) (Fin 3)
      (coordinateSum (coreDuality.symm (coreDuality (coordinateEvaluation v)))) = 0
    rw [LinearEquiv.symm_apply_apply, (coordinate_exact _).mpr ⟨v, rfl⟩, map_zero]
  · intro h
    have h0 : coordinateSum (coreDuality.symm a) = 0 :=
      (dotProductEquiv (ZMod 2) (Fin 3)).injective (h.trans (map_zero _).symm)
    obtain ⟨v, hv⟩ := (coordinate_exact _).mp h0
    refine ⟨v, ?_⟩
    change coreDuality (coordinateEvaluation v) = a
    rw [hv, LinearEquiv.apply_symm_apply]

end BinaryLinearThree.FanoDecomposition
