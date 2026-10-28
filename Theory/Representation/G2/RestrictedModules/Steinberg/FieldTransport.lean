module

public import Theory.Representation.G2.RestrictedModules.Steinberg.Construction
public import Theory.Representation.G2.RestrictedModules.NaturalFieldTransport
public import Theory.Representation.ExtendScalars

/-!
# Coefficient automorphisms of the concrete G₂ highest-weight orbit

Coefficient transport on the natural tensor cube preserves the specified seed
and carries its orbit span onto itself, using the actual `Atlas.G2.fieldEquiv`.
Restricting this semilinear equivalence gives a genuine equivalence between the
coefficient-conjugate representation and the group-automorphism twist. The
intertwining equivalence is retained after every scalar extension.

Source: GLS3, Definition 2.8.3 and Remark 2.8.8.
-/

@[expose] public noncomputable section

namespace Atlas.G2.Restricted.Steinberg

open scoped TensorProduct

variable (F : Type*) [Field F] [CharP F 2]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Coefficient transport on the actual tensor cube. -/
def ambientCoefficientEquiv (σ : F ≃+* F) :
    LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) (Ambient F) (Ambient F) :=
  TensorProduct.congr (Representation.coordinateSemilinearEquiv σ (Fin 6))
    (TensorProduct.congr (Representation.coordinateSemilinearEquiv σ (Fin 6))
      (Representation.coordinateSemilinearEquiv σ (Fin 6)))

omit [CharP F 2] in
@[simp] theorem ambientCoefficientEquiv_pure (σ : F ≃+* F)
    (x y z : NaturalCoordinates.Space F) :
    ambientCoefficientEquiv F σ (pure F x y z) =
      pure F (fun i => σ (x i)) (fun i => σ (y i)) (fun i => σ (z i)) := by
  have h (v : NaturalCoordinates.Space F) :
      Representation.coordinateSemilinearEquiv σ (Fin 6) v = fun i => σ (v i) := by
    ext i
    exact Representation.coordinateSemilinearEquiv_apply σ (Fin 6) v i
  simp only [ambientCoefficientEquiv, pure, TensorProduct.congr_tmul, h]

omit [CharP F 2] in
@[simp] theorem ambientCoefficientEquiv_symm (σ : F ≃+* F) :
    (ambientCoefficientEquiv F σ).symm = ambientCoefficientEquiv F σ.symm := by
  have h : (Representation.coordinateSemilinearEquiv σ (Fin 6)).symm =
      Representation.coordinateSemilinearEquiv σ.symm (Fin 6) := by
    apply LinearEquiv.ext
    intro v
    funext i
    rw [Representation.coordinateSemilinearEquiv_symm_apply]
    exact (Representation.coordinateSemilinearEquiv_apply σ.symm (Fin 6) v i).symm
  simp only [ambientCoefficientEquiv, TensorProduct.congr_symm, h]
  rfl

omit [CharP F 2] in
/-- The chosen tensor has coefficients in the prime field. -/
@[simp] theorem ambientCoefficientEquiv_seed (σ : F ≃+* F) :
    ambientCoefficientEquiv F σ (seed F) = seed F := by
  have he (i : Fin 6) : (fun j => σ (e F i j)) = e F i := by
    ext j
    simp [e, Pi.single_apply]
  simp only [seed, map_add, ambientCoefficientEquiv_pure, he]

/-- The coefficient map intertwines the actual field automorphism on every tensor. -/
theorem ambientAction_fieldEquiv (σ : F ≃+* F) (g : Model F) (v : Ambient F) :
    ambientAction F (fieldEquiv σ g) (ambientCoefficientEquiv F σ v) =
      ambientCoefficientEquiv F σ (ambientAction F g v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul x yz =>
    induction yz using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul y z =>
      change ambientAction F (fieldEquiv σ g)
        (ambientCoefficientEquiv F σ (pure F x y z)) =
        ambientCoefficientEquiv F σ (ambientAction F g (pure F x y z))
      simp only [ambientCoefficientEquiv_pure, ambientAction_pure,
        NaturalCoordinates.action_fieldEquiv]

/-- Coefficient transport preserves the generated subspace. -/
theorem ambientCoefficientEquiv_mem (σ : F ≃+* F) (v : Ambient F)
    (hv : v ∈ orbitSpan F) : ambientCoefficientEquiv F σ v ∈ orbitSpan F := by
  change ambientCoefficientEquiv F σ v ∈ (orbitSpan F).toSubmodule
  change v ∈ Submodule.span F _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨g, rfl⟩ := hv
    rw [← ambientAction_fieldEquiv, ambientCoefficientEquiv_seed]
    exact Submodule.subset_span ⟨fieldEquiv σ g, rfl⟩
  | zero => simpa only [map_zero] using (orbitSpan F).toSubmodule.zero_mem
  | add v w _ _ hv hw => simpa only [map_add] using (orbitSpan F).toSubmodule.add_mem hv hw
  | smul a v _ hv =>
    rw [map_smulₛₗ]
    exact (orbitSpan F).toSubmodule.smul_mem ((σ : F →+* F) a) hv

/-- The genuine semilinear coefficient equivalence on the orbit carrier. -/
def coefficientEquiv (σ : F ≃+* F) :
    LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) (Space F) (Space F) where
  toFun v := ⟨ambientCoefficientEquiv F σ v.val,
    ambientCoefficientEquiv_mem F σ v.val v.property⟩
  invFun v := ⟨(ambientCoefficientEquiv F σ).symm v.val, by
    rw [ambientCoefficientEquiv_symm]
    exact ambientCoefficientEquiv_mem F σ.symm v.val v.property⟩
  left_inv v := Subtype.ext ((ambientCoefficientEquiv F σ).symm_apply_apply v.val)
  right_inv v := Subtype.ext ((ambientCoefficientEquiv F σ).apply_symm_apply v.val)
  map_add' v w := Subtype.ext ((ambientCoefficientEquiv F σ).map_add v.val w.val)
  map_smul' a v := Subtype.ext ((ambientCoefficientEquiv F σ).map_smulₛₗ a v.val)

@[simp] theorem coefficientEquiv_val (σ : F ≃+* F) (v : Space F) :
    (coefficientEquiv F σ v).val = ambientCoefficientEquiv F σ v.val := rfl

@[simp] theorem coefficientEquiv_highestVector (σ : F ≃+* F) :
    coefficientEquiv F σ (highestVector F) = highestVector F :=
  Subtype.ext (ambientCoefficientEquiv_seed F σ)

/-- Field transport on the actual restricted action. -/
theorem action_fieldEquiv (σ : F ≃+* F) (g : Model F) (v : Space F) :
    action F (fieldEquiv σ g) (coefficientEquiv F σ v) =
      coefficientEquiv F σ (action F g v) :=
  Subtype.ext (ambientAction_fieldEquiv F σ g v.val)

set_option backward.isDefEq.respectTransparency false in
/-- Equality of coefficient conjugation and precomposition by the actual field automorphism. -/
theorem coefficientConjugate_eq (σ : F ≃+* F) :
    Representation.semilinearConjugate (F := F) (G := Model F)
        (V := Space F) (W := Space F) σ (action F) (coefficientEquiv F σ) =
      (action F).comp (fieldEquiv σ).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  have h := action_fieldEquiv F σ g ((coefficientEquiv F σ).symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- A genuine intertwining equivalence, on the specified carrier. -/
def coefficientConjugateEquiv (σ : F ≃+* F) :
    Representation.RepEquiv
      (Representation.semilinearConjugate (F := F) (G := Model F)
        (V := Space F) (W := Space F) σ (action F) (coefficientEquiv F σ))
      ((action F).comp (fieldEquiv σ).toMonoidHom) where
  toLinearEquiv := LinearEquiv.refl F _
  isIntertwining' g := by
    simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]
    exact DFunLike.congr_fun (coefficientConjugate_eq F σ) g

set_option backward.isDefEq.respectTransparency false in
/-- The intertwining equivalence persists after an arbitrary scalar extension. -/
def coefficientConjugateExtendScalarsEquiv (σ : F ≃+* F)
    (E : Type*) [Field E] [Algebra F E] :
    Representation.RepEquiv
      (Representation.extendScalars (F := F) (V := Space F) E
        (Representation.semilinearConjugate (F := F) (G := Model F)
        (V := Space F) (W := Space F) σ (action F) (coefficientEquiv F σ)))
      ((Representation.extendScalars (F := F) (V := Space F) E (action F)).comp (fieldEquiv σ).toMonoidHom) where
  toLinearEquiv := LinearEquiv.refl E _
  isIntertwining' g := by
    simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]
    rw [coefficientConjugate_eq]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient Frobenius agrees with the genuine finite-field group automorphism. -/
theorem frobeniusConjugate_eq [Finite F] (r : ℕ) :
    Representation.semilinearConjugate (F := F) (G := Model F)
        (V := Space F) (W := Space F) (iterateFrobeniusEquiv F 2 r) (action F)
        (coefficientEquiv F (iterateFrobeniusEquiv F 2 r)) =
      (action F).comp (NaturalCoordinates.frobeniusAutomorphism F r).toMonoidHom :=
  coefficientConjugate_eq F _

end Atlas.G2.Restricted.Steinberg
