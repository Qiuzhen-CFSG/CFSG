module
public import Theory.Representation.AlternatingFiveMovedPair.Natural

/-!
# Natural descent-pair involution operators

The two descent constituents admit an actual factor swap. It is transpose on
the first tensor and transpose followed by Frobenius on the second. The first
operator moves two binary dimensions, while the second moves at least four
by the semilinear displacement bound. Field intertwiners of the first factor
move at least eight dimensions even with arbitrary summand mixing.

Source: Aschbacher–Smith, quasithin manuscript, D.3.5, pp.195–196.
-/

@[expose] public noncomputable section
open Module
open scoped TensorProduct
namespace Representation.AlternatingFiveMovedPair.Natural
open SL2FourNatural BinaryOffender BinaryOffender.NaturalTensor
/-- A nontrivial field twist on the first component also moves eight dimensions. -/
theorem first_field_intertwiner_bound (T : Module.End (ZMod 2) Space)
    (r : SL) (σ : F →+* F) (hσ : ∃ a, σ a ≠ a)
    (hT : ∀ g v, T (action (g, 1) v) =
      action (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹, 1) (T v)) :
    8 ≤ operatorFixedCodim T := by
  let ρ := action.comp (MonoidHom.inl SL SL)
  have hh := field_bound_of_realization ρ firstCoordinates
    firstCoordinates_action T r σ hσ hT
  have hd : finrank (ZMod 2) (V × V) = 8 := by
    simp only [Module.finrank_prod, V, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [NaturalTensor.finrank_field F (n := 2)
      (by rw [Nat.card_eq_fintype_card, card_field]; norm_num)]
  rwa [hd] at hh

/-- Entrywise Frobenius in the explicit two-by-two tensor coordinates. -/
def coordinateFrobenius : (Fin 2 → Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → Fin 2 → F) where
  toFun v i j := fieldFrobenius (v i j)
  invFun v i j := fieldFrobenius (v i j)
  left_inv v := by funext i j; exact fieldFrobenius_involutive _
  right_inv v := by funext i j; exact fieldFrobenius_involutive _
  map_add' v w := by funext i j; exact map_add fieldFrobenius _ _
  map_smul' c v := by funext i j; exact ZMod.map_smul fieldFrobenius c (v i j)

/-- Both natural factors are Frobenius-twisted simultaneously. -/
def tensorFrobenius : Tensor ≃ₗ[ZMod 2] Tensor :=
  ((tensorCoordinates F).restrictScalars (ZMod 2)).trans
    (coordinateFrobenius.trans ((tensorCoordinates F).symm.restrictScalars (ZMod 2)))

lemma tensorFrobenius_coordinates (v : Tensor) (i j : Fin 2) :
    tensorCoordinates F (tensorFrobenius v) i j = fieldFrobenius (tensorCoordinates F v i j) := by
  change tensorCoordinates F ((tensorCoordinates F).symm _) i j = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

lemma tensorFrobenius_tmul (v w : V) :
    tensorFrobenius (v ⊗ₜ[F] w) = frobeniusLinear v ⊗ₜ[F] frobeniusLinear w := by
  apply (tensorCoordinates F).injective
  funext i j
  rw [tensorFrobenius_coordinates, tensorCoordinates_tmul, tensorCoordinates_tmul, map_mul]
  rfl

lemma tensorFrobenius_smul (a : F) (v : Tensor) :
    tensorFrobenius (a • v) = fieldFrobenius a • tensorFrobenius v := by
  apply (tensorCoordinates F).injective
  funext i j
  rw [tensorFrobenius_coordinates, map_smul, map_smul]
  change fieldFrobenius (a * tensorCoordinates F v i j) =
    fieldFrobenius a * tensorCoordinates F (tensorFrobenius v) i j
  rw [map_mul, tensorFrobenius_coordinates]

/-- The ordinary factor interchange in tensor coordinates. -/
def tensorTranspose : Tensor ≃ₗ[ZMod 2] Tensor :=
  (_root_.TensorProduct.comm F V V).restrictScalars (ZMod 2)

/-- The factor swap preserves both descent types, with a field twist on the second. -/
def factorSwap : Space ≃ₗ[ZMod 2] Space :=
  tensorTranspose.prodCongr (tensorFrobenius.trans tensorTranspose)

lemma factorSwap_action (g : SL × SL) (v : Space) :
    factorSwap (action g v) = action (g.2, g.1) (factorSwap v) := by
  apply Prod.ext
  · exact tensorFlip_intertwines F g v.1
  · change tensorTranspose (tensorFrobenius (tensorAction F (g.1, slFrobenius g.2) v.2)) =
      tensorAction F (g.2, slFrobenius g.1) (tensorTranspose (tensorFrobenius v.2))
    induction v.2 using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      change tensorTranspose (tensorFrobenius
          (specialLinearNatural 2 g.1 x ⊗ₜ[F] specialLinearNatural 2 (slFrobenius g.2) y)) = _
      rw [tensorFrobenius_tmul, tensorFrobenius_tmul]
      change frobeniusLinear (SL2FourNatural.action (slFrobenius g.2) y) ⊗ₜ[F]
          frobeniusLinear (SL2FourNatural.action g.1 x) =
        SL2FourNatural.action g.2 (frobeniusLinear y) ⊗ₜ[F]
          SL2FourNatural.action (slFrobenius g.1) (frobeniusLinear x)
      rw [frobenius_action, frobenius_action]
      have hsig : slFrobenius (slFrobenius g.2) = g.2 := slFrobenius.left_inv _
      rw [hsig]
    | add x y hx hy => simp only [map_add, hx, hy]

private lemma prod_operatorFixedCodim {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) W]
    (A : Module.End (ZMod 2) U) (B : Module.End (ZMod 2) W) :
    operatorFixedCodim (A.prodMap B) = operatorFixedCodim A + operatorFixedCodim B := by
  have hmap : A.prodMap B - 1 = (A - 1).prodMap (B - 1) := by ext x <;> rfl
  let P := LinearMap.range (A - 1)
  let Q := LinearMap.range (B - 1)
  have hi : Function.Injective (P.subtype.prodMap Q.subtype) := by
    rintro ⟨x, y⟩ ⟨x',y'⟩ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hd := LinearMap.finrank_range_of_inj (f := P.subtype.prodMap Q.subtype) hi
  rw [LinearMap.range_prodMap, Submodule.range_subtype, Submodule.range_subtype,
    Module.finrank_prod] at hd
  unfold operatorFixedCodim
  rw [hmap, LinearMap.range_prodMap]
  exact hd

lemma tensorTranspose_displacement : 2 ≤ operatorFixedCodim tensorTranspose.toLinearMap :=
  flip_tensor_bound F (n := 2) (by rw [Nat.card_eq_fintype_card, card_field]; norm_num)

lemma twistedTranspose_displacement :
    4 ≤ operatorFixedCodim (tensorFrobenius.trans tensorTranspose).toLinearMap := by
  apply field_tensor_bound F (n := 2) (by rw [Nat.card_eq_fintype_card, card_field]; norm_num)
    _ fieldFrobenius.toRingHom
  · refine ⟨⟨0, 1⟩, ?_⟩
    decide +kernel
  · intro a v
    change tensorTranspose (tensorFrobenius (a • v)) = _
    rw [tensorFrobenius_smul]
    exact (_root_.TensorProduct.comm F V V).map_smul (fieldFrobenius a) _

/-- A factor-interchanging model involution moves at least six binary dimensions. -/
theorem factorSwap_displacement : 6 ≤ operatorFixedCodim factorSwap.toLinearMap := by
  change 6 ≤ operatorFixedCodim (tensorTranspose.toLinearMap.prodMap
    (tensorFrobenius.trans tensorTranspose).toLinearMap)
  rw [prod_operatorFixedCodim]
  have h := tensorTranspose_displacement
  have j := twistedTranspose_displacement
  omega
end Representation.AlternatingFiveMovedPair.Natural
