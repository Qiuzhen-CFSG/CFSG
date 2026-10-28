module
public import Theory.Representation.AlternatingFiveMovedPair.NaturalCommutant
public import Theory.Representation.AlternatingFiveMovedPair.NaturalDisplacement

/-!
# Involutions in the commutant and pure-swap coset of the natural pair

The two scalar commutant blocks have odd order, so a centralizing involution
is the identity. Composing a component-swapping intertwiner with the explicit
factor swap puts it in the commutant. Involutivity forces the first scalar to
be one. The first block is then ordinary transpose, moving two dimensions;
the second remains Frobenius-semilinear and moves at least four dimensions.

Source: Aschbacher–Smith, quasithin manuscript, D.3.5, printed pp.195–196.
-/

@[expose] public noncomputable section
open Module
open scoped TensorProduct
namespace Representation.AlternatingFiveMovedPair.Natural
open SL2FourNatural BinaryOffender BinaryOffender.NaturalTensor

theorem centralizing_involution_eq_one (T : Module.End (ZMod 2) Space)
    (hT : T * T = 1)
    (hcomm : ∀ g v, T (action g v) = action g (T v)) : T = 1 := by
  obtain ⟨a, b, hab⟩ := NaturalCommutant.centralizer_block_scalars T hcomm
  have ha : a ^ 2 = 1 := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Tensor)
    intro v
    have h := congrArg (fun f : Module.End (ZMod 2) Space => (f (v, 0)).1) hT
    change (T (T (v, 0))).1 = v at h
    rw [hab, hab] at h
    simpa only [smul_smul, pow_two, one_smul] using h
  have hb : b ^ 2 = 1 := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Tensor)
    intro v
    have h := congrArg (fun f : Module.End (ZMod 2) Space => (f (0, v)).2) hT
    change (T (T (0, v))).2 = v at h
    rw [hab, hab] at h
    simpa only [smul_smul, pow_two, one_smul] using h
  have ha1 : a = 1 := CharTwo.sq_injective (by simpa only [one_pow] using ha)
  have hb1 : b = 1 := CharTwo.sq_injective (by simpa only [one_pow] using hb)
  apply LinearMap.ext
  intro v
  change T v = v
  simpa only [ha1, hb1, one_smul] using hab v

theorem tensorTranspose_smul (a : F) (v : Tensor) :
    tensorTranspose (a • v) = a • tensorTranspose v :=
  (_root_.TensorProduct.comm F V V).map_smul a v

theorem tensorTranspose_involutive (v : Tensor) :
    tensorTranspose (tensorTranspose v) = v := by
  exact (_root_.TensorProduct.comm F V V).symm_apply_apply v

theorem tensorFrobenius_involutive (v : Tensor) :
    tensorFrobenius (tensorFrobenius v) = v := by
  apply (tensorCoordinates F).injective
  funext i j
  rw [tensorFrobenius_coordinates, tensorFrobenius_coordinates,
    fieldFrobenius_involutive]

theorem tensorFrobenius_transpose (v : Tensor) :
    tensorFrobenius (tensorTranspose v) = tensorTranspose (tensorFrobenius v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change tensorFrobenius (y ⊗ₜ[F] x) = tensorTranspose (tensorFrobenius (x ⊗ₜ[F] y))
    rw [tensorFrobenius_tmul, tensorFrobenius_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem factorSwap_involutive (v : Space) : factorSwap (factorSwap v) = v := by
  apply Prod.ext
  · exact tensorTranspose_involutive v.1
  · change tensorTranspose (tensorFrobenius (tensorTranspose (tensorFrobenius v.2))) = v.2
    rw [tensorFrobenius_transpose, tensorFrobenius_involutive, tensorTranspose_involutive]

theorem swap_intertwiner_block_scalars (T : Module.End (ZMod 2) Space)
    (hT : ∀ g v, T (action g v) = action (g.2, g.1) (T v)) :
    ∃ a b : F, ∀ v, T v =
      (a • tensorTranspose v.1, b • tensorTranspose (tensorFrobenius v.2)) := by
  let q := T.comp factorSwap.toLinearMap
  have hq : ∀ g v, q (action g v) = action g (q v) := by
    intro g v
    change T (factorSwap (action g v)) = action g (T (factorSwap v))
    rw [factorSwap_action, hT]
  obtain ⟨a, b, hab⟩ := NaturalCommutant.centralizer_block_scalars q hq
  refine ⟨a, b, fun v => ?_⟩
  have h := hab (factorSwap v)
  change T (factorSwap (factorSwap v)) = _ at h
  rw [factorSwap_involutive] at h
  exact h

private lemma prod_operatorFixedCodim (A B : Module.End (ZMod 2) Tensor) :
    operatorFixedCodim (A.prodMap B) = operatorFixedCodim A + operatorFixedCodim B := by
  have hmap : A.prodMap B - 1 = (A - 1).prodMap (B - 1) := by ext x <;> rfl
  let P := LinearMap.range (A - 1)
  let Q := LinearMap.range (B - 1)
  let : Module.Free (ZMod 2) P := Module.Free.of_divisionRing (ZMod 2) P
  let : Module.Free (ZMod 2) Q := Module.Free.of_divisionRing (ZMod 2) Q
  have hi : Function.Injective (P.subtype.prodMap Q.subtype) := by
    rintro ⟨x, y⟩ ⟨x',y'⟩ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hd := LinearMap.finrank_range_of_inj (f := P.subtype.prodMap Q.subtype) hi
  rw [LinearMap.range_prodMap, Submodule.range_subtype, Submodule.range_subtype,
    Module.finrank_prod] at hd
  unfold operatorFixedCodim
  rw [hmap, LinearMap.range_prodMap]
  exact hd

/-- Every involutory intertwiner of the pure component swap moves six dimensions. -/
theorem swap_intertwiner_displacement (T : Module.End (ZMod 2) Space)
    (hT2 : T * T = 1)
    (hT : ∀ g v, T (action g v) = action (g.2, g.1) (T v)) :
    6 ≤ operatorFixedCodim T := by
  obtain ⟨a, b, hab⟩ := swap_intertwiner_block_scalars T hT
  have ha : a ^ 2 = 1 := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Tensor)
    intro v
    have h := congrArg (fun f : Module.End (ZMod 2) Space => (f (v, 0)).1) hT2
    change (T (T (v, 0))).1 = v at h
    rw [hab, hab] at h
    change a • tensorTranspose (a • tensorTranspose v) = v at h
    rw [tensorTranspose_smul, tensorTranspose_involutive, smul_smul] at h
    simpa only [pow_two, one_smul] using h
  have ha1 : a = 1 := CharTwo.sq_injective (by simpa only [one_pow] using ha)
  let B : Module.End (ZMod 2) Tensor := b • (tensorFrobenius.trans tensorTranspose).toLinearMap
  have hprod : T = tensorTranspose.toLinearMap.prodMap B := by
    apply LinearMap.ext
    intro v
    change T v = (tensorTranspose v.1, b • tensorTranspose (tensorFrobenius v.2))
    simpa only [ha1, one_smul] using hab v
  have hB : 4 ≤ operatorFixedCodim B := by
    apply field_tensor_bound F (n := 2)
      (by rw [Nat.card_eq_fintype_card, card_field]; norm_num) _ fieldFrobenius.toRingHom
    · refine ⟨⟨0, 1⟩, ?_⟩
      decide +kernel
    · intro c v
      change b • tensorTranspose (tensorFrobenius (c • v)) =
        fieldFrobenius c • (b • tensorTranspose (tensorFrobenius v))
      rw [tensorFrobenius_smul, tensorTranspose_smul, smul_smul, smul_smul, mul_comm]
  rw [hprod, prod_operatorFixedCodim]
  have hA := tensorTranspose_displacement
  omega

end Representation.AlternatingFiveMovedPair.Natural
