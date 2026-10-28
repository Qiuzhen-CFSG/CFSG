module
public import Theory.Representation.AlternatingFiveMovedPair.NaturalDisplacement
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Independent inner involutions on the natural descent pair

Both coordinate factors have four natural summands, giving displacement eight
for arbitrary inner or field intertwiners of the second factor as well as the
first. Two independently supported upper-root involutions constrain every tensor
to its first corner. Their common fixed space in the pair has binary dimension
at most four. Actual SL₂ conjugacy transports this bound, so an actor containing
nontrivial involutions supported in both factors moves at least twelve dimensions.

Source: Aschbacher–Smith, quasithin manuscript, D.3.5, pp.195–196.
-/

@[expose] public noncomputable section
open Module
open scoped TensorProduct
namespace Representation.AlternatingFiveMovedPair.Natural
open SL2FourNatural BinaryOffender BinaryOffender.NaturalTensor

lemma secondCoordinates_action (g : SL) (v : Space) :
    firstCoordinates (factorSwap (action (1, g) v)) =
      amplifiedNatural g (firstCoordinates (factorSwap v)) := by
  rw [factorSwap_action, firstCoordinates_action]

/-- The second component admits the same arbitrary-intertwiner inner bound. -/
theorem second_inner_intertwiner_bound (T : Module.End (ZMod 2) Space)
    (hTi : Function.Injective T) (r : SL) (hr : r * r = 1) (hne : r ≠ 1)
    (hT : ∀ g v, T (action (1, g) v) = action (1, r * g * r⁻¹) (T v)) :
    8 ≤ operatorFixedCodim T := by
  let ρ := action.comp (MonoidHom.inr SL SL)
  have hh := inner_bound_of_realization ρ (factorSwap.trans firstCoordinates)
    secondCoordinates_action T hTi r hr hne hT
  have hd : finrank (ZMod 2) (V × V) = 8 := by
    simp only [Module.finrank_prod, V, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [NaturalTensor.finrank_field F (n := 2)
      (by rw [Nat.card_eq_fintype_card, card_field]; norm_num)]
  rwa [hd] at hh

/-- The second component admits the same arbitrary-intertwiner field bound. -/
theorem second_field_intertwiner_bound (T : Module.End (ZMod 2) Space)
    (r : SL) (σ : F →+* F) (hσ : ∃ a, σ a ≠ a)
    (hT : ∀ g v, T (action (1, g) v) =
      action (1, r * Matrix.SpecialLinearGroup.map σ g * r⁻¹) (T v)) :
    8 ≤ operatorFixedCodim T := by
  let ρ := action.comp (MonoidHom.inr SL SL)
  have hh := field_bound_of_realization ρ (factorSwap.trans firstCoordinates)
    secondCoordinates_action T r σ hσ hT
  have hd : finrank (ZMod 2) (V × V) = 8 := by
    simp only [Module.finrank_prod, V, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [NaturalTensor.finrank_field F (n := 2)
      (by rw [Nat.card_eq_fintype_card, card_field]; norm_num)]
  rwa [hd] at hh

private lemma upper_first (v : Tensor) (i : Fin 2) :
    tensorCoordinates F (tensorAction F (upper 1, 1) v) i 0 =
      tensorCoordinates F v i 0 + tensorCoordinates F v i 1 := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change tensorCoordinates F (specialLinearNatural 2 (upper 1) x ⊗ₜ[F]
      specialLinearNatural 2 (1 : SL) y) i 0 = _
    rw [map_one, Module.End.one_apply]
    rw [tensorCoordinates_tmul, tensorCoordinates_tmul, tensorCoordinates_tmul]
    change y i * SL2FourNatural.action (upper 1) x 0 = _
    rw [upper_action]
    simp only [Matrix.cons_val_zero, one_mul, mul_add]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; ring

private lemma upper_second (v : Tensor) (j : Fin 2) :
    tensorCoordinates F (tensorAction F (1, upper 1) v) 0 j =
      tensorCoordinates F v 0 j + tensorCoordinates F v 1 j := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change tensorCoordinates F (specialLinearNatural 2 (1 : SL) x ⊗ₜ[F]
      specialLinearNatural 2 (upper 1) y) 0 j = _
    rw [map_one, Module.End.one_apply]
    rw [tensorCoordinates_tmul, tensorCoordinates_tmul, tensorCoordinates_tmul]
    change SL2FourNatural.action (upper 1) y 0 * x j = _
    rw [upper_action]
    simp only [Matrix.cons_val_zero, one_mul, add_mul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; ring

private lemma upper_fixed_tensor_zero (v : Tensor)
    (ha : tensorAction F (upper 1, 1) v = v)
    (hb : tensorAction F (1, upper 1) v = v)
    (h00 : tensorCoordinates F v 0 0 = 0) : v = 0 := by
  have hc (i : Fin 2) : tensorCoordinates F v i 1 = 0 := by
    have h := upper_first v i
    rw [ha] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  have hr (j : Fin 2) : tensorCoordinates F v 1 j = 0 := by
    have h := upper_second v j
    rw [hb] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  apply (tensorCoordinates F).injective
  funext i j
  fin_cases i <;> fin_cases j <;> simp [h00, hc, hr]

lemma slFrobenius_upper_one : slFrobenius (upper 1) = upper 1 := by
  apply Subtype.ext
  funext i j
  change fieldFrobenius ((upper 1).val i j) = (upper 1).val i j
  fin_cases i <;> fin_cases j <;> simp [upper]

/-- Independent upper-root involutions leave at most four binary fixed dimensions. -/
theorem common_upper_fixed_finrank :
    finrank (ZMod 2) ↥(LinearMap.ker (action (upper 1, 1) - 1) ⊓
      LinearMap.ker (action (1, upper 1) - 1)) ≤ 4 := by
  let K := LinearMap.ker (action (upper 1, 1) - 1) ⊓
    LinearMap.ker (action (1, upper 1) - 1)
  let f : K →ₗ[ZMod 2] F × F :=
    { toFun v := (tensorCoordinates F v.val.1 0 0, tensorCoordinates F v.val.2 0 0)
      map_add' v w := by simp
      map_smul' c v := by
        exact Prod.ext
          (congrArg (fun w : Fin 2 → Fin 2 → F => w 0 0)
            (((tensorCoordinates F).restrictScalars (ZMod 2)).map_smul c v.val.1))
          (congrArg (fun w : Fin 2 → Fin 2 → F => w 0 0)
            (((tensorCoordinates F).restrictScalars (ZMod 2)).map_smul c v.val.2)) }
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have hf : f v = 0 := hv
    have ha : action (upper 1, 1) v.val = v.val := sub_eq_zero.mp v.property.1
    have hb : action (1, upper 1) v.val = v.val := sub_eq_zero.mp v.property.2
    apply Subtype.ext
    apply Prod.ext
    · exact upper_fixed_tensor_zero v.val.1 (congrArg Prod.fst ha)
        (congrArg Prod.fst hb) (congrArg Prod.fst hf)
    · apply upper_fixed_tensor_zero v.val.2
      · have hh := congrArg Prod.snd ha
        change tensorAction F (upper 1, slFrobenius 1) v.val.2 = v.val.2 at hh
        simpa only [map_one] using hh
      · have hh := congrArg Prod.snd hb
        change tensorAction F (1, slFrobenius (upper 1)) v.val.2 = v.val.2 at hh
        rwa [slFrobenius_upper_one] at hh
      · exact congrArg Prod.snd hf
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  have he : finrank (ZMod 2) (F × F) = 4 := by
    rw [Module.finrank_prod, NaturalTensor.finrank_field F (n := 2)
      (by rw [Nat.card_eq_fintype_card, card_field]; norm_num)]
  rwa [he] at hd

private lemma upper_one_order : orderOf (upper (1 : F)) = 2 := by
  apply (orderOf_eq_prime_iff (p := 2)).mpr
  constructor
  · rw [pow_two]
    apply Subtype.ext
    change (upper 1).val * (upper 1).val = (1 : SL).val
    decide +kernel
  · intro h
    have hh := congrArg (fun g : SL => g.val 0 1) h
    exact one_ne_zero hh

private lemma exists_conjugate_upper (a : SL) (ha : a * a = 1) (hne : a ≠ 1) :
    ∃ c : SL, c * upper 1 * c⁻¹ = a := by
  let e := Theory.PSL2.sl2QuotientEquiv F
  have hoa : orderOf a = 2 := (orderOf_eq_prime_iff (p := 2)).mpr ⟨by rw [pow_two, ha], hne⟩
  have hp := Theory.PSL2.involutions_isConj (e (upper 1)) (e a)
    ((e.orderOf_eq (upper 1)).trans upper_one_order) ((e.orderOf_eq a).trans hoa)
  have hc : IsConj (upper 1) a := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      using e.symm.toMonoidHom.map_isConj hp
  exact isConj_iff.mp hc

/-- Independent inner involutions leave at most four binary fixed dimensions. -/
theorem common_inner_fixed_finrank (a b : SL)
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    finrank (ZMod 2) ↥(LinearMap.ker (action (a, 1) - 1) ⊓
      LinearMap.ker (action (1, b) - 1)) ≤ 4 := by
  obtain ⟨c, hc⟩ := exists_conjugate_upper a ha ha1
  obtain ⟨d, hd⟩ := exists_conjugate_upper b hb hb1
  let K := LinearMap.ker (action (a, 1) - 1) ⊓ LinearMap.ker (action (1, b) - 1)
  let U := LinearMap.ker (action (upper 1, 1) - 1) ⊓
    LinearMap.ker (action (1, upper 1) - 1)
  have hleft (v : Space) : action (upper 1, 1) (action (c⁻¹, d⁻¹) v) =
      action (c⁻¹, d⁻¹) (action (a, 1) v) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    apply congrArg (fun g : SL × SL => action g v)
    apply Prod.ext
    · change upper 1 * c⁻¹ = c⁻¹ * a
      rw [← hc]
      group
    · exact one_mul d⁻¹ |>.trans (mul_one d⁻¹).symm
  have hright (v : Space) : action (1, upper 1) (action (c⁻¹, d⁻¹) v) =
      action (c⁻¹, d⁻¹) (action (1, b) v) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    apply congrArg (fun g : SL × SL => action g v)
    apply Prod.ext
    · exact one_mul c⁻¹ |>.trans (mul_one c⁻¹).symm
    · change upper 1 * d⁻¹ = d⁻¹ * b
      rw [← hd]
      group
  have hU (v : K) : action (c⁻¹, d⁻¹) v.val ∈ U := by
    refine ⟨?_, ?_⟩
    · change action (upper 1, 1) (action (c⁻¹, d⁻¹) v.val) - action (c⁻¹, d⁻¹) v.val = 0
      rw [hleft, sub_eq_zero.mp v.property.1, Module.End.one_apply, sub_self]
    · change action (1, upper 1) (action (c⁻¹, d⁻¹) v.val) - action (c⁻¹, d⁻¹) v.val = 0
      rw [hright, sub_eq_zero.mp v.property.2, Module.End.one_apply, sub_self]
  let f : K →ₗ[ZMod 2] U := ((action (c⁻¹, d⁻¹)).comp K.subtype).codRestrict U hU
  have hi : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    exact (action.apply_bijective (c⁻¹, d⁻¹)).injective (congrArg Subtype.val hvw)
  exact (LinearMap.finrank_le_finrank_of_injective hi).trans common_upper_fixed_finrank

/-- An actor containing inner involutions on both factors moves twelve dimensions. -/
theorem fixedCodim_ge_twelve_of_independent_inner
    (A : Subgroup (Module.End (ZMod 2) Space)ˣ)
    (a b : SL) (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (haA : action.asGroupHom (a, 1) ∈ A) (hbA : action.asGroupHom (1, b) ∈ A) :
    12 ≤ fixedCodim (Units.coeHom _) A := by
  let K := LinearMap.ker (action (a, 1) - 1) ⊓ LinearMap.ker (action (1, b) - 1)
  have hle : fixedSpace (Units.coeHom _) A ≤ K := by
    intro v hv
    exact ⟨sub_eq_zero.mpr (hv ⟨_, haA⟩), sub_eq_zero.mpr (hv ⟨_, hbA⟩)⟩
  have hh := (Submodule.finrank_mono hle).trans (common_inner_fixed_finrank a b ha hb ha1 hb1)
  have he := fixedCodim_add_finrank (Units.coeHom (Module.End (ZMod 2) Space)) A
  change finrank (ZMod 2) (fixedSpace (Units.coeHom (Module.End (ZMod 2) Space)) A) ≤ 4 at hh
  rw [finrank_space] at he
  change 12 ≤ fixedCodim (Units.coeHom (Module.End (ZMod 2) Space)) A
  omega
end Representation.AlternatingFiveMovedPair.Natural
