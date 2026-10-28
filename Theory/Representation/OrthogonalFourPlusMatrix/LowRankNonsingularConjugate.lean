module
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerSingularity

/-!
# A rank-two involution at any nonsingular determinant point

A nonidentity low-rank normalizer involution fixes its displacement line.
That line is nonsingular by the rank-one quadratic-isometry argument, and
field linearity makes every coefficient multiple fixed. Over F₄, scale a
fixed point to any prescribed nonzero determinant and move it to the desired
matrix by left multiplication in SL₂(4). Thus an inner conjugate of the
original operator fixes every specified nonsingular point.

Source application: the Sylow point choice in Aschbacher–Smith 9.4.1,
printed p.735, using the rank-two action supplied by 9.2.4(2).
-/

@[expose] public noncomputable section
open Matrix Module
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

/-- A low-rank normalizer involution fixes a nonsingular displacement vector. -/
theorem low_rank_involution_nonsingular_fixed
    (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hne : t ≠ 1) (ht2 : t * t = 1)
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 2) :
    ∃ u : V, u.det ≠ 0 ∧ t u = u := by
  obtain ⟨x,hx⟩ : ∃ x : V, t x ≠ x := by
    by_contra! h
    exact hne (LinearEquiv.ext h)
  let u := t x - x
  have hu : u ≠ 0 := sub_ne_zero.mpr hx
  have hdet : u.det ≠ 0 := fun hz =>
    low_rank_involution_singular_not_mem_displacement t ht hr
      (by simpa only [pow_two] using ht2) u hu hz ⟨x,rfl⟩
  refine ⟨u,hdet,?_⟩
  have hs : t (t x) = x := by
    exact LinearEquiv.congr_fun ht2 x
  change t (t x - x) = t x - x
  rw [map_sub,hs]
  funext i j
  change x i j - t x i j = t x i j - x i j
  simp only [sub_eq_add_neg,CharTwo.neg_eq,add_comm]

/-- An inner conjugate of the specified rank-two actor fixes any nonsingular point. -/
theorem exists_inner_conjugate_fixing_nonsingular
    (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hne : t ≠ 1) (ht2 : t * t = 1)
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 2)
    (v : V) (hv : v.det ≠ 0) :
    ∃ a : G, (linearAction a * t * (linearAction a)⁻¹) v = v := by
  obtain ⟨u,hu,htu⟩ := low_rank_involution_nonsingular_fixed t ht hne ht2 hr
  obtain ⟨c,hc⟩ := Finite.surjective_of_injective
    (CharTwo.sq_injective : Function.Injective (fun c : F => c ^ 2)) (v.det / u.det)
  change c ^ 2 = v.det / u.det at hc
  let s := c • u
  have hsdet : s.det = v.det := by
    change (c • u).det = v.det
    rw [Matrix.det_smul]
    change c ^ 2 * u.det = v.det
    rw [hc,div_mul_cancel₀ _ hu]
  have hts : t s = s := by
    dsimp only [s]
    rw [low_rank_field_linear t ht hr,htu]
  let a : Matrix.SpecialLinearGroup (Fin 2) F := ⟨v * s⁻¹,by
    rw [Matrix.det_mul,Matrix.det_nonsing_inv,hsdet,Ring.inverse_eq_inv,
      mul_inv_cancel₀ hv]⟩
  have ha : linearAction (a,1) s = v := by
    change (v * s⁻¹) * s * (1 : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹.val = v
    rw [inv_one,SpecialLinearGroup.coe_one,mul_one,mul_assoc,
      Matrix.nonsing_inv_mul s (isUnit_iff_ne_zero.mpr (hsdet.trans_ne hv)),mul_one]
  refine ⟨(a,1),?_⟩
  change linearAction (a,1) (t ((linearAction (a,1)).symm v)) = v
  have hai : (linearAction (a,1)).symm v = s := by
    rw [←ha,LinearEquiv.symm_apply_apply]
  rw [hai,hts,ha]

end ClassicalOrthogonal.FourPlusMatrix.Binary
