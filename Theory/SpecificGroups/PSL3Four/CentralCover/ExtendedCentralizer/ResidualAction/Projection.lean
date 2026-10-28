module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.Geometry

/-!
# Faithful projection of the linear E₉ residual

The intrinsic residual embeds in the actual projective matrix group: its
exponent is three, whereas the covering kernel has exponent two. Conjugation
therefore agrees faithfully with the projective action. The action kernel
maps into the pointwise fixer of this projected subgroup, with descent kernel
of order dividing four.

Consequently a projective fixer of order dividing eighteen forces the action
kernel modulo the residual to be a two-group. That numerical matrix input is
explicit here; no centralizer order or action-surjectivity assertion is assumed
as a property of the cover.

Source: Aschbacher--Smith, 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004. This is the transfer step, not the remaining model calculation.
-/

public section

open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

private noncomputable def residualModel (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    residualIn (L := L) w ≃* ElementaryNine :=
  (fixedResidualEquiv w).symm.trans e

theorem residual_cube (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine)
    (x : residualIn (L := L) w) : x ^ 3 = 1 := by
  apply (residualModel w e).injective
  rw [map_pow, map_one]
  change Multiplicative.ofAdd (3 • (residualModel w e x).toAdd) = 1
  apply congrArg Multiplicative.ofAdd
  ext i
  change (3 : ℕ) • ((residualModel w e x).toAdd i) = (0 : ZMod 3)
  rw [nsmul_eq_mul]
  change (3 : ZMod 3) * _ = 0
  rw [show (3 : ZMod 3) = 0 by decide, zero_mul]

theorem residual_mul_comm (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine)
    (x y : residualIn (L := L) w) : x * y = y * x := by
  apply (residualModel w e).injective
  simp only [map_mul, mul_comm]

theorem residualIn_le_actionKernel (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    residualIn (L := L) w ≤ (residualAction (L := L) w).ker := by
  intro x hx
  change MulAut.conjNormal x = (1 : MulAut (residualIn (L := L) w))
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  change x * (y : centralizerIn w) * x⁻¹ = (y : centralizerIn w)
  have h := congrArg Subtype.val (residual_mul_comm w e ⟨x, hx⟩ y)
  change x * (y : centralizerIn w) = (y : centralizerIn w) * x at h
  rw [h, mul_inv_cancel_right]

@[expose] def residualToLinear (w : I) : residualIn (L := L) w →* L where
  toFun x := ⟨x.val.val, residualIn_le_linear w x.property⟩
  map_one' := by rfl
  map_mul' _ _ := by rfl

omit [L.Normal] in
theorem residualToLinear_injective (w : I) :
    Function.Injective (residualToLinear (L := L) w) := by
  intro x y h
  have hv : x.val.val = y.val.val := congrArg (fun a : L => (a : I)) h
  exact Subtype.ext (Subtype.ext hv)

@[expose] noncomputable def residualProjection (c : FourCover L) (w : I) :
    residualIn (L := L) w →* PSL := c.toMonoidHom.comp (residualToLinear w)

theorem residualProjection_injective (c : FourCover L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    Function.Injective (residualProjection c w) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hz : residualToLinear w x ∈ center L := by
    rw [← c.ker_eq_center]
    exact hx
  let := c.center_isKleinFour
  have hs : residualToLinear w x ^ 2 = 1 := by
    have hh := Monoid.pow_exponent_eq_one (⟨residualToLinear w x, hz⟩ : center L)
    rw [IsKleinFour.exponent_two] at hh
    exact congrArg Subtype.val hh
  have hs' : x ^ 2 = 1 := (residualToLinear_injective w) (by
    simpa only [map_pow, map_one] using hs)
  have hc := residual_cube w e x
  rw [pow_succ, hs', one_mul] at hc
  exact hc

@[expose] noncomputable def projectedResidual (c : FourCover L) (w : I) : Subgroup PSL :=
  (residualProjection c w).range

noncomputable def residualProjectionEquiv (c : FourCover L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    residualIn (L := L) w ≃* projectedResidual c w :=
  MulEquiv.ofBijective (residualProjection c w).rangeRestrict
    ⟨fun _ _ h => residualProjection_injective c w e (congrArg Subtype.val h),
      (residualProjection c w).rangeRestrict_surjective⟩

theorem projectedResidual_card (c : FourCover L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    Nat.card (projectedResidual c w) = 9 :=
  (Nat.card_congr (residualProjectionEquiv c w e).symm.toEquiv).trans
    (residualIn_card w e)

@[expose] noncomputable def projectedResidualFixer (c : FourCover L) (w : I) :
    Subgroup (MulAut PSL) :=
  PSL3.OuterSolvable.standard F ⊓ fixingSubgroup (MulAut PSL) (projectedResidual c w : Set PSL)

@[expose] noncomputable def kernelProjectiveAction (c : FourCover L) (w : I) :
    (residualAction (L := L) w).ker →* MulAut PSL :=
  (projectiveAction L c).comp
    ((centralizerIn w).subtype.comp (residualAction (L := L) w).ker.subtype)

theorem kernelProjectiveAction_range_le (d : Overgroup L) (w : I) :
    (kernelProjectiveAction d.cover w).range ≤ projectedResidualFixer d.cover w := by
  rintro a ⟨x, rfl⟩
  constructor
  · rw [← d.full_action]
    exact ⟨x.val.val, rfl⟩
  · intro y
    obtain ⟨r, hr⟩ := y.property
    change projectiveAction L d.cover x.val.val y.val = y.val
    rw [← hr]
    change d.cover.toCover.autMap d.cover.ker_eq_center (MulAut.conjNormal x.val.val)
      (d.cover.toMonoidHom (residualToLinear w r)) = _
    rw [d.cover.toCover.autMap_apply]
    change d.cover.toMonoidHom ((MulAut.conjNormal x.val.val) (residualToLinear w r)) =
      d.cover.toMonoidHom (residualToLinear w r)
    apply congrArg d.cover.toMonoidHom
    apply Subtype.ext
    have hx := congrArg (fun a : MulAut (residualIn (L := L) w) =>
      ((a r).val.val : I)) x.property
    exact hx

/-- The residual identification uses the actual covering projection. -/
theorem residualProjectionEquiv_apply (c : FourCover L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine)
    (r : residualIn (L := L) w) :
    (residualProjectionEquiv c w e r : PSL) = residualProjection c w r := by rfl

/-- Actual conjugation and the projective action agree on every residual element. -/
theorem residualProjection_conjugation (c : FourCover L) (w : I)
    (x : centralizerIn w) (r : residualIn (L := L) w) :
    residualProjection c w (residualAction w x r) =
      projectiveAction L c (x : I) (residualProjection c w r) := by
  change c.toMonoidHom (residualToLinear w (residualAction w x r)) =
    c.toCover.autMap c.ker_eq_center (MulAut.conjNormal (x : I))
      (c.toMonoidHom (residualToLinear w r))
  rw [c.toCover.autMap_apply]
  rfl

/-- The residual-action kernel can be tested after its faithful projection. -/
theorem mem_residualAction_ker_iff_projective_fixes (c : FourCover L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine)
    (x : centralizerIn w) :
    x ∈ (residualAction (L := L) w).ker ↔
      ∀ r : residualIn (L := L) w,
        projectiveAction L c (x : I) (residualProjection c w r) = residualProjection c w r := by
  constructor
  · intro hx r
    rw [← residualProjection_conjugation]
    change residualAction w x = 1 at hx
    rw [hx]
    rfl
  · intro hx
    change residualAction w x = 1
    apply MulEquiv.ext
    intro r
    apply residualProjection_injective c w e
    rw [residualProjection_conjugation]
    exact hx r

/-- The full overgroup projective kernel has order four. -/
theorem projectiveAction_ker_card (d : Overgroup L) :
    Nat.card (projectiveAction L d.cover).ker = 4 := by
  rw [d.projectiveAction_ker, card_map_of_injective L.subtype_injective]
  let := d.cover.center_isKleinFour
  exact IsKleinFour.card_four

/-- The kernel of projective descent inside the residual-action kernel is
still a subgroup of the actual central four. -/
theorem kernelProjectiveAction_ker_card_dvd (d : Overgroup L) (w : I) :
    Nat.card (kernelProjectiveAction d.cover w).ker ∣ 4 := by
  let j : (kernelProjectiveAction d.cover w).ker →* (projectiveAction L d.cover).ker := {
    toFun x := ⟨x.val.val.val, x.property⟩
    map_one' := by rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y h
    have hv : x.val.val.val = y.val.val.val := congrArg (fun a : (projectiveAction L d.cover).ker => (a : I)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext hv))
  simpa only [projectiveAction_ker_card d] using card_dvd_of_injective j hj

/-- A projective pointwise-fixer bound suffices for the two-kernel assertion.
This separates the finite-group transfer from the still required matrix calculation. -/
theorem kernel_quotient_two_of_projectedFixer_card_dvd
    (d : Overgroup L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine)
    (hfix : Nat.card (projectedResidualFixer d.cover w) ∣ 18) :
    IsPGroup 2 (residualActionKernelQuotient (L := L) w) := by
  let f := kernelProjectiveAction d.cover w
  have hr : Nat.card f.range ∣ 18 :=
    (card_dvd_of_le (kernelProjectiveAction_range_le d w)).trans hfix
  have hk : Nat.card (residualAction (L := L) w).ker ∣ 72 := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Nat.mul_dvd_mul hr (kernelProjectiveAction_ker_card_dvd d w)
  have hR : Nat.card ((residualIn (L := L) w).subgroupOf
      (residualAction (L := L) w).ker) = 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (residualIn_le_actionKernel w e)).toEquiv]
    exact residualIn_card w e
  rw [card_eq_card_quotient_mul_card_subgroup
    ((residualIn (L := L) w).subgroupOf (residualAction (L := L) w).ker), hR] at hk
  apply IsPGroup.of_card_dvd_pow (n := 3)
  apply Nat.dvd_of_mul_dvd_mul_left (k := 9) (by decide)
  simpa [Nat.mul_comm] using hk

/-- The faithful image of the residual is an actual Sylow three-subgroup of PSL₃(4). -/
noncomputable def projectedResidualSylow (c : FourCover L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    Sylow 3 PSL := Sylow.ofCard (projectedResidual c w) (by
      rw [projectedResidual_card c w e, Matrix.PSL3Four.card_PSL]
      decide +kernel)
theorem projectedResidualSylow_coe (c : FourCover L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    (projectedResidualSylow c w e : Subgroup PSL) = projectedResidual c w := by
  exact Sylow.coe_ofCard _ _

end Matrix.PSL3Four.ExtendedCentralizer
