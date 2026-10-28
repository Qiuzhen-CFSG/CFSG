module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FittingActions
public import Theory.GroupTheory.Fitting.Equiv
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Inversion in both nonquasisimple A.3.6 alternatives

An element of order two in the natural SL₂ quotient is the scalar -1,
so it inverts the full Fitting subgroup. Together with the proved
nilpotent Fitting inversion theorem, this gives full Frattini inversion
in both alternatives. The final transport is equivariant for original
conjugation, and retains every prime and higher homocyclic exponent.

Source: Aschbacher--Smith, A.3.6, pp.43--45, and the first paragraph
of the proof of 13.1.9, p.869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.FittingActions

private theorem sl2_scalar_involution {F : Type*} [Field F]
    (hF : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : orderOf x = 2) : x = -1 := by
  have hpow : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hd : (Matrix.SpecialLinearGroup.toGL x).det = 1 := by
    apply Units.ext
    exact x.property
  rcases Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
      (Matrix.SpecialLinearGroup.toGL x) (by rw [← map_pow, hpow, map_one]) hd with he | he
  · have hx1 : x = 1 := Matrix.SpecialLinearGroup.toGL_injective (by simpa using he)
    simp [hx1] at hx
  · exact Subtype.ext (congrArg Units.val he)

/-- The scalar involution in the natural A.3.6 quotient inverts the full Fitting section. -/
theorem natural_fitting_inversion {K : Type*} [Group K] [Finite K]
    (hn : A36Natural K) (t : K)
    (ht : orderOf (QuotientGroup.mk' (fittingSubgroup K) t) = 2)
    (x : fittingSubgroup K ⧸ frattini (fittingSubgroup K)) :
    FittingActions.fittingFrattiniAction K t x = x⁻¹ := by
  obtain ⟨p, hp, hp3, F, hF, hfin, hcard, v, e, hact⟩ := hn.2
  have hodd : Odd (Nat.card F) := hcard ▸
    hp.eq_two_or_odd'.resolve_left (by omega)
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F hodd
  let c := QuotientGroup.quotientMulEquivOfEq hn.1
  have horder : orderOf (QuotientGroup.mk' (generalizedFitting K) t) = 2 := by
    rw [← c.orderOf_eq]
    exact ht
  have he : e (QuotientGroup.mk' (generalizedFitting K) t) = -1 :=
    sl2_scalar_involution h2 _ ((e.orderOf_eq _).trans horder)
  have hconj (a : generalizedFitting K) :
      (⟨t * a * t⁻¹, (inferInstance : (generalizedFitting K).Normal).conj_mem
        a a.property t⟩ : generalizedFitting K) = a⁻¹ := by
    apply v.injective
    rw [hact, he, map_inv]
    change Multiplicative.ofAdd (Matrix.mulVec (-1 : Matrix (Fin 2) (Fin 2) F)
      (Multiplicative.toAdd (v a))) = (v a)⁻¹
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
    rfl
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (frattini (fittingSubgroup K)) x
  rw [FittingActions.fittingFrattiniAction_apply_mk, ← map_inv]
  congr 1
  apply Subtype.ext
  exact congrArg (fun z : generalizedFitting K => (z : K)) (hconj ⟨a, hn.1.symm ▸ a.property⟩)

/-- Inversion transports through an actual group isomorphism, with the full Fitting and Frattini subgroups. -/
theorem fitting_inversion_of_a36_equiv {K D : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] [Group D] [Finite D] (e : K ≃* D)
    (hs : A36Natural D ∨ A36Nilpotent D) (t : K)
    (ht : orderOf (QuotientGroup.mk' (fittingSubgroup K) t) = 2)
    (x : fittingSubgroup K ⧸ frattini (fittingSubgroup K)) :
    FittingActions.fittingFrattiniAction K t x = x⁻¹ := by
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let eF : fittingSubgroup K ≃* fittingSubgroup D :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_fitting_equiv e))
  let ePhi : (fittingSubgroup K ⧸ frattini (fittingSubgroup K)) ≃*
      (fittingSubgroup D ⧸ frattini (fittingSubgroup D)) :=
    QuotientGroup.congr _ _ eF (frattini_map_equiv eF)
  let eQ : (K ⧸ fittingSubgroup K) ≃* (D ⧸ fittingSubgroup D) :=
    QuotientGroup.congr _ _ e (map_fitting_equiv e)
  have het : orderOf (QuotientGroup.mk' (fittingSubgroup D) (e t)) = 2 :=
    (eQ.orderOf_eq (QuotientGroup.mk' (fittingSubgroup K) t)).trans ht
  have hi (y : fittingSubgroup D ⧸ frattini (fittingSubgroup D)) :
      FittingActions.fittingFrattiniAction D (e t) y = y⁻¹ := by
    rcases hs with hn | hn
    · exact natural_fitting_inversion hn _ het y
    · exact FittingActions.nilpotent_fitting_inversion hn _ het y
  have heq (y : fittingSubgroup K ⧸ frattini (fittingSubgroup K)) :
      ePhi (FittingActions.fittingFrattiniAction K t y) =
        FittingActions.fittingFrattiniAction D (e t) (ePhi y) := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (frattini (fittingSubgroup K)) y
    rw [FittingActions.fittingFrattiniAction_apply_mk]
    change QuotientGroup.mk' _ (eF (FittingActions.fittingAction K t a)) =
      FittingActions.fittingFrattiniAction D (e t) (QuotientGroup.mk' _ (eF a))
    rw [FittingActions.fittingFrattiniAction_apply_mk]
    congr 1
    apply Subtype.ext
    change e (t * a * t⁻¹) = e t * e a * (e t)⁻¹
    simp only [map_mul, map_inv]
  apply ePhi.injective
  rw [heq, hi, map_inv]

end CFSG.Quasithin.Chapter1.Section02.FittingActions
