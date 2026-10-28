module
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.ScalarCentralizer
public import Theory.SpecificGroups.SL2.SylowTorusAutomorphisms
public import Theory.Representation.FixedFieldRestriction
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Odd field coefficients of linear Hermitian normalizers

Every coefficient automorphism of the quadratic finite field acts entrywise
on the Hermitian matrices and restricts to the defining fixed field. After
removing this canonical lift and the inner matrix action, an arbitrary lift
centralizes SL₂, hence is a scalar by the existing commutant calculation.
If the original lift is linear over the defining field, the coefficient fixes
that field. It belongs to the quadratic Galois group, and odd order forces it
to be trivial.

This supplies the extension-field step in the orthogonal central Hall branch
of Aschbacher--Smith 10.2.3, printed p.745. Both the matrix automorphism and
its module lift retain their literal actions.
-/

@[expose] public noncomputable section
open Matrix Matrix.SpecialLinearGroup BenderSuzuki.ZD.Linear
namespace Representation.OrthogonalFourMinus.RankOne.AmbientActions
open Representation.OrthogonalFourMinus.FiniteModel
variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem field_commutes_conjugation (σ : Field n ≃+* Field n) (x : Field n) :
    σ (conjugation n x) = conjugation n (σ x) := by
  change σ (x ^ (2^n)) = (σ x) ^ (2^n)
  exact map_pow σ x _

def fieldRestriction (σ : Field n ≃+* Field n) : fixedField n ≃+* fixedField n where
  toFun x := ⟨σ x, by
    change conjugation n (σ x) = σ x
    rw [←field_commutes_conjugation]
    exact congrArg _ x.property⟩
  invFun x := ⟨σ.symm x, by
    change conjugation n (σ.symm x) = σ.symm x
    rw [←field_commutes_conjugation]
    exact congrArg _ x.property⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add σ (x : Field n) (y : Field n))
  map_mul' x y := Subtype.ext (map_mul σ (x : Field n) (y : Field n))

def fieldLift (σ : Field n ≃+* Field n) : Space n ≃+ Space n where
  toFun X := ⟨X.val.map σ, by
    ext i j
    change conjugation n (σ (X.val j i)) = σ (X.val i j)
    rw [←field_commutes_conjugation, entry_conjugate]⟩
  invFun X := ⟨X.val.map σ.symm, by
    ext i j
    change conjugation n (σ.symm (X.val j i)) = σ.symm (X.val i j)
    rw [←field_commutes_conjugation, entry_conjugate]⟩
  left_inv X := by apply Subtype.ext; ext i j; exact σ.symm_apply_apply _
  right_inv X := by apply Subtype.ext; ext i j; exact σ.apply_symm_apply _
  map_add' X Y := by apply Subtype.ext; ext i j; exact map_add σ _ _

theorem fieldLift_smul (σ : Field n ≃+* Field n) (a : fixedField n) (X : Space n) :
    fieldLift n σ (a • X) = fieldRestriction n σ a • fieldLift n σ X := by
  apply Subtype.ext
  ext i j
  exact map_mul σ _ _

theorem fieldLift_action (σ : Field n ≃+* Field n)
    (g : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    fieldLift n σ (action n g X) = action n (sl2FieldAut σ g) (fieldLift n σ X) := by
  apply Subtype.ext
  ext i j
  change σ ((action n g X).val i j) = _
  simp only [action_apply, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
  change
    (σ (g.val i 0) * σ (X.val 0 0) + σ (g.val i 1) * σ (X.val 1 0)) *
        σ (conjugation n (g.val j 0)) +
      (σ (g.val i 0) * σ (X.val 0 1) + σ (g.val i 1) * σ (X.val 1 1)) *
        σ (conjugation n (g.val j 1)) = _
  simp only [field_commutes_conjugation]
  rfl

theorem linear_lift_coefficient_trivial
    (g : Matrix.SpecialLinearGroup (Fin 2) (Field n))
    (σ : Field n ≃+* Field n) (hodd : Odd (orderOf σ))
    (E : Space n ≃ₗ[fixedField n] Space n)
    (hE : ∀ a X, E (action n a X) =
      action n ((MulAut.conj g * sl2FieldAut σ) a) (E X)) : σ = 1 := by
  let a := MulAut.conj g * sl2FieldAut σ
  let e₀ : Space n ≃+ Space n := (fieldLift n σ).trans
    (LinearMap.GeneralLinearGroup.toLinearEquiv ((action n).asGroupHom g)).toAddEquiv
  have he₀ (b : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
      e₀ (action n b X) = action n (a b) (e₀ X) := by
    change action n g (fieldLift n σ (action n b X)) =
      action n (g * sl2FieldAut σ b * g⁻¹) (action n g (fieldLift n σ X))
    rw [fieldLift_action]
    simp only [←Module.End.mul_apply, ←map_mul]
    simp only [inv_mul_cancel_right]
  let f : Space n →+ Space n := e₀.symm.toAddMonoidHom.comp E.toAddMonoidHom
  obtain ⟨c,hc⟩ := commuting_addHom_eq_scalar n f (by
    intro b X
    apply e₀.injective
    change e₀ (e₀.symm (E (action n b X))) = e₀ (action n b (e₀.symm (E X)))
    rw [e₀.apply_symm_apply,he₀,e₀.apply_symm_apply]
    exact hE b X)
  have hform (X : Space n) : E X = e₀ (c • X) := by
    have hh := congrArg e₀ (hc X)
    change e₀ (e₀.symm (E X)) = _ at hh
    rwa [e₀.apply_symm_apply] at hh
  have hsemi (d : fixedField n) (X : Space n) :
      E (d • X) = fieldRestriction n σ d • E X := by
    rw [hform,hform]
    change action n g (fieldLift n σ (c • d • X)) =
      fieldRestriction n σ d • action n g (fieldLift n σ (c • X))
    rw [smul_comm c d,fieldLift_smul,map_smul]
  have hσ (d : fixedField n) : σ d = d := by
    let X : Space n := (coordinates n).symm ((1,0),0)
    have hX : X ≠ 0 := by
      intro he
      have hh := congrArg (fun Y : Space n => Y.val 0 0) he
      exact one_ne_zero hh
    have hEX : E X ≠ 0 := fun he => hX (E.injective (he.trans E.map_zero.symm))
    have he : fieldRestriction n σ d = d := smul_left_injective (fixedField n) hEX
      ((hsemi d X).symm.trans (E.map_smul d X))
    exact congrArg Subtype.val he
  have hm := Theory.FixedFieldRestriction.mem_zpowers_of_fixedField_fixed
    (conjugation n) σ (fun x hx => hσ ⟨x,hx⟩)
  have hpow : σ^2 = 1 := by
    obtain ⟨k,rfl⟩ := hm
    have h2 : conjugation n ^ 2 = 1 := by
      ext x
      exact conjugation_involutive n x
    rw [←zpow_natCast,←zpow_mul, mul_comm k, zpow_mul, zpow_natCast,h2,one_zpow]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right
    dvd_rfl (orderOf_dvd_of_pow_eq_one hpow))
theorem odd_linear_lift_inner
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) (Field n)))
    (ho : Odd (orderOf α)) (E : Space n ≃ₗ[fixedField n] Space n)
    (hE : ∀ a X, E (action n a X) = action n (α a) (E X)) :
    ∃ g, α = MulAut.conj g := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup
    (Matrix.SpecialLinearGroup (Fin 2) (Field n)))
  let f := q.comp (Atlas.RankOneFieldAutomorphisms.slFieldAction (F := Field n))
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro σ hσ
    change σ = 1
    obtain ⟨g,hg⟩ := (QuotientGroup.eq_one_iff _).mp (show q
      (Atlas.RankOneFieldAutomorphisms.slFieldAction σ) = 1 from hσ)
    exact Atlas.RankOneFieldAutomorphisms.field_eq_one_of_SL_inner σ g hg.symm
  obtain ⟨g,σ,hα⟩ := sl2_semilinear_coverage α
  have hq : q α = f σ := by
    rw [hα,map_mul]
    have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rw [hg,one_mul]
    rfl
  have hσodd : Odd (orderOf σ) := by
    rw [←orderOf_injective f hi σ,←hq]
    exact ho.of_dvd_nat (orderOf_map_dvd q α)
  have hσ := linear_lift_coefficient_trivial n g σ hσodd E (by simpa only [←hα] using hE)
  refine ⟨g,?_⟩
  rw [hα,hσ]
  have h1 : sl2FieldAut (1 : Field n ≃+* Field n) = 1 := by ext x i j; rfl
  rw [h1,mul_one]
end Representation.OrthogonalFourMinus.RankOne.AmbientActions

