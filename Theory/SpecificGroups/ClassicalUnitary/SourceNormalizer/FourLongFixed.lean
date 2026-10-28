module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOuterFixed
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularFixed

/-!
# Invariant long-root lines under outer unitary involutions

The actual additive lift of an outer involution is conjugate, by an inner
Hermitian action, to quadratic field conjugation. It is therefore linear
over the defining field. On an invariant line its square-one identity
forces its scalar to be one in characteristic two. The common fixed space
of a specified inner Sylow is such a line, with dimension obtained from
the exact fixed-space cardinality.

The prepared consumer identifies that line with the original right-residual
center and proves that every outer Sylow involution centralizes it.
Conversely, pointwise fixation of any nonzero defining-field line forces
the square of the quotient automorphism to be inner, by scalar rigidity
and the quadratic fixed-field theorem.
Source: Aschbacher–Smith F.4.29(7),37, printed pp.289,293, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Matrix Matrix.SpecialLinearGroup
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne.AmbientActions
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongFixed
variable (m : ℕ) [NeZero m]

/-- An involutory outer lift fixing an invariant line setwise fixes it pointwise. -/
theorem outer_fixes_line
    (α : MulAut (SpecialLinearGroup (Fin 2) (Field m))) (hα : α^2=1)
    (hout : ¬ ∃ g, α=MulAut.conj g)
    (E : Space m ≃+ Space m) (hE2 : Function.Involutive E)
    (hE : ∀ g x, E (action m g x)=action m (α g) (E x))
    (U : Submodule (fixedField m) (Space m)) (hU : Module.finrank (fixedField m) U=1)
    (hstable : ∀ x ∈ U, E x ∈ U) : ∀ x ∈ U, E x=x := by
  obtain ⟨c,hc⟩ := FourOuterFixed.outer_lift_conjugation m α hα hout E hE2 hE
  have hlinear (a : fixedField m) (x : Space m) : E (a • x)=a • E x := by
    let y := action m c⁻¹ x
    have hy : action m c y=x := Representation.self_inv_apply _ _ _
    rw [←hy,←map_smul,hc,map_smul,map_smul,hc]
  intro x hx
  by_cases hz : x=0
  · rw [hz,E.map_zero]
  let v : U := ⟨x,hx⟩
  obtain ⟨a,ha⟩ := exists_smul_eq_of_finrank_eq_one hU
    (show v ≠ 0 from fun hh => hz (congrArg Subtype.val hh)) (⟨E x,hstable x hx⟩ : U)
  have he : E x=a • x := (congrArg Subtype.val ha).symm
  have ha2 : a*a=1 := smul_left_injective (fixedField m) hz (by
    change (a*a) • x=(1 : fixedField m) • x
    calc
      (a*a) • x = a • (a • x) := mul_smul _ _ _
      _ = E (E x) := by rw [he,hlinear,he]
      _ = (1 : fixedField m) • x := by rw [hE2,one_smul])
  have ha1 : a=1 := by
    rcases sq_eq_one_iff.mp (by simpa only [pow_two] using ha2) with ha | ha
    · exact ha
    · simpa only [CharTwo.neg_eq] using ha
  rw [he,ha1,one_smul]

/-- The common fixed space of a specified inner Sylow is one-dimensional. -/
theorem sylow_fixed_finrank
    (P : Sylow 2 (SpecialLinearGroup (Fin 2) (Field m))) :
    Module.finrank (fixedField m) (Representation.invariants ((action m).comp (P : Subgroup _).subtype))=1 := by
  let U := Representation.invariants ((action m).comp (P : Subgroup _).subtype)
  let e : U ≃ {X : Space m // ∀ g ∈ (P : Subgroup _), action m g X=X} :=
    { toFun x := ⟨x.val,fun g hg => x.property ⟨g,hg⟩⟩
      invFun x := ⟨x.val,fun g => x.property g.val g.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hcard : Nat.card U=2^m :=
    (Nat.card_congr e).trans (FourSingularFixed.sylow_fixed_card m P)
  have hh := Module.natCard_eq_pow_finrank (K := fixedField m) (V := U)
  rw [card_fixedField,hcard] at hh
  exact Nat.pow_right_injective (Nat.one_lt_pow (NeZero.ne m) (by decide))
    (hh.symm.trans (pow_one (2^m)).symm)

/-- Fixing one nonzero defining-field line pointwise forces the square of
the component automorphism to be inner. Additional field actors are retained. -/
theorem square_inner_of_fixed_line
    (α : MulAut (SpecialLinearGroup (Fin 2) (Field m)))
    (E : Space m ≃+ Space m)
    (hE : ∀ g x, E (action m g x)=action m (α g) (E x))
    (X : Space m) (hne : X ≠ 0) (hfix : ∀ a : fixedField m, E (a • X)=a • X) :
    ∃ g, α^2=MulAut.conj g := by
  obtain ⟨g,σ,hα⟩ := Matrix.SpecialLinearGroup.sl2_semilinear_coverage α
  let e₀ : Space m ≃+ Space m := (fieldLift m σ).trans
    (LinearMap.GeneralLinearGroup.toLinearEquiv ((action m).asGroupHom g)).toAddEquiv
  have he₀ (b : SpecialLinearGroup (Fin 2) (Field m)) (x : Space m) :
      e₀ (action m b x)=action m (α b) (e₀ x) := by
    rw [hα]
    change action m g (fieldLift m σ (action m b x)) =
      action m (g * BenderSuzuki.ZD.Linear.sl2FieldAut σ b * g⁻¹)
        (action m g (fieldLift m σ x))
    rw [fieldLift_action]
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  let F : Space m →+ Space m := e₀.symm.toAddMonoidHom.comp E.toAddMonoidHom
  obtain ⟨c,hc⟩ := commuting_addHom_eq_scalar m F (by
    intro b x
    apply e₀.injective
    change e₀ (e₀.symm (E (action m b x)))=e₀ (action m b (e₀.symm (E x)))
    rw [e₀.apply_symm_apply,he₀,e₀.apply_symm_apply,hE])
  have hform (x : Space m) : E x=e₀ (c • x) := by
    have hh := congrArg e₀ (hc x)
    change e₀ (e₀.symm (E x))=_ at hh
    rwa [e₀.apply_symm_apply] at hh
  have hsemi (a : fixedField m) (x : Space m) :
      E (a • x)=fieldRestriction m σ a • E x := by
    rw [hform,hform]
    change action m g (fieldLift m σ (c • a • x)) =
      fieldRestriction m σ a • action m g (fieldLift m σ (c • x))
    rw [smul_comm c a,fieldLift_smul,map_smul]
  have hEX : E X=X := by simpa only [one_smul] using hfix 1
  have hσ (a : fixedField m) : σ a=a := by
    have hh := hsemi a X
    rw [hfix,hEX] at hh
    exact congrArg Subtype.val (smul_left_injective (fixedField m) hne hh.symm)
  have hm := Theory.FixedFieldRestriction.mem_zpowers_of_fixedField_fixed
    (conjugation m) σ (fun x hx => hσ ⟨x,hx⟩)
  have hσ2 : σ^2=1 := by
    obtain ⟨k,rfl⟩ := hm
    have h2 : conjugation m ^ 2=1 := by ext x; exact conjugation_involutive m x
    rw [←zpow_natCast,←_root_.zpow_mul,mul_comm k,_root_.zpow_mul,zpow_natCast,h2,_root_.one_zpow]
  have hs (x : SpecialLinearGroup (Fin 2) (Field m)) :
      BenderSuzuki.ZD.Linear.sl2FieldAut σ (BenderSuzuki.ZD.Linear.sl2FieldAut σ x)=x := by
    ext i j
    exact DFunLike.congr_fun hσ2 (x.val i j)
  refine ⟨g * BenderSuzuki.ZD.Linear.sl2FieldAut σ g,?_⟩
  rw [pow_two,hα]
  apply MulEquiv.ext
  intro x
  change g * BenderSuzuki.ZD.Linear.sl2FieldAut σ (g * BenderSuzuki.ZD.Linear.sl2FieldAut σ x * g⁻¹) * g⁻¹ =
    (g * BenderSuzuki.ZD.Linear.sl2FieldAut σ g)*x*(g * BenderSuzuki.ZD.Linear.sl2FieldAut σ g)⁻¹
  rw [map_mul,map_mul,map_inv,hs]
  group

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongFixed
