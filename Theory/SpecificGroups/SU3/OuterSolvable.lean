module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Semilinear
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Solvability of the outer group of projective SU₃

Unitary conjugation gives a homomorphism from `U(J)` into `Aut(PSU(J))`.
The determinant of a unitary commutator is one, so commutators of these
conjugations are inner. This is the abelian diagonal quotient needed here.

For the antidiagonal form over a finite field, assume each automorphism has
an actual unitary-semilinear formula. The formulas are closed under inverses
by finiteness and under products by the existing composition theorem.
Field automorphisms commute, so an automorphism commutator has trivial
field part and is a unitary conjugation. Thus the second derived subgroup
of the automorphism group is inner and the actual outer quotient is
metabelian. No uniqueness of field parts or splitting is needed.

Source: GLS3, Theorem 2.5.12(c,d,f) and Section 2.7's matrix identification
of `Inndiag(PSU₃(q))` with `PGU₃(q)` (`refs/KGroup/GLS3/chapter2.tex`).
Semilinear coverage is an explicit hypothesis, proved separately.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm
open scoped commutatorElement
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The homomorphism induced by unitary conjugation on the actual projective image. -/
public def unitaryConjHom : J.unitarySubgroup →*
    MulAut (ProjectiveSpecialUnitaryMatrixGroup J) where
  toFun := J.unitaryConj
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp [J.unitaryConj_apply_val]
  map_mul' u v := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (J.unitaryConj (u * v) x).val = (J.unitaryConj u (J.unitaryConj v x)).val
    simp [J.unitaryConj_apply_val, map_mul, mul_assoc]

/-- The conjugation homomorphism has the specified unitary action. -/
@[simp] public theorem unitaryConjHom_apply (u : J.unitarySubgroup) :
    J.unitaryConjHom u = J.unitaryConj u := by rfl

/-- A determinant-one unitary conjugation is conjugation by its projective image. -/
public theorem unitaryConj_special_is_inner (x : J.specialSubgroup) :
    J.unitaryConj ⟨x.val, x.property.1⟩ = MulAut.conj (J.specialToProjective x) := by
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  change (J.unitaryConj _ b).val =
    (J.specialToProjective x).val * b.val * ((J.specialToProjective x).val)⁻¹
  rw [J.unitaryConj_apply_val, J.specialToProjective_apply_val]

/-- The unitary diagonal quotient is abelian: commutators of unitary conjugations are inner. -/
public theorem unitaryConj_commutator_is_inner (u v : J.unitarySubgroup) :
    ⁅J.unitaryConj u, J.unitaryConj v⁆ ∈
      MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let x : J.specialSubgroup := ⟨(⁅u, v⁆ : J.unitarySubgroup).val,
    (⁅u, v⁆ : J.unitarySubgroup).property, by
      change Matrix.GeneralLinearGroup.det (u.val * v.val * u.val⁻¹ * v.val⁻¹) = 1
      simp [map_mul, map_inv]⟩
  refine ⟨J.specialToProjective x, ?_⟩
  rw [← unitaryConj_special_is_inner]
  exact map_commutatorElement (J.unitaryConjHom) u v

/-- Inverting a semilinear formula inverts its field part. -/
public theorem HasUnitarySemilinearForm.inv [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} {σ : E ≃+* E}
    (ha : J.HasUnitarySemilinearForm a σ) :
    J.HasUnitarySemilinearForm a⁻¹ σ⁻¹ := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Finite (E ≃+* E) := Finite.of_injective (fun τ : E ≃+* E => (τ : E → E))
    DFunLike.coe_injective
  let : Finite (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Finite.of_injective
      (fun b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) =>
        (b : ProjectiveSpecialUnitaryMatrixGroup J → ProjectiveSpecialUnitaryMatrixGroup J))
      DFunLike.coe_injective
  have hp (n : ℕ) : J.HasUnitarySemilinearForm (a ^ n) (σ ^ n) := by
    induction n with
    | zero =>
      simp only [pow_zero]
      apply (HasUnitarySemilinearForm.one_iff J).2
      exact ⟨1, (J.unitaryConjHom.map_one).symm⟩
    | succ n ih => simpa only [pow_succ] using ih.mul J hJ ha
  let x := (a, σ)
  have hx : x ^ (orderOf x - 1) = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  have ha' : a ^ (orderOf x - 1) = a⁻¹ := congrArg Prod.fst hx
  have hσ' : σ ^ (orderOf x - 1) = σ⁻¹ := congrArg Prod.snd hx
  simpa only [ha', hσ'] using hp (orderOf x - 1)

/-- Semilinear coverage makes the actual outer quotient metabelian. -/
public theorem outer_derivedSeries_two_eq_bot_of_semilinear_coverage [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    derivedSeries (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) 2 = ⊥ := by
  let := finiteFieldAut_isCyclic (E := E)
  let := IsCyclic.commGroup (α := E ≃+* E)
  have hcomm : commutator (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      J.unitaryConjHom.range := by
    apply Subgroup.commutator_le.2
    intro a _ b _
    obtain ⟨σ, ha⟩ := hcoverage a
    obtain ⟨τ, hb⟩ := hcoverage b
    have h := ((ha.mul J hJ hb).mul J hJ (ha.inv J hJ)).mul J hJ (hb.inv J hJ)
    have hh : J.HasUnitarySemilinearForm ⁅a, b⁆ 1 := by
      simpa [commutatorElement_def, mul_comm, mul_left_comm, mul_assoc] using h
    obtain ⟨u, hu⟩ := (HasUnitarySemilinearForm.one_iff J).1 hh
    exact ⟨u, hu.symm⟩
  have hinner : ⁅J.unitaryConjHom.range, J.unitaryConjHom.range⁆ ≤
      MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
    apply Subgroup.commutator_le.2
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact J.unitaryConj_commutator_is_inner u v
  have hderived : derivedSeries (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) 2 ≤
      MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (Subgroup.commutator_mono hcomm hcomm).trans hinner
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective
    (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))), Subgroup.map_eq_bot_iff]
  simpa only [QuotientGroup.ker_mk'] using hderived

/-- The actual outer quotient is solvable under unitary-semilinear coverage. -/
public theorem outer_isSolvable_of_semilinear_coverage [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    Group.IsSolvable (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  ⟨⟨2, J.outer_derivedSeries_two_eq_bot_of_semilinear_coverage hJ hcoverage⟩⟩

end BenderSuzuki.MatrixGroups.HermitianForm
