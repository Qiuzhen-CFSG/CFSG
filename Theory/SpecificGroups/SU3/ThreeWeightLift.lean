module
public import Theory.SpecificGroups.SU3.CyclicNormalOuter.OddCoverage
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.SemilinearReduction
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.GroupTheory.PerfectCentralCoverExistence
/-!
# Two-power automorphisms of the actual projective unitary group

Over an odd prime field, the existing semilinear coverage of PSU₃ gives
unitary conjugation or unitary conjugation followed by field conjugation.
Both operations lift through the literal special-to-projective map. The
standard Hermitian equation identifies field conjugation with a conjugated
inverse transpose. Perfectness of SU₃ then forces the lifted automorphism
to satisfy every power relation satisfied by the projective automorphism.

The scalar kernel has order dividing the multiplicative field order, hence
is prime to the defining characteristic, including characteristic three.
These are precisely the inputs of the three-weight square argument used in
Aschbacher–Smith A.3.15 and 1.3.4; semilinear coverage is GLS3, 2.5.12.
-/

public section
open Matrix Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.ThreeWeightLift
open OddPrimeSylow.NormalizedOuter
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

private def unitarySpecialAut (u : J.unitarySubgroup) : MulAut J.specialSubgroup where
  toFun := J.specialUnitaryConj u
  invFun := J.specialUnitaryConj u⁻¹
  left_inv x := by apply Subtype.ext; simp [specialUnitaryConj_val,mul_assoc]
  right_inv x := by apply Subtype.ext; simp [specialUnitaryConj_val,mul_assoc]
  map_mul' x y := by apply Subtype.ext; simp [specialUnitaryConj_val,mul_assoc]

private theorem unitarySpecialAut_val (u : J.unitarySubgroup) (x : J.specialSubgroup) :
    (unitarySpecialAut J u x).val=u.val*x.val*u.val⁻¹ := J.specialUnitaryConj_val u x

private theorem unitarySpecialAut_compat (u : J.unitarySubgroup) (x : J.specialSubgroup) :
    J.specialToProjective (unitarySpecialAut J u x)=J.unitaryConj u (J.specialToProjective x) :=
  (J.unitaryConj_specialToProjective u x).symm

private def gram : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero J.form J.form_nondegenerate

private theorem gram_sq (hJ : J.form=!![0,0,1;0,1,0;1,0,0]) : gram J * gram J=1 := by
  apply Units.ext
  change J.form*J.form=1
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem gram_inverse (hJ : J.form=!![0,0,1;0,1,0;1,0,0]) : (gram J).inv=J.form := by
  have hh : (gram J)⁻¹=gram J := inv_eq_of_mul_eq_one_left (gram_sq J hJ)
  exact congrArg Units.val hh

private theorem entrywise_dual (hJ : J.form=!![0,0,1;0,1,0;1,0,0]) (x : J.specialSubgroup) :
    x.val.val.map J.conj = J.form*x.val.inv.transpose*J.form := by
  have hx := ((J.mem_specialSubgroup_iff x.val).mp x.property).1
  change (x.val.val.map J.conj).transpose*J.form*x.val.val=J.form at hx
  have hg : J.form*J.form=1 := congrArg Units.val (gram_sq J hJ)
  have ht : J.form.transpose=J.form := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) F=>A*x.val.inv*J.form) hx
  have he : (x.val.val.map J.conj).transpose=J.form*x.val.inv*J.form := by
    simpa only [Matrix.mul_assoc,Units.val_inv,Matrix.mul_one,hg] using hh
  have h := congrArg Matrix.transpose he
  simpa only [Matrix.transpose_transpose,Matrix.transpose_mul,ht,Matrix.mul_assoc] using h

private theorem lift_pow_eq_one [Group.IsPerfect J.specialSubgroup]
    (α : MulAut J.specialSubgroup) (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hc : ∀x,J.specialToProjective (α x)=β (J.specialToProjective x))
    (r : ℕ) (hr : β^r=1) : α^r=1 := by
  have hp (n : ℕ) (x : J.specialSubgroup) :
      J.specialToProjective ((α^n) x)=(β^n) (J.specialToProjective x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ',MulAut.mul_apply,hc,ih]
  have hh : (α^r).toMonoidHom=(1:MulAut J.specialSubgroup).toMonoidHom := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
      J.specialToProjective J.specialToProjective_ker_le_center
    apply MonoidHom.ext
    intro x
    change J.specialToProjective ((α^r) x)=J.specialToProjective x
    rw [hp,hr]
    rfl
  exact MulEquiv.ext (fun x=>DFunLike.congr_fun hh x)

variable [Finite F]

/-- The actual lift has the same two-power order and an actual linear or dual formula. -/
theorem exists_lift
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (hcard : Nat.card F=q^2) (hfixed : Nat.card {x:F // J.conj x=x}=q)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (n : ℕ) (hβ : β^(2^n)=1) :
    ∃α:MulAut J.specialSubgroup,
      (∀x,J.specialToProjective (α x)=β (J.specialToProjective x)) ∧ α^(2^n)=1 ∧
      ∃g:GL (Fin 3) F,
        (∀x,(α x).val=g*x.val*g⁻¹) ∨
        (∀x,(α x).val.val=g.val*x.val.inv.transpose*g.inv) := by
  have hq2 : 2<q := by obtain ⟨r,hr⟩:=ho; have hh:=hq.two_le; omega
  let : Group.IsPerfect J.specialSubgroup := J.special_isPerfect_of_fixed_card hq2 hcard hfixed
  obtain ⟨σ,hσ⟩ := Coverage.semilinear_coverage_odd J hJ hq ho hcard hfixed β
  rcases fieldAut_eq_one_or_conj J hq hcard hfixed σ with he | he
  · subst σ
    obtain ⟨u,hu⟩ := (HasUnitarySemilinearForm.one_iff J).mp hσ
    have hc : ∀x,J.specialToProjective (unitarySpecialAut J u x)=β (J.specialToProjective x) := by
      intro x
      rw [hu]
      exact unitarySpecialAut_compat J u x
    exact ⟨unitarySpecialAut J u,hc,lift_pow_eq_one J _ β hc (2^n) hβ,
      u.val,Or.inl (unitarySpecialAut_val J u)⟩
  · rw [he] at hσ
    obtain ⟨u,hu⟩ := (HasUnitarySemilinearForm.conj_iff J
      (entrywiseProjectiveAut_isEntrywiseConjugation J hJ)).mp hσ
    let α := unitarySpecialAut J u * entrywiseSpecialAut J hJ
    have hc : ∀x,J.specialToProjective (α x)=β (J.specialToProjective x) := by
      intro x
      rw [hu]
      change J.specialToProjective (unitarySpecialAut J u (entrywiseSpecialAut J hJ x))=
        J.unitaryConj u (entrywiseProjectiveAut J hJ (J.specialToProjective x))
      rw [unitarySpecialAut_compat,entrywiseProjectiveAut_specialToProjective]
    refine ⟨α,hc,lift_pow_eq_one J α β hc (2^n) hβ,u.val*gram J,Or.inr ?_⟩
    intro x
    change (unitarySpecialAut J u (entrywiseSpecialAut J hJ x)).val.val=_
    rw [unitarySpecialAut_val]
    change u.val.val*(entrywiseSpecialAut J hJ x).val.val*u.val.inv=_
    rw [entrywiseSpecialAut_apply_val,entrywise_dual J hJ]
    change u.val.val*(J.form*x.val.inv.transpose*J.form)*u.val.inv=
      (u.val.val*(gram J).val)*x.val.inv.transpose*((gram J).inv*u.val.inv)
    rw [gram_inverse J hJ]
    change u.val.val*(J.form*x.val.inv.transpose*J.form)*u.val.inv=
      (u.val.val*J.form)*x.val.inv.transpose*(J.form*u.val.inv)
    simp only [Matrix.mul_assoc]
omit [Finite F] in
/-- The literal scalar kernel has order prime to the defining characteristic. -/
theorem kernel_card_cast_ne_zero {q : ℕ} [CharP F q]
    (hq : q.Prime) (hcard : Nat.card F = q^2) :
    (Nat.card J.specialToProjective.ker : F) ≠ 0 := by
  let f : J.specialToProjective.ker →* center (GL (Fin 3) F) :=
    (J.specialSubgroup.subtype.comp J.specialToProjective.ker.subtype).codRestrict
      (center (GL (Fin 3) F)) (fun x => by
        change x.val.val ∈ center (GL (Fin 3) F)
        apply ProjGenLinGroup.mk_eq_one.mp
        simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
          congrArg Subtype.val (MonoidHom.mem_ker.mp x.property))
  have hf : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : center (GL (Fin 3) F) => z.val) hh
  have hd : Nat.card J.specialToProjective.ker ∣ Nat.card Fˣ := by
    apply (Subgroup.card_dvd_of_injective f hf).trans
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact Subgroup.card_range_dvd (GeneralLinearGroup.scalar (Fin 3))
  rw [Nat.card_units,hcard] at hd
  rw [ne_eq, CharP.cast_eq_zero_iff F q]
  intro hh
  have hdiv := hh.trans hd
  have hp : q ∣ q^2 := dvd_pow_self q (by decide : 2 ≠ 0)
  have hle : 1 ≤ q^2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hq.ne_zero)
  have hdone : q ∣ 1 := (Nat.dvd_sub_iff_right hle hp).mp hdiv
  exact hq.not_dvd_one hdone

end BenderSuzuki.MatrixGroups.HermitianForm.ThreeWeightLift
