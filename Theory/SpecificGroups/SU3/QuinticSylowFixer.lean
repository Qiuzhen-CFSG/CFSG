module
public import Theory.SpecificGroups.PSU3.SylowFixedInvertedRoot
public import Theory.SpecificGroups.SU3.OddPrimeRootConfiguration
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.Representation.ExtraspecialQuinticActor

/-!
# Quintic root displacement for SU₃(5) Sylow fixers

The sign involution moves the actual Hermitian root group of order 125.
Its coordinates have exponent five, so it is an extraspecial group to
which the binary displacement bound of eight applies. A Sylow-fixing
involution descends to an inner projective involution. Projective fusion,
lifting a conjugator and faithfulness of the central-quotient action
identify it with a conjugate of the same special-unitary sign action.
An actual change of Hermitian basis handles every stored form.

The final theorem keeps the ambient faithful representation, embedding
and prescribed conjugating actor. It requires no chosen constituent or
representation classification. Source: Aschbacher--Smith 12.6.26, printed
p.832, using the quintic calculation of G.7.1(2).
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.QuinticSylowFixer
open OddPrimeSylow.NormalizedOuter.Coverage
open OddPrimeSylow.NormalizedOuter
variable {F : Type*} [Field F] (J : HermitianForm 3 F)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private def rootEquiv : hermitianUnipotentCoord J ≃* rootGroup J hJ :=
  MulEquiv.ofBijective (root J hJ).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (root_injective J hJ),
      (root J hJ).rangeRestrict_surjective⟩

private theorem coord_pow_five [CharP F 5] (x : hermitianUnipotentCoord J) : x ^ 5 = 1 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
  apply Subtype.ext
  apply Prod.ext
  · change x.val.1 + x.val.1 + x.val.1 + x.val.1 + x.val.1 = 0
    linear_combination (CharP.cast_eq_zero F 5) * x.val.1
  · change (((x.val.2 + x.val.2 - x.val.1 * J.conj x.val.1) + x.val.2 -
      (x.val.1 + x.val.1) * J.conj x.val.1) + x.val.2 -
      (x.val.1 + x.val.1 + x.val.1) * J.conj x.val.1) + x.val.2 -
      (x.val.1 + x.val.1 + x.val.1 + x.val.1) * J.conj x.val.1 = 0
    linear_combination (CharP.cast_eq_zero F 5) * (x.val.2 - 2*x.val.1*J.conj x.val.1)

private def signAction : MulAut (hermitianUnipotentCoord J) where
  toFun x := ⟨(-x.val.1,x.val.2), by simpa using x.property⟩
  invFun x := ⟨(-x.val.1,x.val.2), by simpa using x.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    apply Prod.ext
    · exact neg_add _ _
    · change x.val.2 + y.val.2 - x.val.1 * J.conj y.val.1 =
        x.val.2 + y.val.2 - (-x.val.1) * J.conj (-y.val.1)
      simp

private theorem signAction_ne_one [CharP F 5] : signAction J ≠ 1 := by
  let x : hermitianUnipotentCoord J := ⟨(2,-2),by
    change (-2:F) + J.conj (-2) + 2 * J.conj 2 = 0
    simp only [map_neg,map_ofNat]
    ring⟩
  intro h
  have he := congrArg (fun f : MulAut (hermitianUnipotentCoord J) => (f x).val.1) h
  change -(2:F) = 2 at he
  have hz : (4:F)=0 := by linear_combination -he
  have hd := (CharP.cast_eq_zero_iff F 5 4).mp hz
  norm_num at hd

private theorem special_root_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro x y he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : J.specialSubgroup => z.val.val 0 1) he
  · exact congrArg (fun z : J.specialSubgroup => z.val.val 0 2) he

private theorem sign_root_conjugation (x : hermitianUnipotentCoord J) :
    hermitianUnipotentSU J hJ (signAction J x) =
      hermitianTorusSU J hJ (-1) * hermitianUnipotentSU J hJ x *
        (hermitianTorusSU J hJ (-1))⁻¹ := by
  apply Subtype.ext
  have he : hermitianTorusAction J (-1) x = signAction J x := by
    apply Subtype.ext
    apply Prod.ext <;> simp [hermitianTorusAction_fst,hermitianTorusAction_snd,signAction]
  have hh := hermitianTorusGL_mul_unipotent J (-1) x
  rw [he] at hh
  exact (eq_mul_inv_iff_mul_eq.mpr hh.symm)

/-- Every conjugate of the sign involution moves a literal exponent-five
extraspecial subgroup of order 125 in the special unitary group. -/
theorem sign_conjugate_moves_root [Finite F] [CharP F 5]
    (hF : Nat.card F = 5 ^ 2) (hf : Nat.card {x : F // J.conj x = x} = 5)
    (g : J.specialSubgroup) :
    ∃ Y : Subgroup J.specialSubgroup, IsExtraspecial 5 Y ∧ Nat.card Y = 125 ∧
      (∀ y : Y, y ^ 5 = 1) ∧ ∃ b : MulAut Y, b ≠ 1 ∧
        ∀ y : Y, (b y : J.specialSubgroup) =
          (g * hermitianTorusSU J hJ (-1) * g⁻¹) * y.val *
            (g * hermitianTorusSU J hJ (-1) * g⁻¹)⁻¹ := by
  let e := rootEquiv J hJ
  let : IsExtraspecial 5 (hermitianUnipotentCoord J) :=
    (OddPrimeRootConfiguration.rootGroup_isExtraspecial J hJ (by decide) hF hf).of_mulEquiv e.symm
  let j := (MulAut.conj g).toMonoidHom.comp (hermitianUnipotentSU J hJ)
  have hj : Function.Injective j := (MulAut.conj g).injective.comp (special_root_injective J hJ)
  let er : hermitianUnipotentCoord J ≃* j.range :=
    MulEquiv.ofBijective j.rangeRestrict ⟨MonoidHom.rangeRestrict_injective_iff.mpr hj,j.rangeRestrict_surjective⟩
  refine ⟨j.range,IsExtraspecial.of_mulEquiv er inferInstance,?_,?_,MulAut.congr er (signAction J),?_,?_⟩
  · rw [←Nat.card_congr er.toEquiv,Nat.card_congr e.toEquiv]
    exact rootGroup_card J hJ 5 hF hf
  · intro y
    obtain ⟨x,rfl⟩ := er.surjective y
    rw [←map_pow,coord_pow_five,map_one]
  · intro hb
    apply signAction_ne_one J
    exact (MulAut.congr er).injective (hb.trans (map_one _).symm)
  · intro y
    obtain ⟨x,rfl⟩ := er.surjective y
    change (er (signAction J (er.symm (er x))) : J.specialSubgroup) = _
    rw [er.symm_apply_apply]
    change j ((signAction J) x) = _
    change (MulAut.conj g) (hermitianUnipotentSU J hJ (signAction J x)) = _
    rw [sign_root_conjugation,map_mul,map_mul,map_inv]
    rfl


/-- A nonidentity involutory Sylow fixer is a conjugate of the literal sign action. -/
theorem sylow_fixer_is_sign_conjugation [Finite F]
    (hF : Nat.card F = 5 ^ 2) (hc : ∀ x, J.conj x = x ^ 5)
    (P : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    (ha : orderOf a = 2) (hP : ∀ x ∈ P, a x = x) :
    ∃ g : J.specialSubgroup,
      a = MulAut.conj (g * hermitianTorusSU J hJ (-1) * g⁻¹) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : DivisionMonoid (ProjectiveSpecialUnitaryMatrixGroup J) :=
    @Group.toDivisionMonoid _ inferInstance
  have hf : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 5 1
      (by decide) (by simpa using hF) (by simpa using hc)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J 5 (by decide) hF hf
  let := J.projective_isPerfect_of_fixed_card (by decide : 2 < 5) hF hf
  let := J.special_isPerfect_of_fixed_card (by decide : 2 < 5) hF hf
  have hz : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top with hz|hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
  let eQ : (J.specialSubgroup ⧸ center J.specialSubgroup) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J :=
    (QuotientGroup.quotientMulEquivOfEq (J.specialToProjective_ker_eq_center hz).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective J.specialToProjective_surjective)
  have heQ (x : J.specialSubgroup) :
      eQ (QuotientGroup.mk' (center J.specialSubgroup) x) = J.specialToProjective x := by
    simp only [eQ,MulEquiv.trans_apply,QuotientGroup.mk'_apply,
      QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  let b := MulAut.centralQuotientAction eQ a
  have hb : orderOf b = 2 :=
    (orderOf_injective _ (MulAut.centralQuotientAction_injective eQ) a).trans ha
  obtain ⟨Q,hQ⟩ := MulAut.centralQuotientAction_exists_fixed_sylow eQ a P hP
  obtain ⟨t,ht⟩ := OddPrimeSylow.inner_of_involutive_fixing_sylow J (by decide) (by decide)
    hF hf Q b (hb ▸ pow_orderOf_eq_one b) hQ
  have hto : orderOf t = 2 :=
    (orderOf_injective MulAut.conj (Theory.GroupTheory.conj_injective_of_center_eq_bot hz) t).symm.trans
      (ht ▸ hb)
  have h2 : (2:F) ≠ 0 := by
    let := Fintype.ofFinite F
    let : CharP F 5 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two (by decide : 5 ≠ 2)
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (InvolutionConjugateBounds.Inner.projective_involutions_isConj J (by decide) (by decide)
      hF hc (hermitianTorusPSU J hJ (-1)) t (torus_neg_orderOf J hJ h2) hto)
  obtain ⟨r,hr⟩ := J.specialToProjective_surjective g
  refine ⟨r,MulAut.centralQuotientAction_injective eQ ?_⟩
  rw [MulAut.centralQuotientAction_conj,heQ]
  have htq : J.specialToProjective (hermitianTorusSU J hJ (-1)) =
      hermitianTorusPSU J hJ (-1) := by
    apply Subtype.ext
    exact J.specialToProjective_apply_val _
  have hqt : J.specialToProjective (r * hermitianTorusSU J hJ (-1) * r⁻¹) = t := by
    rw [map_mul,map_mul,map_inv,hr,htq]
    exact hg
  rw [hqt]
  exact ht



/-- On a faithful binary ambient module, every nontrivial involutory SU₃(5)
Sylow fixer displaces at least eight dimensions. -/
theorem eight_le_displacement_of_sylow_fixer [Finite F]
    (hF : Nat.card F = 5 ^ 2) (hc : ∀ x, J.conj x = x ^ 5)
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hρ : Function.Injective ρ)
    (j : J.specialSubgroup →* D) (hj : Function.Injective j)
    (t : D) (a : MulAut J.specialSubgroup) (ha : orderOf a = 2)
    (P : Sylow 2 J.specialSubgroup) (hP : ∀ x ∈ P, a x = x)
    (heq : ∀ x, j (a x) = t * j x * t⁻¹) :
    8 ≤ Module.finrank (ZMod 2) (ρ t - LinearMap.id).range := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hf : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 5 1
      (by decide) (by simpa using hF) (by simpa using hc)
  obtain ⟨C,hC⟩ := FormTransport.exists_standard_basis J 5 hF hf
  let e := FormTransport.specialEquiv J C hC
  let J₀ := FormTransport.standardForm J
  let a₀ := MulAut.congr e a
  let P₀ := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have ha₀ : orderOf a₀ = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  have hP₀ : ∀ x ∈ P₀, a₀ x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hP x hx]
  obtain ⟨g,hg⟩ := sylow_fixer_is_sign_conjugation J₀ rfl hF hc P₀ a₀ ha₀ hP₀
  obtain ⟨Y,hY,hYcard,hYexp,b,hb,hmove⟩ := sign_conjugate_moves_root J₀ rfl hF hf g
  let := hY
  let k := j.comp e.symm.toMonoidHom
  have hk : Function.Injective k := hj.comp e.symm.injective
  apply Representation.ExtraspecialQuinticActor.eight_le_displacement_of_movement ρ hρ
    (k.comp Y.subtype) (hk.comp Y.subtype_injective) hYcard hYexp t b hb
  intro x
  change k (b x).val = t * k x.val * t⁻¹
  rw [hmove]
  change k ((MulAut.conj (g * hermitianTorusSU J₀ rfl (-1) * g⁻¹)) x.val) = _
  rw [←hg]
  change j (e.symm (e (a (e.symm x.val)))) = _
  rw [e.symm_apply_apply]
  exact heq (e.symm x.val)
end BenderSuzuki.MatrixGroups.HermitianForm.QuinticSylowFixer
