module
public import Theory.SpecificGroups.SU3.OddPrimeOuterExponent
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.AllPrimes
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import ABG.ChapterII.Section2.UnitaryCard
public import Theory.GroupAction.InnerCentralizerCardinality

/-!
# Sylow-fixing involution centralizers in PSU₃(3)

Lifting the original projective involution through the scalar kernel
identifies a covering centralizer with GU₂(3), of order 96. Thus its
projective centralizer has order dividing 96. Semilinear coverage gives
an outer exponent dividing eight and hence a two-group outer quotient.
A Sylow-fixing involution is inner, so its full automorphism centralizer
cannot have order divisible by nine.

The supplied Hermitian form and Frobenius involution are retained.
Simplicity is inherited from the actual source component.
Source: Aschbacher–Smith A.3.21 and 12.6.26, printed pp.55 and832;
Huppert II.10.12 and GLS3 §2.5–2.7 for the native matrix interfaces.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.TernarySylowCentralizer
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private theorem standard_centralizer_card_dvd
    (k : ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 3 1 one_ne_zero))
    (hk : orderOf k = 2) :
    Nat.card (centralizer ({k} : Set _)) ∣ 96 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let J3 := ABG.unitaryForm 3 3 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 3 1 one_ne_zero
  let q := J3.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J3.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨z, hz, rfl⟩ := Matrix.SU3.InnerThreeRank.exists_involution_lift_of_cube_kernel q
    J3.specialToProjective_surjective hcube k hk
  let C := centralizer ({z} : Set J3.specialSubgroup)
  have hmap : C.map q = centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J3)) :=
    Matrix.SU3.InnerThreeRank.map_centralizer_of_central_cube_kernel q J3.specialToProjective_surjective
      J3.specialToProjective_ker_le_center hcube z (by simpa only [hz] using pow_orderOf_eq_one z)
  let ep := MulEquiv.subgroupCongr hmap
  let f := ep.toMonoidHom.comp (q.subgroupMap C)
  have hf : Function.Surjective f := ep.surjective.comp (q.subgroupMap_surjective C)
  let ec : C ≃* J2.unitarySubgroup :=
    (Matrix.SU3.involutionCentralizerEquiv (by decide : 3 ≠ 2)
      (GaloisField.card 3 (2 * 1) (by decide)) J3 J2 rfl rfl
      (by intro x; simp only [J3, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one])
      (by intro x; simp only [J2, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]) z hz).symm
  have hd := card_dvd_of_surjective f hf
  rw [Nat.card_congr ec.toEquiv] at hd
  have hcard : Nat.card J2.unitarySubgroup = 96 := by
    change Nat.card (ABG.GU2 3 1 one_ne_zero) = 96
    rw [ABG.GU2_card 3 1 (by decide) one_ne_zero]
    norm_num
  exact hcard ▸ hd

/-- The literal ternary projective involution centralizer has order dividing 96. -/
theorem centralizer_card_dvd {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hF : Nat.card F = 3 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 3)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set _)) ∣ 96 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨e⟩ := Matrix.SU3.InnerThreeRank.exists_projective_equiv_standard 3 F J hF hc
  rw [Nat.card_congr (Matrix.SU3.InnerThreeRank.centralizerEquiv e t).toEquiv]
  exact standard_centralizer_card_dvd (e t) ((e.orderOf_eq t).trans ht)


/-- The full outer group has two-power order for the original field and form. -/
theorem outer_isTwoGroup {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hF : Nat.card F = 3 ^ 2) (hc : ∀ x, J.conj x = x ^ 3) :
    IsPGroup 2 (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective
    (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) x
  refine ⟨3,?_⟩
  rw [←map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact J.odd_prime_unitary_power_inner (by decide) (by decide) hF hc a

/-- A Sylow-fixing involution in the full PSU3(3) automorphism group cannot centralize E9. -/
theorem not_nine_dvd_sylow_fixer_centralizer {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hF : Nat.card F = 3 ^ 2) (hc : ∀ x, J.conj x = x ^ 3)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))) := by
  let B := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite B := Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hf : Nat.card {x : F // J.conj x = x} = 3 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 3 1
      (by decide) (by simpa using hF) (by simpa using hc)
  let := J.projective_isPerfect_of_fixed_card (by decide : 2 < 3) hF hf
  have hz : center B = ⊥ := by
    rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with hz|hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp hz)).elim
  obtain ⟨t,ht⟩ := OddPrimeSylow.inner_of_involutive_fixing_sylow J (by decide) (by decide)
    hF hf P a (ha ▸ pow_orderOf_eq_one a) hP
  have hto : orderOf t = 2 :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hz) t).symm.trans
      (ht ▸ ha)
  have hd := MulAut.centralizer_conj_card_dvd hz t
  have hC := centralizer_card_dvd J hF hc t hto
  obtain ⟨n,hn⟩ := (outer_isTwoGroup J hF hc).exists_card_eq
  intro h9
  rw [ht] at h9
  have hh := h9.trans (hd.trans (Nat.mul_dvd_mul_right hC (Nat.card (MulAut.Outer B))))
  rw [hn] at hh
  have hcop : Nat.Coprime 9 (2^n) := (by decide : Nat.Coprime 9 2).pow_right n
  exact (by decide : ¬ 9 ∣ 96) (hcop.dvd_mul_right.mp hh)
end BenderSuzuki.MatrixGroups.HermitianForm.TernarySylowCentralizer
