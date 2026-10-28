module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Action
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ProjectiveIndices
public import Theory.SpecificGroups.SU3.OddPrimeOuterExponent
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.MatrixCocycle

/-!
# The odd-prime unitary split branch

A Hermitian basis change preserves the actual PSU₃ component. Over the
prime-square matrix field, semilinear automorphism squares are unitary.
An odd prime actor is therefore unitary, and the outer exponents force
p = 3 and r ≡ −1 mod 3. Projective scalar rigidity identifies the unitary
action image with the literal PGU₃ carrier. The outside actor fills this
index-three extension. Its kernel and residual are the original star
kernel and star residual, yielding the complete source alternative (2).

Source: Aschbacher–Smith A.3.18, printed pp.51–53; GLS3, Theorem 2.5.12.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
open Matrix BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter

private theorem unitary_inner_le {F : Type*} [Field F] (J : HermitianForm 3 F) :
    MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ J.unitaryConjHom.range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨u, rfl⟩ := J.specialToProjective_surjective x
  exact ⟨⟨u.val, u.property.1⟩, (J.unitaryConjHom_apply _).trans
    (J.unitaryConj_special_is_inner u)⟩

private theorem unitary_action_kernel {F : Type*} [Field F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (h2 : (2 : F) ≠ 0)
    (hconj : ∃ t : F, J.conj t ≠ t) :
    J.unitaryConjHom.ker = (unitaryToPGU J).ker := by
  ext u
  constructor
  · intro hu
    have hh : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
        Commute (ProjGenLinGroup.mk u.val) x.val := by
      intro x
      have he := congrArg (fun b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => (b x).val) hu
      rw [J.unitaryConjHom_apply] at he
      change (J.unitaryConj u x).val = x.val at he
      rw [J.unitaryConj_apply_val] at he
      exact (mul_inv_eq_iff_eq_mul).mp he
    apply Subtype.ext
    exact ProjGenLinGroup.mk_eq_one.mpr
      (Descent.projective_centralizer_scalar J hJ h2 hconj u.val hh)
  · intro hu
    have he : ProjGenLinGroup.mk u.val = 1 := congrArg Subtype.val hu
    change J.unitaryConjHom u = 1
    rw [J.unitaryConjHom_apply]
    ext x
    change (J.unitaryConj u x).val = x.val
    rw [J.unitaryConj_apply_val, he, one_mul, inv_one, mul_one]

private def pguEquivUnitaryAction {F : Type*} [Field F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (h2 : (2 : F) ≠ 0)
    (hconj : ∃ t : F, J.conj t ≠ t) :
    projectiveUnitary J ≃* J.unitaryConjHom.range :=
  (QuotientGroup.quotientKerEquivOfSurjective (unitaryToPGU J)
    (unitaryToPGU_surjective J)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (unitary_action_kernel J hJ h2 hconj).symm).trans
        (QuotientGroup.quotientKerEquivRange J.unitaryConjHom))

private theorem unitary_square_mem {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (hF : Nat.card F = r ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = r)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    a ^ 2 ∈ J.unitaryConjHom.range := by
  obtain ⟨σ, ha⟩ := Coverage.semilinear_coverage_odd J hJ hr ho hF hfixed a
  have hσ : σ ^ 2 = 1 := FiniteField.ringAut_sq_of_card_prime_pow hr (by decide) hF σ
  have hs : J.HasUnitarySemilinearForm (a ^ 2) 1 := by
    simpa only [← pow_two, hσ] using ha.mul J hJ ha
  obtain ⟨u, hu⟩ := (HasUnitarySemilinearForm.one_iff J).mp hs
  exact ⟨u, (J.unitaryConjHom_apply u).trans hu.symm⟩

theorem ordinary_odd_unitary_projective
    {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    {p r : ℕ} (hp : p.Prime) (ho : Odd p) (hrank : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : r.Prime) (hro : Odd r)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 r)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    p = 3 ∧ SignedCongruence true r ∧
      ClassicalGroup.IsPSU (starComponent p K) 3 r ∧
        IsPGUThree (primeToResidual 3 (Star p H)) r := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
  have hfixed : Nat.card {x : F // J.conj x = x} = r := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius J.conj r 1
      (by decide) (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hc)
  obtain ⟨e₀⟩ := FormTransport.exists_projectiveEquiv J r hF hfixed
  let J₀ := FormTransport.standardForm J
  let e' := e.trans e₀
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    e'.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  let f := normalAction K e'
  have hb := hH.stronglyQuasithin p hp ho
  have hd6 : p ∣ 6 := prime_dvd_of_action_power_inner hz hrank hb e' a ha haK
    (J₀.odd_prime_sixth_power_inner hr hro hF hc (f a))
  have hnot2 : ¬ p ∣ 2 := hp.coprime_iff_not_dvd.mp (Nat.coprime_two_right.mpr ho)
  have hd3 : p ∣ 3 := (hp.dvd_mul.mp (show p ∣ 2 * 3 from hd6)).resolve_left hnot2
  have hp3 : p = 3 := ((Nat.dvd_prime Nat.prime_three).mp hd3).resolve_left hp.ne_one
  cases hp3
  have hdiv : 3 ∣ r + 1 :=
    (Nat.prime_three.dvd_mul.mp (prime_dvd_of_action_power_inner hz hrank hb e' a ha haK
      (J₀.odd_prime_unitary_power_inner hr hro hF hc (f a)))).resolve_left (by decide)
  have hmod : r % 3 = 2 := by
    have := Nat.mod_eq_zero_of_dvd hdiv
    omega
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    obtain ⟨k, hk⟩ := hro
    omega
  have h2 := Coverage.two_ne_zero_of_prime_square hr hr3 hF
  have hconj : ∃ t : F, J₀.conj t ≠ t := by
    by_contra hn
    push Not at hn
    let e : F ≃ {x : F // J₀.conj x = x} :=
      { toFun := fun x => ⟨x, hn x⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he := Nat.card_congr e
    change Nat.card F = Nat.card {x : F // J.conj x = x} at he
    rw [hF, hfixed] at he
    nlinarith
  have hapow : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hcube : f a ^ 3 = 1 := by rw [← map_pow, hapow, map_one]
  have hfa : f a ∈ J₀.unitaryConjHom.range := by
    have hs := J₀.unitaryConjHom.range.pow_mem
      (unitary_square_mem J₀ rfl hr hro hF hfixed (f a)) 2
    have hh : (f a ^ 2) ^ 2 = f a := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hcube, one_mul]
    exact hh ▸ hs
  have hi : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀) ≤ f.range := by
    rw [← normalAction_component_image K e']
    exact Subgroup.map_le_range f K
  have hdiag : f.range ≤ J₀.unitaryConjHom.range := by
    rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup, normalAction_component_image,
      MonoidHom.map_zpowers]
    exact sup_le (unitary_inner_le J₀) (zpowers_le.mpr hfa)
  have hneq : f.range ≠ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := by
    intro he
    have hh : f a ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
      he ▸ (show f a ∈ f.range from ⟨a, rfl⟩)
    have hh' := prime_dvd_of_action_power_inner hz hrank hb e' a ha haK
      (m := 1) (by simpa only [pow_one] using hh)
    norm_num at hh'
  have hs : center (ProjectiveSpecialUnitaryMatrixGroup J₀) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J₀)).Normal).eq_bot_or_eq_top
      with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative (ProjectiveSpecialUnitaryMatrixGroup J₀)
        (center_eq_top_iff.mp h)).elim
  let E₀ := pguEquivUnitaryAction J₀ rfl h2 hconj
  have he : f.range = J₀.unitaryConjHom.range := by
    apply actionImage_eq_of_index_three _ _ _ hi hdiag hneq
    rw [← Nat.card_congr E₀.toEquiv, card_pgu_three_eq_three_mul_psu J₀ r hF hc hmod]
    congr 1
    exact Nat.card_congr (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hs)).toEquiv
  let E : Star 3 H ≃* projectiveUnitary J₀ :=
    (componentActionStarEquiv hz hrank hb e').trans ((MulEquiv.subgroupCongr he).trans E₀.symm)
  refine ⟨rfl, hmod, ?_, ?_⟩
  · exact ⟨F, inferInstance, inferInstance, J₀, hF, hc,
      ⟨(componentStarQuotientEquiv hz hrank hb).symm.trans e'⟩⟩
  · exact ⟨F, inferInstance, inferInstance, J₀, hF, hc,
      ⟨((MulEquiv.subgroupCongr (star_residual_eq_top_of_split hz hrank a ha hgen)).trans
        Subgroup.topEquiv).trans E⟩⟩

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
