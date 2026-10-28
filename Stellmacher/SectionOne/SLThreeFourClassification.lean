module

public import Stellmacher.SectionOne.Defs
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card


/-!
# The center-fixed `SL₃(4)` endpoint in Stellmacher (1.3)

This proves the finite-linear classification used in the center-fixed branch
of Stellmacher's Lemma (1.3).  A nontrivial odd `p`-group `F`, generated as a
commutator by an involution that centralizes `Z(F)`, is nonabelian.  An
embedding of the reduced group in `SL₃(4)` then forces `|F| = 3³` from the
order of the special linear group.  Finally, a nonabelian group of order
`3³` has center of order `3` and elementary abelian central quotient, so it
is extraspecial.

Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.3), journal p. 16.
-/

namespace Stellmacher.SectionOne

universe u

private abbrev FourField := GaloisField 2 2

private theorem fourField_card : Nat.card FourField = 4 := by
  simpa using GaloisField.card 2 2 (by decide)

private theorem glThreeFour_card :
    Nat.card (Matrix.GeneralLinearGroup (Fin 3) FourField) = 181440 := by
  classical
  let _ := Fintype.ofFinite FourField
  rw [Matrix.card_GL_field]
  rw [show Fintype.card FourField = 4 by
    simpa [Nat.card_eq_fintype_card] using fourField_card]
  norm_num [Fin.prod_univ_succ]

private theorem fourField_units_card : Nat.card FourFieldˣ = 3 := by
  rw [Nat.card_units, fourField_card]

private theorem slThreeFour_detKer_card :
    Nat.card
        (Matrix.GeneralLinearGroup.det.ker :
          Subgroup (Matrix.GeneralLinearGroup (Fin 3) FourField)) = 60480 := by
  let det : Matrix.GeneralLinearGroup (Fin 3) FourField →* FourFieldˣ :=
    Matrix.GeneralLinearGroup.det
  change Nat.card det.ker = 60480
  have hrange : det.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective
  have hindex : det.ker.index = 3 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top]
    exact fourField_units_card
  have hmul : Nat.card det.ker * 3 = 181440 := by
    simpa [hindex, glThreeFour_card] using det.ker.card_mul_index
  omega

private theorem isExtraspecial_three_of_card_cube_of_not_commutative
    {F : Type u} [Group F] [Finite F]
    (hcard : Nat.card F = 3 ^ 3) (hncomm : ¬ IsMulCommutative F) :
    IsExtraspecial 3 F := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hFp : IsPGroup 3 F := IsPGroup.of_card hcard
  obtain ⟨k, hkpos, hcenter⟩ :=
    IsPGroup.card_center_eq_prime_pow hcard (by omega : 0 < 3)
  have hcenterDvd : Nat.card (Subgroup.center F) ∣ Nat.card F :=
    Subgroup.card_subgroup_dvd_card (Subgroup.center F)
  have hk_le : k ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by omega : 1 < 3)).mp
    apply Nat.le_of_dvd (by positivity)
    simpa [hcenter, hcard] using hcenterDvd
  have hk : k = 1 := by
    have hcases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · rfl
    · exfalso
      have hindex : (Subgroup.center F).index = 3 := by
        have hmul := (Subgroup.center F).card_mul_index
        rw [hcenter, hcard] at hmul
        norm_num at hmul
        exact Nat.mul_left_cancel (by norm_num : 0 < 9) (by simpa using hmul)
      have hquotCard : Nat.card (F ⧸ Subgroup.center F) = 3 := by
        rw [← Subgroup.index_eq_card]
        exact hindex
      let _ : IsCyclic (F ⧸ Subgroup.center F) :=
        isCyclic_of_prime_card hquotCard
      exact hncomm (isMulCommutative_of_isCyclic_quotient_center_self F)
    · exfalso
      have hcenterTop : Subgroup.center F = ⊤ := by
        apply (Subgroup.card_eq_iff_eq_top (Subgroup.center F)).mp
        rw [hcenter, hcard]
      let _ : IsMulCommutative F := by
        rw [← Subgroup.center_eq_top_iff]
        exact hcenterTop
      exact hncomm inferInstance
  have hcenterCard : Nat.card (Subgroup.center F) = 3 := by
    rw [hcenter, hk]
    norm_num
  have hquotCard : Nat.card (F ⧸ Subgroup.center F) = 3 ^ 2 := by
    rw [← Subgroup.index_eq_card]
    have hmul := (Subgroup.center F).card_mul_index
    rw [hcenterCard, hcard] at hmul
    norm_num at hmul
    exact Nat.mul_left_cancel (by norm_num : 0 < 3) (by simpa using hmul)
  have hquotNontrivial : Nontrivial (F ⧸ Subgroup.center F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hquotCard]; norm_num)
  have hquotP : IsPGroup 3 (F ⧸ Subgroup.center F) :=
    hFp.to_quotient (Subgroup.center F)
  have hquotComm : IsMulCommutative (F ⧸ Subgroup.center F) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hquotCard
  let _ : IsMulCommutative (F ⧸ Subgroup.center F) := hquotComm
  have hquotNotCyclic : ¬ IsCyclic (F ⧸ Subgroup.center F) := by
    intro hcyc
    let _ : IsCyclic (F ⧸ Subgroup.center F) := hcyc
    exact hncomm (isMulCommutative_of_isCyclic_quotient_center_self F)
  have hquotExponent : Monoid.exponent (F ⧸ Subgroup.center F) ∣ 3 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro y
    have hyDvd : orderOf y ∣ 3 ^ 2 := by
      rw [← hquotCard]
      exact orderOf_dvd_natCard y
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hyDvd
    interval_cases j
    · have hyone : y = 1 := by
        rw [← orderOf_eq_one_iff, hj]
        norm_num
      simp [hyone]
    · simpa [hj] using pow_orderOf_eq_one y
    · exfalso
      apply hquotNotCyclic
      apply isCyclic_of_orderOf_eq_card y
      rw [hj, hquotCard]
  exact
    { center_order_p := hcenterCard
      quotient_elementary_abelian :=
        { exponent_dvd_p := hquotExponent }
      quotient_nontrivial := hquotNontrivial }

/-- The `SL₃(4)` classification endpoint in the center-fixed branch of
Stellmacher's Lemma (1.3). -/
public theorem slThreeFour_involutionPGroup_classification
    {G : Type u} [Group G] [Finite G]
    (F : Subgroup G) (x : G) (p : ℕ) [Fact p.Prime]
    (_hx : IsInvolution x)
    (_hFnorm : F.Normal)
    (hFne : F ≠ ⊥)
    (hodd : Nat.Coprime 2 (Nat.card F))
    (hFp : IsPGroup p F)
    (_hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcomm : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcenter :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
    (rho : G →* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (hrho : Function.Injective rho) :
    IsExtraspecial 3 F ∧ Nat.card F = 3 ^ 3 := by
  have hncomm : ¬ IsMulCommutative F := by
    intro hFcomm
    let _ : IsMulCommutative F := hFcomm
    have hcenterMap : (Subgroup.center F).map F.subtype = F := by
      rw [Subgroup.center_eq_top]
      calc
        Subgroup.map F.subtype ⊤ = F.subtype.range :=
          (MonoidHom.range_eq_map F.subtype).symm
        _ = F := F.range_subtype
    have hcommBot : ⁅F, Subgroup.zpowers x⁆ = ⊥ := by
      simpa [hcenterMap] using hcenter
    exact hFne (hcomm.symm.trans hcommBot)
  let det : Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 2) →*
      (GaloisField 2 2)ˣ :=
    Matrix.GeneralLinearGroup.det
  let slToKer :
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) →* det.ker :=
    Matrix.SpecialLinearGroup.toGL.codRestrict det.ker (by intro g; simp [det])
  let rhoF : F →* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
    rho.comp F.subtype
  let rhoKer : F →* det.ker := slToKer.comp rhoF
  have hrhoKer : Function.Injective rhoKer := by
    intro a b hab
    apply F.subtype_injective
    apply hrho
    apply Matrix.SpecialLinearGroup.toGL_injective
    exact congrArg Subtype.val hab
  have hcardDvd : Nat.card F ∣ 60480 := by
    have hdiv := Subgroup.card_dvd_of_injective rhoKer hrhoKer
    have hkerCard : Nat.card det.ker = 60480 := by
      simpa [det] using slThreeFour_detKer_card
    rwa [hkerCard] at hdiv
  obtain ⟨n, hcardF⟩ := hFp.exists_card_eq
  have hn : 3 ≤ n := by
    by_contra hnlt
    have hnle : n ≤ 2 := by omega
    interval_cases n
    · apply hFne
      apply (Subgroup.eq_bot_iff_card F).mpr
      simpa using hcardF
    · apply hncomm
      have hcyc : IsCyclic F := isCyclic_of_prime_card (by simpa using hcardF)
      exact @IsCyclic.isMulCommutative F inferInstance hcyc
    · exact hncomm (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardF)
  have hpPowDvd : p ^ n ∣ 60480 := by simpa [hcardF] using hcardDvd
  have hpDvd : p ∣ 60480 :=
    (dvd_pow_self p (by omega : n ≠ 0)).trans hpPowDvd
  have hpCases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    have hpFactor : p ∣ 2 ^ 6 * 3 ^ 3 * 5 * 7 := by
      norm_num at hpDvd ⊢
      exact hpDvd
    rcases (Fact.out : Nat.Prime p).dvd_mul.mp hpFactor with hp2or3or5 | hp7
    · rcases (Fact.out : Nat.Prime p).dvd_mul.mp hp2or3or5 with hp2or3 | hp5
      · rcases (Fact.out : Nat.Prime p).dvd_mul.mp hp2or3 with hp2 | hp3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide)).mp
            ((Fact.out : Nat.Prime p).dvd_of_dvd_pow hp2))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide)).mp
            ((Fact.out : Nat.Prime p).dvd_of_dvd_pow hp3)))
      · exact Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide)).mp hp5)))
    · exact Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide)).mp hp7)))
  have hpThree : p = 3 := by
    rcases hpCases with hpTwo | hpThree | hpFive | hpSeven
    · subst p
      exfalso
      apply Nat.not_coprime_of_dvd_of_dvd (by omega : 1 < 2) dvd_rfl
        (show 2 ∣ Nat.card F by rw [hcardF]; exact dvd_pow_self 2 (by omega))
      exact hodd
    · exact hpThree
    · subst p
      have h125 : 5 ^ 3 ∣ 60480 := (Nat.pow_dvd_pow 5 hn).trans hpPowDvd
      norm_num at h125
    · subst p
      have h343 : 7 ^ 3 ∣ 60480 := (Nat.pow_dvd_pow 7 hn).trans hpPowDvd
      norm_num at h343
  subst p
  have hnle : n ≤ 3 := by
    by_contra hnnot
    have hfour : 3 ^ 4 ∣ 60480 :=
      (Nat.pow_dvd_pow 3 (by omega : 4 ≤ n)).trans hpPowDvd
    norm_num at hfour
  have hnThree : n = 3 := by omega
  have hcardThree : Nat.card F = 3 ^ 3 := by simpa [hnThree] using hcardF
  exact ⟨isExtraspecial_three_of_card_cube_of_not_commutative hcardThree hncomm,
    hcardThree⟩

end Stellmacher.SectionOne

