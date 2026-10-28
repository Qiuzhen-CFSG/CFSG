module
public import Theory.GroupTheory.SemidihedralWreathedTwoFiveCenter
public import ABG.ChapterII.Section2.FullSylowShapes
public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.GroupTheory.SingleInvolutionClassSylow
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.SpecificGroups.ProjectiveLinearInvolutions

/-!
# Actual odd-prime PSU₃ two-five overgroups and involution centralizers

The literal SU₃ involution centralizer is GU₂(p), and has odd index by
involution conjugacy. The scalar projective kernel has odd order. Their
actual Sylow comparisons derive the semidihedral or wreathed presentation,
then Hermitian basis transport treats every original nondegenerate form.
The full normalizer of the supplied two-five overgroup fixes the same
central involution of its supplied full Sylow.

Source: ABG II.1 Propositions 1–2 and II.2 Lemma 1; Aschbacher–Smith
A.3.21(a) and the odd ternary row of 6.1.4.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
namespace Matrix.SU3.TwoFiveSylow

private theorem prime_conj (n p : ℕ) [Fact p.Prime]
    (x : GaloisField p (2*1)) :
    (ABG.unitaryForm n p 1 one_ne_zero).conj x = x^p := by
  simp only [ABG.unitaryForm,iterateFrobeniusEquiv_def,pow_one]

private theorem standard_sylow_shape (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))) :
    Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T := by
  let J3 := ABG.unitaryForm 3 p 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
  let F := GaloisField p (2*1)
  have hF : Nat.card F = p^2 := GaloisField.card p (2*1) (by decide)
  have h2 : (2 : F) ≠ 0 := Field.two_ne_zero_of_odd_card F (hF.symm ▸ ho.pow)
  have hp2 : p ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ dvd_rfl)
  let z := standardInvolution J3 rfl
  have hz : orderOf z = 2 := standardInvolution_orderOf J3 rfl h2
  let S : Sylow 2 J3.specialSubgroup := Classical.choice inferInstance
  let P : Sylow 2 (ABG.GU2 p 1 one_ne_zero) := Classical.choice inferInstance
  have hi := odd_index_centralizer_of_one_involution_class z hz
    (fun w hw => involutions_isConj hp2 hF J3 rfl (prime_conj 3 p) w z hw hz)
  let ec : centralizer ({z} : Set J3.specialSubgroup) ≃* ABG.GU2 p 1 one_ne_zero :=
    (involutionCentralizerEquiv hp2 hF J3 J2 rfl rfl
      (prime_conj 3 p) (prime_conj 2 p) z hz).symm
  obtain ⟨e⟩ := sylow_equiv_of_odd_index _ hi ec S P
  let eT := Sylow.equivOfSurjectiveCoprime J3.specialToProjective
    J3.specialToProjective_surjective (Nat.coprime_two_left.mpr J3.odd_card_specialToProjective_ker) S T
  let ePT : P ≃* T := e.symm.trans eT
  rcases ABG.full_GU2_sylow_shape p 1 ho one_ne_zero P with h | ⟨n,h⟩
  · exact .inl (ABG.semidihedral_equiv ePT h)
  · exact .inr ⟨n,ABG.wreathed_equiv ePT h⟩

private theorem sylow_shape (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (F : Type*) [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = p^2) (hconj : ∀x,J.conj x=x^p)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨e⟩ := InnerThreeRank.exists_projective_equiv_standard p F J hF hconj
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let eT : T ≃* P := (T : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective
  rcases standard_sylow_shape p ho P with h | ⟨n,h⟩
  · exact .inl (ABG.semidihedral_equiv eT.symm h)
  · exact .inr ⟨n,ABG.wreathed_equiv eT.symm h⟩

/-- The original Hermitian form and supplied Sylow are retained: every
normalizer element of the actual two-five overgroup fixes its central involution. -/
theorem normalizer_le_centralizer (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (F : Type*) [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = p^2) (hconj : ∀x,J.conj x=x^p)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hTH : (T : Subgroup _) ≤ H) {k : ℕ} (hd : Nat.card H ∣ 2^k*5)
    (z : T) (hz : orderOf z = 2) (hc : z ∈ center T) :
    normalizer (H : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      centralizer ({(z : ProjectiveSpecialUnitaryMatrixGroup J)} : Set _) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  exact Theory.GroupTheory.TwoFiveSylow.normalizer_le_involution_centralizer
    T (sylow_shape p ho F J hF hconj T) H hTH hd z hz hc

/-- Every automorphism of the original PSU₃ carrier preserving the actual
overgroup fixes its supplied central Sylow involution. -/
theorem automorphism_fixes_involution (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (F : Type*) [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = p^2) (hconj : ∀x,J.conj x=x^p)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hTH : (T : Subgroup _) ≤ H) {k : ℕ} (hd : Nat.card H ∣ 2^k*5)
    (z : T) (hz : orderOf z = 2) (hc : z ∈ center T)
    (φ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hφ : H.map φ.toMonoidHom = H) :
    φ (z : ProjectiveSpecialUnitaryMatrixGroup J) = z := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  exact Theory.GroupTheory.TwoFiveSylow.automorphism_fixes_involution
    T (sylow_shape p ho F J hF hconj T) H hTH hd z hz hc φ hφ

end Matrix.SU3.TwoFiveSylow
