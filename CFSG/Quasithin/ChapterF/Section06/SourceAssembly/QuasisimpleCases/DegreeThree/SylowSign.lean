module

public import CFSG.Quasithin.ChapterA.Section03.RankThreeSylow
public import Theory.SpecificGroups.Classical.WreathedSylowSign
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.SpecificGroups.PSU3.UniversalCover.Kernel

/-!
# The degree-three sign from the actual wreathed Sylow model

The scalar projections have odd kernel, so their Sylow subgroups are
isomorphic. Prime-field and Hermitian-form transport identifies the actual
special groups with the source SL₃(p) and SU₃(p). Their involution
centralizers identify Sylow subgroups with those of GL₂(p) and GU₂(p).
The four-element wreathed center then fixes the appropriate field sign.

Source: Aschbacher--Smith A.3.21(b) and F.6.18(10)--(11), pp.55,309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {F : Type*} [Field F] [Finite F]

/-- The actual projective linear Sylow has the source linear sign. -/
theorem psl3_sign_of_wreathed_sylow
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p)
    (P : Sylow 2 PSL(3,F)) (eP : P ≃* WreathedThirtyTwo) : p % 4 = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  let j := Atlas.fieldEquivPSL 3 eF
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let ePQ : P ≃* Q := (P : Subgroup _).equivMapOfInjective j.toMonoidHom j.injective
  let S : Sylow 2 SL(3,ZMod p) := default
  have hk : Nat.Coprime 2 (Nat.card (Matrix.PSL3.projection (ZMod p)).ker) := by
    rw [Matrix.PSL3.projection_ker]
    exact (Matrix.SL3.odd_card_center (ZMod p)).coprime_two_left
  let eSQ := Sylow.equivOfSurjectiveCoprime (Matrix.PSL3.projection (ZMod p))
    (Matrix.PSL3.projection_surjective (ZMod p)) hk S Q
  let R : Sylow 2 (GL (Fin 2) (ZMod p)) := default
  obtain ⟨eSR⟩ := ChapterA.Section03.sl3_sylow_equiv_GL2 p ho S R
  let eRW : R ≃* WreathedThirtyTwo := ((eSR.symm.trans eSQ).trans ePQ.symm).trans eP
  have hc : Nat.card (center R) = 4 :=
    (Nat.card_congr (Subgroup.centerCongr eRW).toEquiv).trans wreathedThirtyTwo_center_card
  have hs := Theory.ClassicalSmallSylow.gl2_sylow_mod_four_of_center_four
    (by simpa only [Nat.card_zmod] using ho) R hc
  simpa only [Nat.card_zmod] using hs

/-- The actual projective unitary Sylow has the source unitary sign, for
its original coefficient field and Hermitian form. -/
theorem psu3_sign_of_wreathed_sylow
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (eP : P ≃* WreathedThirtyTwo) : p % 4 = 3 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let K := ABG.unitaryForm 3 p 1 (by decide)
  obtain ⟨j⟩ := Matrix.SU3.InnerThreeRank.exists_projective_equiv_standard p F J hcard hconj
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let ePQ : P ≃* Q := (P : Subgroup _).equivMapOfInjective j.toMonoidHom j.injective
  let S : Sylow 2 K.specialSubgroup := default
  have hKcard : Nat.card (GaloisField p (2 * 1)) = p ^ 2 := by
    simpa using GaloisField.card p (2 * 1) (by decide)
  have hKconj : ∀ x, K.conj x = x ^ p := by
    intro x
    simp only [K, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]
  have hk : Nat.Coprime 2 (Nat.card K.specialToProjective.ker) := by
    rw [HermitianForm.UniversalCover.card_kernel K hKcard hKconj]
    exact (by decide : Nat.Coprime 2 3).of_dvd_right (Nat.gcd_dvd_left _ _)
  let eSQ := Sylow.equivOfSurjectiveCoprime K.specialToProjective
    K.specialToProjective_surjective hk S Q
  let R : Sylow 2 (ABG.GU2 p 1 (by decide)) := default
  obtain ⟨eSR⟩ := ChapterA.Section03.su3_sylow_equiv_GU2 p ho S R
  let eRW : R ≃* WreathedThirtyTwo := ((eSR.symm.trans eSQ).trans ePQ.symm).trans eP
  have hc : Nat.card (center R) = 4 :=
    (Nat.card_congr (Subgroup.centerCongr eRW).toEquiv).trans wreathedThirtyTwo_center_card
  exact Theory.ClassicalSmallSylow.gu2_sylow_mod_four_of_center_four p ho R hc

end CFSG.Quasithin.ChapterF.SourceAssembly
