module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.SylowSign
public import Theory.GroupTheory.WreathedThirtyTwoFromExponent

/-!
# The actual projective W32 Sylow from order and exponent

The scalar maps have odd kernels. Field and Hermitian-form transport
therefore preserve the original projective Sylow subgroup, whose proved
matrix shape is semidihedral or wreathed. At order 32 and exponent dividing
eight only the concrete W32 model remains. This supplies the source sign
without retaining a model-isomorphism premise in the row-(11) consumer.

Source: Aschbacher--Smith A.3.21(b), F.6.18(11), printed pp.55,310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {F : Type*} [Field F] [Finite F]

theorem psl3_wreathed_of_sylow32_exponent_eight
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p)
    (P : Sylow 2 PSL(3,F)) (hcP : Nat.card P = 32) (he : ∀ x : P, x ^ 8 = 1) : Nonempty (P ≃* WreathedThirtyTwo) := by
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
  let eSP : S ≃* P := eSQ.trans ePQ.symm
  have heS : ∀ x : S, x ^ 8 = 1 := fun x => eSP.injective (by
    simpa only [map_pow, map_one] using he (eSP x))
  obtain ⟨a⟩ := wreathedThirtyTwo_of_shape_card_exponent
    (ChapterA.Section03.sl3_sylow_shape p ho S) ((Nat.card_congr eSP.toEquiv).trans hcP) heS
  exact ⟨eSP.symm.trans a⟩

theorem psu3_wreathed_of_sylow32_exponent_eight
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hcP : Nat.card P = 32) (he : ∀ x : P, x ^ 8 = 1) : Nonempty (P ≃* WreathedThirtyTwo) := by
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
  let eSP : S ≃* P := eSQ.trans ePQ.symm
  have heS : ∀ x : S, x ^ 8 = 1 := fun x => eSP.injective (by
    simpa only [map_pow, map_one] using he (eSP x))
  obtain ⟨a⟩ := wreathedThirtyTwo_of_shape_card_exponent
    (ChapterA.Section03.su3_sylow_shape p ho S) ((Nat.card_congr eSP.toEquiv).trans hcP) heS
  exact ⟨eSP.symm.trans a⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
