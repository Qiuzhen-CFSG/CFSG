module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.SylowSign
public import Theory.GroupTheory.SmallExponentSylowShapes
public import CFSG.Quasithin.ClassicalModels

/-!
# Exponent eight excludes large prime degree-three Sylow subgroups

The actual scalar projections preserve Sylow two-subgroups. Prime-field and
Hermitian-form transport give the source semidihedral or wreathed shapes
in SL₃(p) and SU₃(p). Exponent dividing eight consequently bounds the
original projective Sylow order by 32, without a field-sign premise.
This separates the genuine marked Mathieu Sylow of order 64 from the
odd degree-three entries in the full Theorem C catalogue.

Source: Aschbacher--Smith A.3.21(b) and F.6.18(11)--(13), pp.55,309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {F : Type*} [Field F] [Finite F]

theorem psl3_sylow_card_le_32_of_exponent_eight
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p)
    (P : Sylow 2 PSL(3,F)) (he : ∀ x : P, x ^ 8 = 1) : Nat.card P ≤ 32 := by
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
  have hb := card_le_32_of_semidihedral_or_wreathed_exponent_eight
    (ChapterA.Section03.sl3_sylow_shape p ho S) heS
  exact (Nat.card_congr eSP.symm.toEquiv).trans_le hb

theorem psu3_sylow_card_le_32_of_exponent_eight
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (he : ∀ x : P, x ^ 8 = 1) : Nat.card P ≤ 32 := by
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
  have hb := card_le_32_of_semidihedral_or_wreathed_exponent_eight
    (ChapterA.Section03.su3_sylow_shape p ho S) heS
  exact (Nat.card_congr eSP.symm.toEquiv).trans_le hb

variable {G : Type*} [Group G] [Finite G]

theorem linear_three_model_sylow_card_le_32
    (P : Sylow 2 G) (he : ∀ x : P, x ^ 8 = 1)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL G 3 p) :
    Nat.card P ≤ 32 := by
  obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let ePQ : P ≃* Q := (P : Subgroup G).equivMapOfInjective j.toMonoidHom j.injective
  have hQ : ∀ x : Q, x ^ 8 = 1 := fun x => ePQ.symm.injective (by
    simpa only [map_pow, map_one] using he (ePQ.symm x))
  exact (Nat.card_congr ePQ.toEquiv).trans_le
    (psl3_sylow_card_le_32_of_exponent_eight hp ho hF Q hQ)

theorem unitary_three_model_sylow_card_le_32
    (P : Sylow 2 G) (he : ∀ x : P, x ^ 8 = 1)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSU G 3 p) :
    Nat.card P ≤ 32 := by
  obtain ⟨F, _, _, J, hF, hJ, ⟨j⟩⟩ := hm
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let ePQ : P ≃* Q := (P : Subgroup G).equivMapOfInjective j.toMonoidHom j.injective
  have hQ : ∀ x : Q, x ^ 8 = 1 := fun x => ePQ.symm.injective (by
    simpa only [map_pow, map_one] using he (ePQ.symm x))
  exact (Nat.card_congr ePQ.toEquiv).trans_le
    (psu3_sylow_card_le_32_of_exponent_eight J hp ho hF hJ Q hQ)

end CFSG.Quasithin.ChapterF.SourceAssembly
