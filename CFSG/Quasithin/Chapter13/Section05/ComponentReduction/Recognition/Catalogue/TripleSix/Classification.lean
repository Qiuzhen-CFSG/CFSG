module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.FullCatalogue
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance.Models
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions.Projective
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.Representation.TripleSixOuterDisplacement

/-!
# Selecting the triple-six constituent from the complete B.4 catalogue

The center and order of the actual even hexacode group exclude every other
corrected B.4.2 constructor. The full B.4.5 table is excluded by centerlessness,
actual quotient orders, defining-characteristic divisibility for SU₃, and its
strict quadratic-ratio bounds. Thus the full disjunction supplies the actual
six-dimensional binary action with its F₄ coordinates and projective-line
(vector-plane) offender clause.

The B.4.2 group comparisons adapt the already proved Chapter 15
TripleCover.SourceAdapter.Selection comparisons to the lower corrected
Chapter B contract. No legacy one-dimensional offender implication is used.
The universal B.4 implications remain the explicit earlier source inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2(8) and
Table B.4.5, printed pp.86–87; application 13.5.21, printed p.924.
-/

@[expose] public section

open Representation.TripleSixOuterDisplacement
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TripleSix
private theorem not_hex_center_bot {L : Type*} [Group L]
    (e : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hZ : Subgroup.center L = ⊥) : False := by
  have hc := Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [hZ, Subgroup.card_bot, Representation.Hexacode.even_center_card] at hc
  norm_num at hc

private theorem not_hex_sl3 {L : Type*} [Group L]
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F) : False := by
  let f : F ≃+* GaloisField 2 n :=
    (GaloisField.algEquivGaloisField 2 n hcard).toRingEquiv
  exact
    CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance.hex_not_equiv_sl3
      n (eL.symm.trans (e.trans (Atlas.fieldEquivSL 3 f)))

private theorem center_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hZ : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  exact e.map_eq_one_iff.mp
    (hZ.le ((Subgroup.centerCongr e ⟨x, hx⟩).property))

private theorem not_hex_g2 {L : Type*} [Group L]
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (BF : ChapterB.QuasisimpleSource.BinaryField) (e : L ≃* Atlas.G2.Model BF.Carrier) : False := by
  have hL : Nat.card L = 1080 := by
    rw [Nat.card_congr eL.toEquiv, Atlas.Codes.hexEven_card]
  have hc : Nat.card (Atlas.G2.Model BF.Carrier) = 1080 :=
    (Nat.card_congr e.toEquiv).symm.trans hL
  rw [Atlas.G2.card_Model, BF.card_eq] at hc
  have hd1 : 1 ≤ BF.degree := BF.degree_pos
  have hq : 2 ≤ 2 ^ BF.degree := by
    have hpow : 2 ^ 1 ≤ 2 ^ BF.degree :=
      Nat.pow_le_pow_right (by decide) hd1
    simpa using hpow
  have hq6 : 64 ≤ (2 ^ BF.degree) ^ 6 := by
    have hpow : (2 ^ 1) ^ 6 ≤ (2 ^ BF.degree) ^ 6 :=
      Nat.pow_le_pow_left hq 6
    norm_num at hpow ⊢
    exact hpow
  have hq2 : 4 ≤ (2 ^ BF.degree) ^ 2 := by
    have hpow : (2 ^ 1) ^ 2 ≤ (2 ^ BF.degree) ^ 2 :=
      Nat.pow_le_pow_left hq 2
    norm_num at hpow ⊢
    exact hpow
  have hq6m : 63 ≤ (2 ^ BF.degree) ^ 6 - 1 := by omega
  have hq2m : 3 ≤ (2 ^ BF.degree) ^ 2 - 1 := by omega
  have hbound : 12096 ≤ (2 ^ BF.degree) ^ 6 *
      ((2 ^ BF.degree) ^ 6 - 1) * ((2 ^ BF.degree) ^ 2 - 1) := by
    calc
      12096 = 64 * 63 * 3 := by norm_num
      _ ≤ (2 ^ BF.degree) ^ 6 * ((2 ^ BF.degree) ^ 6 - 1) *
          ((2 ^ BF.degree) ^ 2 - 1) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul hq6 hq6m) hq2m
  omega

theorem tripleSix_of_irreducible {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {L H : Subgroup D}
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) : Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ L) := by
  cases h with
  | linearTwo F _ e _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot)).elim
  | linearThree F _ e _ =>
      exact (not_hex_sl3 eL F.card_eq e.groupEquiv).elim
  | symplectic F _ _ e _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot)).elim
  | symplecticTwo e _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv
        (e.subgroupEquiv.trans binarySymplecticDerivedEquiv)
        (alternatingGroup.center_eq_bot (by simp)))).elim
  | g2 F _ _ e _ _ => exact (not_hex_g2 eL F e.groupEquiv).elim
  | g2Two e _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.subgroupEquiv
        Theory.SpecificGroups.g2_derived_two_center_eq_bot)).elim
  | symmetric n hn e _ _ =>
      have hn4 : 4 ≤ n := by omega
      have hn4' : 4 ≤ Nat.card (Fin n) := by simpa using hn4
      exact (not_hex_center_bot eL (center_bot_of_equiv e.subgroupEquiv
        (alternatingGroup.center_eq_bot hn4'))).elim
  | alternatingSix _ e _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        (alternatingGroup.center_eq_bot (by simp)))).elim
  | alternatingSeven _ _ e _ _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e
        (alternatingGroup.center_eq_bot (by simp)))).elim
  | tripleSix _ action _ => exact ⟨action⟩
  | binaryLinear d _ _ e _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        (sl_binary_center_eq_bot d (by omega)))).elim
  | orthogonalSix _ _ e _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        (alternatingGroup.center_eq_bot (by simp)))).elim
  | symmetricEight _ e _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.subgroupEquiv
        (alternatingGroup.center_eq_bot (by simp)))).elim
  | exteriorFive _ _ e _ _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e
        (sl_binary_center_eq_bot 5 (by decide)))).elim



private theorem not_hex_unitary {L : Type*} [Group L]
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (F : BinaryField) (n : ℕ) (hn : 2 ≤ n)
    (degree : F.degree = 2 * n) (J : HermitianForm 3 F.Carrier)
    (conjugation : ∀ x, J.conj x = x ^ (2 ^ n))
    (f : L ≃* J.specialSubgroup) : False := by
  have hF : Nat.card F.Carrier = (2 ^ n) ^ 2 := by
    rw [F.card_eq, degree, Nat.mul_comm 2 n, pow_mul]
  have hL : Nat.card L = 1080 :=
    (Nat.card_congr eL.toEquiv).trans Atlas.Codes.hexEven_card
  have hd : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ∣ 1080 := by
    rw [← hL, Nat.card_congr f.toEquiv]
    exact J.specialSubgroup.card_map_dvd Matrix.ProjGenLinGroup.mk
  have hc : (2 ^ n) ^ 3 ∣ 1080 :=
    (HermitianForm.BinarySylowOrder.cube_dvd_card_projective J (by omega) hF conjugation).trans hd
  have hp : 2 ^ 6 ∣ (2 ^ n) ^ 3 := by
    rw [← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega)
  exact (by norm_num : ¬ 2 ^ 6 ∣ 1080) (hp.trans hc)

/-- Every row of the full B.4.5 table is incompatible with the actual triple
cover and the quadratic bound. No restricted table is assumed. -/
theorem not_table {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {L : Subgroup D}
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hq : quadraticRatio ρ ≤ 2) : ¬ TableB45 ρ L := by
  intro h
  cases h with
  | alternatingSeven e _ _ _ =>
      exact not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        (alternatingGroup.center_eq_bot (by simp)))
  | orthogonal K F _ e _ _ _ _ =>
      exact not_hex_center_bot eL (center_bot_of_equiv e
        Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot)
  | unitary F n large degree J conjugation e _ _ _ =>
      exact not_hex_unitary eL F n large degree J conjugation e.groupEquiv
  | suzuki k positive e _ _ _ =>
      have hc : 3 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup k) := by
        rw [← Nat.card_congr e.groupEquiv.toEquiv, Nat.card_congr eL.toEquiv,
          Atlas.Codes.hexEven_card]
        norm_num
      exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free k positive hc
  | linearThree _ _ _ _ _ _ quadratic _ => exact not_lt_of_ge hq quadratic
  | g2Derived e _ _ _ =>
      exact not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        Theory.SpecificGroups.g2_derived_two_center_eq_bot)
  | mathieuTwelve _ _ quadratic _ => exact not_lt_of_ge hq quadratic
  | tripleMathieuTwentyTwo _ q _ _ _ =>
      have e := Representation.Hexacode.even_quotient_center_equiv.symm.trans
        ((centralQuotientEquiv eL).symm.trans q)
      have hc := Nat.card_congr e.toEquiv
      rw [nat_card_alternatingGroup, Sporadic.Mathieu.m22_order] at hc
      norm_num at hc
  | mathieuTwentyTwoCocode _ _ quadratic _ => exact not_lt_of_ge hq quadratic
  | mathieuTwentyTwoCode e _ _ _ =>
      have hc := Nat.card_congr (eL.symm.trans e.groupEquiv).toEquiv
      rw [Atlas.Codes.hexEven_card, Sporadic.Mathieu.m22_order] at hc
      norm_num at hc
  | mathieuTwentyThreeCocode _ _ quadratic _ => exact not_lt_of_ge hq quadratic
  | mathieuTwentyThreeCode _ _ quadratic _ => exact not_lt_of_ge hq quadratic
  | mathieuTwentyFourCocode _ _ quadratic _ => exact not_lt_of_ge hq quadratic
  | mathieuTwentyFourCode _ _ quadratic _ => exact not_lt_of_ge hq quadratic

/-- The complete corrected B.4 alternatives identify the original action
with the six-dimensional triple-cover row, including its actual F₄ structure
and the projective-line offender convention. -/
theorem action_of_fullCatalogue {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (eL : generalizedFitting D ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hq : quadraticRatio ρ ≤ 2) (hc : FullCatalogueAction ρ) :
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ (generalizedFitting D)) := by
  rcases hc with h | h
  · exact tripleSix_of_irreducible ρ eL h
  · exact (not_table ρ eL hq h).elim

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TripleSix
