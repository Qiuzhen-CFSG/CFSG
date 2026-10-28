module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.Original
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.SectionRecognition
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Complete
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear

/-!
# Earlier module classifications and the F.9.18 group models

The corrected B.4.2 action list and the complete B.4.5 alternatives give
actual central quotients in the F.9.18(4) list. In B.4.5 the quadratic
bound discards every row with q > 2. In the unitary row the coefficient
field and Frobenius involution are unchanged; its root subgroup of order
q³ excludes the A₇ quotient when q ≥ 4. The same two-divisibility argument
handles SL₃, including its possible center. The other non-Mathieu rows
have either trivial center or an A₆ central quotient, so none is 3.A₇.
The Mathieu alternatives retain M₂₂ itself and its genuine triple cover.

For FF actions the upstream B.4.2 proof supplies the classification, with
no classification premise remaining. The general B.4.5 conclusion is an
explicit input: this file does not assert that every F.9.18 action has
already been reduced to it. Both consequences are applied to the literal
`CoverModels.original_catalogue_or_suzuki` consumer through an actual
isomorphism with the entire generalized Fitting subgroup of the action.

The general small-quadratic classification is the independent earlier-source
input owned by qt-b4-small-quadratic-source. The D.3 action reductions and
final F.9.18 assembly remain with qt-d-138-f918-models-source;
qt-d-138-components-source supplies the relative normality hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2 and B.4.5, printed pp.86–87; F.9.18(4), pp.325–326;
and 13.8.17, p.953.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
open Models Chapter1.Section02.LocalModels
open Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open BenderSuzuki.MatrixGroups
universe u v

/-- Central quotient transport along the actual group isomorphism. -/
def centralQuotientEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (G ⧸ center G) ≃* (H ⧸ center H) :=
  QuotientGroup.congr (center G) (center H) e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro y hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

private theorem threeCover_transport {G H : Type*} {S : Type}
    [Group G] [Group H] [Group S] (e : G ≃* H) (h : IsThreeCover H S) :
    IsThreeCover G S := by
  let : IsQuasisimple H := h.1
  exact ⟨IsQuasisimple.of_mulEquiv e.symm,
    h.2.1.map ((centerCongr e).trans ·), h.2.2.map ((centralQuotientEquiv e).trans ·)⟩

/-- All F.9.18 alternatives, including the cover exclusion, respect isomorphisms. -/
theorem f918Models_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : F918Models H) : F918Models G := by
  rcases h with ⟨h, hn⟩ | h | h
  · refine Or.inl ⟨?_, fun hc => hn (threeCover_transport e.symm hc)⟩
    let q := centralQuotientEquiv e
    cases h with
    | bender h =>
      apply F918QuotientModel.bender
      cases h with
      | linear n hn hi => exact .linear n hn (hi.of_mulEquiv q)
      | unitary n hn hi => exact .unitary n hn (hi.of_mulEquiv q)
      | suzuki m hm hi => exact .suzuki m hm (hi.map (q.trans ·))
    | linear_three n hn h => exact .linear_three n hn (h.of_mulEquiv q)
    | symplectic n hn h => exact .symplectic n hn (h.of_mulEquiv q)
    | g2 n hn h => exact .g2 n hn (h.of_mulEquiv q)
    | linear_four h => exact .linear_four (h.of_mulEquiv q)
    | linear_five h => exact .linear_five (h.of_mulEquiv q)
    | alternating_seven h => exact .alternating_seven (h.map (q.trans ·))
  · exact Or.inr (Or.inl (h.map (e.trans ·)))
  · exact Or.inr (Or.inr (threeCover_transport e h))

private theorem no_seven_of_centerless {G : Type*} [Group G] (hz : center G = ⊥) :
    ¬ IsAlternatingCover G 7 := by
  intro h
  have hc := CoverModels.threeCover_center_card h
  rw [hz, card_bot] at hc
  omega

private def quotientModel {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (hz : center H = ⊥) : (G ⧸ center G) ≃* H :=
  (centralQuotientEquiv e).trans (CoverModels.centerQuotientEquiv hz).symm

private theorem centerless_of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (hz : center H = ⊥) : center G = ⊥ := by
  apply card_eq_one.mp
  rw [Nat.card_congr (centerCongr e).toEquiv, hz, card_bot]

private theorem f918_unitary {G : Type*} [Group G] [Finite G]
    (F : BinaryField) (n : ℕ) (hn : 2 ≤ n) (hd : F.degree = 2*n)
    (J : HermitianForm 3 F.Carrier) (hc : ∀ x, J.conj x = x^(2^n))
    (e : G ≃* J.specialSubgroup) : F918Models G := by
  have hcard : Nat.card F.Carrier = (2 ^ n) ^ 2 := by
    rw [F.card_eq, hd, Nat.mul_comm 2 n, pow_mul]
  have hz := HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hcard hc
  have hk := J.specialToProjective_ker_eq_center hz
  let q : (G ⧸ center G) ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    (centralQuotientEquiv e).trans
      ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ J.specialToProjective_surjective))
  refine Or.inl ⟨.bender (.unitary n hn
    ⟨F.Carrier, inferInstance, inferInstance, J, hcard, hc, ⟨q⟩⟩), ?_⟩
  intro h7
  obtain ⟨a⟩ := h7.2.2
  have hdvd := HermitianForm.BinarySylowOrder.cube_dvd_card_projective J (by omega) hcard hc
  have h64 : 64 ∣ (2 ^ n) ^ 3 := by
    rw [← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega : 6 ≤ n*3)
  have he : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = Nat.card (alternatingGroup (Fin 7)) :=
    Nat.card_congr (q.symm.trans a).toEquiv
  have hb := h64.trans hdvd
  rw [he, Nat.card_eq_fintype_card, card_alternatingGroup] at hb
  norm_num at hb

variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {L : Subgroup D} [IsQuasisimple L]

/-- The entire non-FF table of B.4.5 has precisely the required F.9.18 model
consequence at quadratic ratio at most two. -/
theorem f918Models_of_table (h : TableB45 ρ L) (hq : quadraticRatio ρ ≤ 2) :
    F918Models L := by
  cases h with
  | alternatingSeven a _ _ _ =>
    have hz := alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7))
    exact Or.inl ⟨.alternating_seven ⟨quotientModel a.groupEquiv hz⟩,
      no_seven_of_centerless (centerless_of_equiv a.groupEquiv hz)⟩
  | orthogonal K F hd e _ _ _ _ =>
    have hn : 2 ≤ F.degree := by have := K.degree_pos; omega
    have hz := GorensteinWalter.psl2_center_eq_bot F.Carrier
    exact Or.inl ⟨.bender (.linear F.degree hn
      ⟨F.Carrier, inferInstance, inferInstance, F.card_eq, ⟨quotientModel e hz⟩⟩),
      no_seven_of_centerless (centerless_of_equiv e hz)⟩
  | unitary F n hn hd J hc a _ _ _ => exact f918_unitary F n hn hd J hc a.groupEquiv
  | suzuki m hm a _ _ _ =>
    have hz := Suzuki.NaturalSections.SectionRecognition.center_eq_bot_of_equiv_suzuki a.groupEquiv
    exact Or.inl ⟨.bender (.suzuki m (by omega)
      ⟨(CoverModels.centerQuotientEquiv hz).symm.trans a.groupEquiv⟩),
      no_seven_of_centerless hz⟩
  | linearThree _ _ _ _ _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
  | g2Derived a _ _ _ =>
    have hz := Theory.SpecificGroups.g2_derived_two_center_eq_bot
    exact Or.inl ⟨.g2 1 (by decide)
      ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨quotientModel a.groupEquiv hz⟩⟩,
      no_seven_of_centerless (centerless_of_equiv a.groupEquiv hz)⟩
  | mathieuTwelve _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
  | tripleMathieuTwentyTwo z e _ _ _ => exact Or.inr (Or.inr ⟨inferInstance, ⟨z⟩, ⟨e⟩⟩)
  | mathieuTwentyTwoCocode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
  | mathieuTwentyTwoCode a _ _ _ => exact Or.inr (Or.inl ⟨a.groupEquiv⟩)
  | mathieuTwentyThreeCocode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
  | mathieuTwentyThreeCode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
  | mathieuTwentyFourCocode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
  | mathieuTwentyFourCode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim

private def derivedEquiv {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (e : G ≃* H) : G ≃* commutator H := by
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact e.trans ((MulEquiv.subgroupCongr (Group.IsPerfect.commutator_eq_top (G := H))).trans
    Subgroup.topEquiv).symm

private theorem f918_linear_two {G : Type*} [Group G] [IsQuasisimple G]
    (F : BinaryField) (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    F918Models G := by
  have hn : 2 ≤ F.degree := by
    by_contra hn
    have hd : F.degree = 1 := by have := F.degree_pos; omega
    let : Fintype F.Carrier := Fintype.ofFinite _
    let f : F.Carrier ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, F.card_eq, hd]; simp)
    let b := e.trans ((Atlas.fieldEquivSL 2 f).trans SLTwoPermThree.sl2Two_equiv_perm_three.some)
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    let : Nontrivial G := b.surjective.nontrivial
    exact Group.IsPerfect.not_isSolvable G
      (Group.isSolvable_of_isSolvable_injective (f := b.toMonoidHom) b.injective)
  have hz := Theory.PSL2.sl2_center_eq_bot F.Carrier
  let q := (quotientModel e hz).trans (Theory.PSL2.sl2QuotientEquiv F.Carrier)
  exact Or.inl ⟨.bender (.linear F.degree hn
    ⟨F.Carrier, inferInstance, inferInstance, F.card_eq, ⟨q⟩⟩),
    no_seven_of_centerless (centerless_of_equiv e hz)⟩

private theorem f918_linear_three {G : Type*} [Group G]
    (F : BinaryField) (e : G ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :
    F918Models G := by
  let q := centralQuotientEquiv e
  refine Or.inl ⟨.linear_three F.degree F.degree_pos
    ⟨F.Carrier, inferInstance, inferInstance, F.card_eq, ⟨q⟩⟩, ?_⟩
  by_cases hn : F.degree = 1
  · have hz := sl_three_center_eq_bot F (by rw [hn]; decide)
    exact no_seven_of_centerless (centerless_of_equiv e hz)
  · have hd := Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card (F := F.Carrier)
    rw [F.card_eq] at hd
    have h64 : 64 ∣ (2 ^ F.degree) ^ 3 := by
      rw [← pow_mul]
      exact Nat.pow_dvd_pow 2 (by have := F.degree_pos; omega : 6 ≤ F.degree*3)
    rintro ⟨_, _, ⟨a⟩⟩
    have he : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F.Carrier) =
        Nat.card (alternatingGroup (Fin 7)) := Nat.card_congr (q.symm.trans a).toEquiv
    have hb := h64.trans hd
    rw [he, Nat.card_eq_fintype_card, card_alternatingGroup] at hb
    norm_num at hb

private theorem f918_binary_linear {G : Type*} [Group G] {d : ℕ}
    (hd : d = 4 ∨ d = 5) (e : G ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) :
    F918Models G := by
  have hp : 0 < d := by rcases hd with rfl | rfl <;> decide
  have hz := sl_binary_center_eq_bot d hp
  let q := (quotientModel e hz).trans (binaryProjectiveEquiv d hp)
  refine Or.inl ⟨?_, no_seven_of_centerless (centerless_of_equiv e hz)⟩
  rcases hd with rfl | rfl
  · exact .linear_four ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨q⟩⟩
  · exact .linear_five ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨q⟩⟩

private theorem f918_six_quotient {G : Type*} [Group G]
    (e : (G ⧸ center G) ≃* alternatingGroup (Fin 6)) : F918Models G := by
  refine Or.inl ⟨.symplectic 1 (by decide)
    ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨e.trans binarySymplecticDerivedEquiv.symm⟩⟩, ?_⟩
  rintro ⟨_, _, ⟨a⟩⟩
  have he := Nat.card_congr (e.symm.trans a).toEquiv
  rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at he
  norm_num at he

private def sourceField (F : ChapterB.QuasisimpleSource.BinaryField) : BinaryField where
  Carrier := F.Carrier
  degree := F.degree
  degree_pos := F.degree_pos
  card_eq := F.card_eq

omit [Finite D] in
/-- The complete corrected B.4.2 action list also gives the exact group
conclusion, including its central quotient and exclusion of 3.A₇. -/
theorem f918Models_of_irreducible {H : Subgroup D}
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    F918Models L := by
  cases h with
  | linearTwo F _ e _ _ => exact f918_linear_two (sourceField F) e.groupEquiv
  | linearThree F _ e _ => exact f918_linear_three (sourceField F) e.groupEquiv
  | symplectic F _ _ e _ =>
    have hz := Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot (F := F.Carrier)
    exact Or.inl ⟨.symplectic F.degree F.degree_pos
      ⟨F.Carrier, inferInstance, inferInstance, F.card_eq,
        ⟨(CoverModels.centerQuotientEquiv (centerless_of_equiv e.groupEquiv hz)).symm.trans
          (derivedEquiv e.groupEquiv)⟩⟩,
      no_seven_of_centerless (centerless_of_equiv e.groupEquiv hz)⟩
  | symplecticTwo e _ =>
    exact f918_six_quotient (quotientModel (e.subgroupEquiv.trans binarySymplecticDerivedEquiv)
      (alternatingGroup.center_eq_bot (by simp)))
  | g2 F hF _ e _ _ =>
    have hc : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hF
    have hz := Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hc
    let a := derivedEquiv e.groupEquiv
    exact Or.inl ⟨.g2 F.degree F.degree_pos
      ⟨F.Carrier, inferInstance, inferInstance, F.card_eq,
        ⟨(CoverModels.centerQuotientEquiv (centerless_of_equiv e.groupEquiv hz)).symm.trans a⟩⟩,
      no_seven_of_centerless (centerless_of_equiv e.groupEquiv hz)⟩
  | g2Two e _ _ =>
    have hz := Theory.SpecificGroups.g2_derived_two_center_eq_bot
    exact Or.inl ⟨.g2 1 (by decide)
      ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨quotientModel e.subgroupEquiv hz⟩⟩,
      no_seven_of_centerless (centerless_of_equiv e.subgroupEquiv hz)⟩
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · exact f918_linear_two BinaryField.four (e.subgroupEquiv.trans alternatingFiveLinearEquiv)
    · have hz := alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7))
      exact Or.inl ⟨.alternating_seven ⟨quotientModel e.subgroupEquiv hz⟩,
        no_seven_of_centerless (centerless_of_equiv e.subgroupEquiv hz)⟩
  | alternatingSix _ e _ _ =>
    exact f918_six_quotient (quotientModel e.groupEquiv (alternatingGroup.center_eq_bot (by simp)))
  | alternatingSeven _ _ e _ _ _ =>
    have hz := alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7))
    exact Or.inl ⟨.alternating_seven ⟨quotientModel e hz⟩,
      no_seven_of_centerless (centerless_of_equiv e hz)⟩
  | tripleSix _ a _ => exact f918_six_quotient a.quotientEquiv
  | binaryLinear d hd _ e _ => exact f918_binary_linear hd e.groupEquiv
  | orthogonalSix _ _ e _ _ =>
    exact f918_binary_linear (Or.inl rfl) (e.groupEquiv.trans alternatingEightLinearEquiv)
  | symmetricEight _ e _ =>
    exact f918_binary_linear (Or.inl rfl) (e.subgroupEquiv.trans alternatingEightLinearEquiv)
  | exteriorFive _ _ e _ _ _ => exact f918_binary_linear (Or.inr rfl) e

open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases in
/-- B.4.2 is proved upstream, so an actual FF action has no remaining
classification premise in this group-model consequence. -/
theorem f918Models_of_ff [Finite V]
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hff : IsFFModule ρ) :
    F918Models (generalizedFitting D) := by
  let : IsQuasisimple (generalizedFitting D) := hyp.quasisimple
  obtain ⟨A, hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  exact f918Models_of_irreducible ρ
    (ChapterB.SourceClassification.irreducibleClassification_knownSimple
      D V ρ hyp.sqtk hyp.quasisimple hyp.faithful hyp.irreducible ⟨A, hA⟩)

open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases in
/-- At q ≤ 2, the complete B.4.5 conclusion implies the source group models.
Its FF branch uses the proved B.4.2 classification; its boundary is impossible. -/
theorem f918Models_of_b45 [Finite V]
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hb : B45Conclusion ρ) (hq : quadraticRatio ρ ≤ 2) :
    F918Models (generalizedFitting D) := by
  let : IsQuasisimple (generalizedFitting D) := hyp.quasisimple
  cases hb with
  | ff hc => exact f918Models_of_ff ρ hyp (Representation.BinaryOffender.isFFModule_of_cubicRatio_le_one ρ hc)
  | table _ _ ht => exact f918Models_of_table ρ ht hq
  | boundary _ hb _ => exact (not_lt_of_ge hq hb).elim

section Original
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L₀ V₀ V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L₀ V₀ V₁ V₂ V₃ M G₁)
  (hH : H ∈ Source.Hz (one L₀ T V₁) T G₁ M)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L₀)
  (hF9all : ∀ J ∈ Source.Hz (one L₀ T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L₀ V₀ V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V₀ : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339
    L₀ (one L₀ T V₁) (plus L₀ T V₁) T M V₀ V₁)
  (hK : (K.subgroupOf H).IsCComponent)

include d hH h hF9all hcentral hcomm hsource hK

/-- The table consequence discharges the literal F.9.18 premise of the
original cover-recognition consumer. Construction of this classified action
and its component isomorphism remains with the F.9.18 assembly. -/
theorem source_catalogue_of_table [Finite V]
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (ht : TableB45 ρ (generalizedFitting D)) (hq : quadraticRatio ρ ≤ 2)
    (e : Source.starImage H K ≃* generalizedFitting D) :
    ComponentModelOrSuzuki (Source.starImage H K) := by
  let : IsQuasisimple (generalizedFitting D) := hyp.quasisimple
  exact CoverModels.original_catalogue_or_suzuki d hH h hF9all hcentral hcomm hsource hK
    (f918Models_transport e (f918Models_of_table ρ ht hq))
/-- An FF action with the literal component as generalized Fitting subgroup
supplies the complete cover-recognition premise using the proved B.4.2. -/
theorem source_catalogue_of_ff [Finite V]
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hff : IsFFModule ρ)
    (e : Source.starImage H K ≃* generalizedFitting D) :
    ComponentModelOrSuzuki (Source.starImage H K) := by
  exact CoverModels.original_catalogue_or_suzuki d hH h hF9all hcentral hcomm hsource hK
    (f918Models_transport e (f918Models_of_ff ρ hyp hff))

/-- The complete B.4.5 consequence discharges the literal F.9.18 premise,
retaining the supplied classified action rather than merely a family tag. -/
theorem source_catalogue_of_b45 [Finite V]
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hb : B45Conclusion ρ) (hq : quadraticRatio ρ ≤ 2)
    (e : Source.starImage H K ≃* generalizedFitting D) :
    ComponentModelOrSuzuki (Source.starImage H K) := by
  exact CoverModels.original_catalogue_or_suzuki d hH h hF9all hcentral hcomm hsource hK
    (f918Models_transport e (f918Models_of_b45 ρ hyp hb hq))
end Original

end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
