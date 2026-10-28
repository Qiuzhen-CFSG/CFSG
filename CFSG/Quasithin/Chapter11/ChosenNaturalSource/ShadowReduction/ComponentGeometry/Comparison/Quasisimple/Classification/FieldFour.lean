module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.CentralQuotients
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.OddExtensions
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.SpecificGroups.Janko1.Model
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockGeometry
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers.Center
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import GorensteinWalter.SL2ProjectiveCover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.Complete

/-!
# Eliminating the exceptional field-four component list in 11.4.2

The complete exceptional list of 11.1.1 retains its central covers and
odd-kernel extensions. The central-quotient restrictions from B.4/B.5 exclude
its sporadic, odd linear and unitary models. A quasisimple group with trivial
two-core cannot surject onto odd-characteristic SL2, removing the extension
rows. Only A7 and its three-cover remain on the original two-core quotient.

Alternating representation recognition then proves that the actual FF
component image is A7, even if the original action was reducible. Applying
the completed field-automorphism contradiction at the same seed quotient
marking proves component equality throughout this exceptional branch.
The final consumer reduces the full 11.1.1 alternatives to their
characteristic-two Lie rows under strict comparison.

The preceding source geometry and seed marking retain their existing
producers; qt-d-1222-shadow-components discharges them in final assembly.
The remaining Lie rows, proper-overcomponent comparison and Hall/Cartan
argument remain with qt-d-1222-shadow-component-comparison. This module
does not claim equality for all characteristic-two models at field size four.
Source: Aschbacher--Smith 11.1.1 and 11.4.2, printed pp.761,776--777.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
open Chapter1.Section02.LocalModels LocalGeometry.Components
variable {A : Type*} [Group A] [Finite A] [IsQuasisimple A]

private def centerlessTargetEquiv {B : Type*} [Group B] [Nontrivial B]
    (f : A →* B) (hf : Function.Surjective f) (hz : center B = ⊥) :
    (A ⧸ center A) ≃* B :=
  (IsQuasisimple.centralQuotientEquiv f hf).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)

private theorem centerless_of_simple_perfect {B : Type*} [Group B]
    [IsSimpleGroup B] [Group.IsPerfect B] : center B = ⊥ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center B) inferInstance).resolve_right
    (fun he => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp he))

omit [Finite A] in
private theorem not_sporadic_mark (h : CentralQuotientRestrictions (A ⧸ center A))
    {B : Type*} [Group B] (e : A ≃* B) (hz : center B = ⊥)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel B) : False := by
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  let : Nontrivial B := e.injective.nontrivial
  exact h.not_sporadic (hm.of_mulEquiv (centerlessTargetEquiv e.toMonoidHom e.surjective hz))

omit [Finite A] in
private theorem psl2_central_quotient {q : ℕ} (hq : 3 < q)
    (hm : ClassicalGroup.IsPSL A 2 q) : ClassicalGroup.IsPSL (A ⧸ center A) 2 q := by
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three F (by omega)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  exact ⟨F,inferInstance,inferInstance,hc,⟨centerlessTargetEquiv e.toMonoidHom e.surjective
    (Group.IsPerfect.center_quotient_center_eq_bot _)⟩⟩

omit [Finite A] in
private theorem not_linear_three_five (h : CentralQuotientRestrictions (A ⧸ center A))
    (hm : ClassicalGroup.IsPSL A 3 5 ∨ Source.IsSL A 3 5) : False := by
  apply h.not_odd_psl3 5 (by decide) (by decide)
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hc,⟨centerlessTargetEquiv e.toMonoidHom e.surjective
      (Group.IsPerfect.center_quotient_center_eq_bot _)⟩⟩
  · obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    let f := (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 3) F))).comp e.toMonoidHom
    exact ⟨F,inferInstance,inferInstance,hc,⟨centerlessTargetEquiv f
      ((QuotientGroup.mk'_surjective _).comp e.surjective)
      (Group.IsPerfect.center_quotient_center_eq_bot _)⟩⟩

private theorem psu_five_simple {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5) :
    IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 5 1 (by decide)
    (by simpa using hc) (by simpa using hconj)
  exact BenderSuzuki.External.huppert_II_10_13 J 5 (by decide) hc (by simpa using hf)

omit [Finite A] in
private theorem not_unitary_three_five (h : CentralQuotientRestrictions (A ⧸ center A))
    (hm : ClassicalGroup.IsPSU A 3 5 ∨ IsSU A 3 5) : False := by
  have hn : 5 = 3 := by
    apply h.odd_psu3 5 (by decide) (by decide)
    rcases hm with hm | hm
    · obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := hm
      let := psu_five_simple J hc hconj
      let : Group.IsPerfect (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      exact ⟨F,inferInstance,inferInstance,J,hc,hconj,
        ⟨centerlessTargetEquiv e.toMonoidHom e.surjective centerless_of_simple_perfect⟩⟩
    · obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := hm
      let := psu_five_simple J hc hconj
      let f := J.specialToProjective.comp e.toMonoidHom
      have hf : Function.Surjective f := J.specialToProjective_surjective.comp e.surjective
      let : Group.IsPerfect (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Group.IsPerfect.ofSurjective hf
      exact ⟨F,inferInstance,inferInstance,J,hc,hconj,
        ⟨centerlessTargetEquiv f hf centerless_of_simple_perfect⟩⟩
  omega

/-- Comparing the full q=4 list with FF restrictions leaves only A7 and
its central three-cover on the original two-core quotient. The image
comparison must still determine which covering center acts trivially. -/
theorem fieldFour_alternating (hc : pCore 2 A = ⊥)
    (h : CentralQuotientRestrictions (A ⧸ center A)) (hm : FieldFourOvergroup A) :
    IsAlternating A 7 ∨ IsAlternatingCover A 7 := by
  cases hm with
  | alternating he => exact Or.inl he
  | alternatingCover he => exact Or.inr he
  | primeLinear p hp he =>
    have hp3 : 3 < p := by have := hp.1.two_le; have := hp.2.1; omega
    have hh := h.odd_psl2 p 1 hp.1 (hp.1.odd_of_ne_two (by omega))
      (Or.inl rfl) (by simp only [pow_one]; omega) (by simpa using psl2_central_quotient hp3 he)
    rcases hh with hh | hh | hh <;> have := hp.2.1 <;> omega
  | linearTwentyFive he =>
    have hh := h.odd_psl2 5 2 (by decide) (by decide) (Or.inr rfl) (by decide)
      (psl2_central_quotient (by decide) he)
    rcases hh with hh | hh | hh <;> omega
  | three u he =>
    cases u with
    | false => exact (not_linear_three_five h he).elim
    | true => exact (not_unitary_three_five h he).elim
  | m22 he => exact (not_sporadic_mark h he.some Sporadic.Mathieu.m22_center_eq_bot
      (Or.inl ⟨.m22, (by intro hh; cases hh), ⟨MulEquiv.refl _⟩⟩)).elim
  | m22Cover he => exact (h.not_sporadic (Or.inl ⟨.m22, (by intro hh; cases hh), he.2.2⟩)).elim
  | m23 he => exact (not_sporadic_mark h he.some Sporadic.Mathieu.M23Geometry.m23_center_eq_bot
      (Or.inl ⟨.m23, (by intro hh; cases hh), ⟨MulEquiv.refl _⟩⟩)).elim
  | j1 he =>
    let : Group.IsPerfect Janko1.Model := Group.IsPerfect.ofSurjective (f := he.some.toMonoidHom) he.some.surjective
    exact (not_sporadic_mark h he.some centerless_of_simple_perfect
      (Or.inr ⟨MulEquiv.refl _⟩)).elim
  | j2 he => exact (not_sporadic_mark h he.some
      Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockGeometry.center_eq_bot
      (Or.inl ⟨.j2, (by intro hh; cases hh), ⟨MulEquiv.refl _⟩⟩)).elim
  | j4 he => exact (not_sporadic_mark h he.some Janko4.model_center_eq_bot
      (Or.inl ⟨.j4, (by intro hh; cases hh), ⟨MulEquiv.refl _⟩⟩)).elim
  | hs he => exact (not_sporadic_mark h he.some Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot
      (Or.inl ⟨.hs, (by intro hh; cases hh), ⟨MulEquiv.refl _⟩⟩)).elim
  | ru he => exact (not_sporadic_mark h he.some Rudvalis.LowCentralizers.model_center_eq_bot
      (Or.inl ⟨.ru, (by intro hh; cases hh), ⟨MulEquiv.refl _⟩⟩)).elim
  | nilpotentExtension he => exact (not_odd_sl2_extension hc _ (by decide : Odd 5) he).elim
  | elementaryExtension p hp he => exact (not_odd_sl2_extension hc _
      (hp.1.odd_of_ne_two (by have := hp.2.1; omega)) he).elim


private theorem alternatingSeven_of_irreducible
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] {σ : Representation (ZMod 2) Q U} {K : Subgroup Q}
    (h : ChapterK.RankOne.SourceHypotheses σ K) (hff : IsFFModule σ)
    (e : (K ⧸ center K) ≃* alternatingGroup (Fin 7)) :
    Nonempty (K ≃* alternatingGroup (Fin 7)) := by
  let := h.quasisimple
  obtain ⟨hr,_⟩ := ChapterK.Alternating.source_of_ff_input σ
    ⟨h.sqtk,h.fitting.symm,h.quasisimple,h.faithful,h.irreducible,h.smallCubic,Or.inr ⟨e⟩⟩ hff
  cases hr with
  | six a =>
    let e6 := centerlessTargetEquiv a.restricted.groupEquiv.toMonoidHom
      a.restricted.groupEquiv.surjective (alternatingGroup.center_eq_bot (by simp))
    have hc := Nat.card_congr (e.symm.trans e6).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
  | sevenNatural a => exact ⟨a.restricted.groupEquiv⟩
  | sevenFour _ a => exact ⟨a.groupEquiv⟩
  | tripleSix a =>
    have hc := Nat.card_congr (e.symm.trans
      (ChapterK.Alternating.HexacodeOffenders.quotientEquiv a.restricted)).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc

/-- B.5.1 detects the whole A7 component image from its central quotient.
This uses the proved alternating representation recognition, including the
exclusion of its covering rows, and works for reducible original actions. -/
theorem alternatingSeven_of_source
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] {σ : Representation (ZMod 2) Q U} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ K)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hK : IsQuasisimple K)
    (hff : IsFFModule σ) (e : (K ⧸ center K) ≃* alternatingGroup (Fin 7)) :
    Nonempty (K ≃* alternatingGroup (Fin 7)) := by
  rcases irreducible_realization_of_source c hff with h | h <;>
    rcases h with ⟨W,_,_,_,ρ,hf,hi,hff⟩ <;>
    exact alternatingSeven_of_irreducible
      (ChapterB.SourceClassification.source_hypotheses hsq c.fitting_eq.symm hK hf hi hff) hff e

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The complete field-four source list on the original chosen flag leaves
only the two alternating-seven quotient rows. The FF witness is discharged
by the original Thompson reduction, and the extension kernels are retained. -/
theorem ofFlag_fieldFour_alternating
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : FieldFourOvergroup ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)) :
    let Q := (ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz
    IsAlternating Q 7 ∨ IsAlternatingCover Q 7 :=
  fieldFour_alternating (pCore_quotient_pCore_eq_bot 2)
    (ofFlag_centralQuotientRestrictions S f X z H h hne hstar hlinear h1132 hcent hline hXR) hm

/-- The complete q=4 catalogue determines the actual A7 action image;
the two-core quotient and the image are never identified without a kernel proof. -/
theorem ofFlag_fieldFour_image
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : FieldFourOvergroup ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)) :
    IsAlternating (componentImage (ofFlag S f X z H)) 7 := by
  let E := ofFlag S f X z H
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  obtain ⟨_,_,_,_,_,hff,_⟩ := ofFlag_ff_reduction S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  let : IsQuasisimple (componentImage E) := (action_structure E h hf hne hstar hcent).2.2
  let : IsSimpleGroup (componentImage E ⧸ center (componentImage E)) := IsQuasisimple.simple
  let : Nontrivial (componentImage E) :=
    (QuotientGroup.mk'_surjective (center (componentImage E))).nontrivial
  obtain ⟨hK,⟨d⟩⟩ := source_classification E h hf hne hstar hcent hff
  let : IsQuasisimple (offenderComponent E) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hK).symm
  have he : Nonempty (((E.Kz ⧸ pCore 2 E.Kz) ⧸ center (E.Kz ⧸ pCore 2 E.Kz)) ≃*
      alternatingGroup (Fin 7)) := by
    rcases ofFlag_fieldFour_alternating S f X z H h hne hstar hlinear h1132 hcent hline hXR hm
      with ha | hc
    · obtain ⟨a⟩ := ha
      exact ⟨centerlessTargetEquiv a.toMonoidHom a.surjective
        (alternatingGroup.center_eq_bot (by simp))⟩
    · exact hc.2.2
  obtain ⟨a⟩ := alternatingSeven_of_source d (offenderGroup_sqtk E h) inferInstance
    (offenderAction_ff E hff) ((offenderCentralQuotientEquiv E h hK).trans he.some)
  exact ⟨(subgroupOfEquivOfLe hK).symm.trans a⟩

/-- Source 11.4.2 for the entire field-four alternative of 11.1.1,
using the already completed A7 terminal contradiction. The common original
seed quotient marking is retained for its upstream Cartan producer. -/
theorem ofFlag_eq_of_fieldFour
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : FieldFourOvergroup ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hq : S.field.degree = 2)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hm7 : AlternatingSevenModel (ofFlag S f X z H) :=
    ⟨hq,ofFlag_fieldFour_image S f X z H h hne hstar hlinear h1132 hcent hline hXR hm⟩
  exact AlternatingSeven.ofFlag_false S f X z H h hne hstar
    hlinear h1132 hcent hline hXR hm7 e

/-- The literal full 11.1.1 input in a strict quasisimple comparison now
reduces to its characteristic-two Lie rows. The entire exceptional q=4
branch, including the covering and extension models, has been discharged. -/
theorem ofFlag_lie_of_componentAlternative
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : LocalGeometry.Components.ComponentAlternative (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) :
    LieOvergroup ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) S.field.degree := by
  cases hm with
  | equal he =>
    exact ((h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he).elim
  | lie hl => exact hl
  | four hq hm =>
    exact (hne (ofFlag_eq_of_fieldFour S f X z H h hstar
      hlinear h1132 hcent hline hXR hm hq e)).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
