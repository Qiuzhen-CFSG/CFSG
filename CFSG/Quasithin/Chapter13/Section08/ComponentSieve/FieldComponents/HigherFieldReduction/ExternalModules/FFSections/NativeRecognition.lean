module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NativeSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.ActionCases
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.ActionSieve

/-!
# Corrected B.4.2 on the surviving external field constituents

The proved native source classifier is applied with its full known-simple
catalogue and exact faithful irreducible FF hypotheses. For a centerless
component its cubic-cover case is impossible, so all remaining action and
offender clauses transport literally to the established model sieves.
The unitary comparison instead extracts the component models directly from
the corrected list, without using either triple-cover offender convention.

This gives natural or marked-five constituents for PSL₂, natural coordinates
with the original field size and ratio one half for odd-degree PSL₃, and
excludes even-degree PSU₃. NativeLayers applies the first result to the
literal external Borel layer. The field-sieve owner retains construction of
the original FF sections and the final external contradictions.
Source: Aschbacher–Smith, B.4.2 and 13.8.20(a), pp.86,954–955.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.NativeRecognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
universe u v w z
private def field (F : ChapterB.QuasisimpleSource.BinaryField) : BinaryField where
  Carrier := F.Carrier
  degree := F.degree
  degree_pos := F.degree_pos
  card_eq := F.card_eq

private def action {D E V W : Type*} [Group D] [Group E] [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    (a : ChapterB.QuasisimpleSource.ActionEquiv ρ σ) : ActionEquiv ρ σ :=
  ⟨a.groupEquiv,a.linearEquiv,a.intertwines⟩

private def marked {D E V W : Type*} [Group D] [Group E] [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    {H L : Subgroup D} {M : Subgroup E}
    (a : ChapterB.QuasisimpleSource.MarkedActionEquiv ρ H L σ M) :
    MarkedActionEquiv ρ H L σ M :=
  ⟨action a.action,a.contained,a.subgroupEquiv,a.compatible⟩

private theorem centerless_actionCase {D : Type u} [Group D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {L J : Subgroup D}
    (hz : center L = ⊥)
    (hc : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L J) :
    IrreducibleActionCase ρ L J := by
  cases hc with
  | linearTwo F hj e ho hr => exact .linearTwo (field F) hj (action e) ho hr
  | linearThree F hj e hr => exact .linearThree (field F) hj (action e) hr
  | symplectic F hn hj e hr => exact .symplectic (field F) hn hj (action e) hr
  | symplecticTwo e hr => exact .symplecticTwo (marked e) hr
  | g2 F hn hj e ho hr => exact .g2 (field F) hn hj (action e) ho hr
  | g2Two e ho hr => exact .g2Two (marked e) ho hr
  | symmetric n hn e ho hr => exact .symmetric n hn (marked e) ho hr
  | alternatingSix hj e ho hr => exact .alternatingSix hj (action e) ho hr
  | alternatingSeven hj ht e hd ho hr => exact .alternatingSeven hj ht e hd ho hr
  | tripleSix _ a _ =>
    have hh := Nat.card_congr a.centerEquiv.toEquiv
    rw [hz,card_bot] at hh
    norm_num [Nat.card_zmod] at hh
  | binaryLinear n hn hj e hr => exact .binaryLinear n hn hj (action e) hr
  | orthogonalSix hj ht e ho hr => exact .orthogonalSix hj ht (action e) ho hr
  | symmetricEight ht e hr => exact .symmetricEight ht (marked e) hr
  | exteriorFive hj ht e hd ho hr => exact .exteriorFive hj ht e hd ho hr

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

private theorem native_model {L H : Subgroup D}
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) : QuasisimpleModel L := by
  cases h with
  | linearTwo F _ e _ _ => exact .linearTwo (field F) e.groupEquiv
  | linearThree F _ e _ => exact .linearThree (field F) e.groupEquiv
  | symplectic F _ _ e _ => exact .symplecticFour (field F) e.groupEquiv
  | symplecticTwo e _ =>
    exact .alternatingSix (e.subgroupEquiv.trans binarySymplecticDerivedEquiv)
  | g2 F _ _ e _ _ => exact .g2 (field F) e.groupEquiv
  | g2Two e _ _ => exact .g2DerivedTwo e.subgroupEquiv
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · exact .linearTwo BinaryField.four (e.subgroupEquiv.trans alternatingFiveLinearEquiv)
    · exact .alternatingSeven e.subgroupEquiv
  | alternatingSix _ e _ _ => exact .alternatingSix e.groupEquiv
  | alternatingSeven _ _ e _ _ _ => exact .alternatingSeven e
  | tripleSix _ h _ => exact .tripleSix h.centerEquiv h.quotientEquiv
  | binaryLinear d hd _ e _ =>
    rcases hd with rfl | rfl
    · exact .linearFourTwo e.groupEquiv
    · exact .linearFiveTwo e.groupEquiv
  | orthogonalSix _ _ e _ _ =>
    exact .linearFourTwo (e.groupEquiv.trans alternatingEightLinearEquiv)
  | symmetricEight _ e _ =>
    exact .linearFourTwo (e.subgroupEquiv.trans alternatingEightLinearEquiv)
  | exteriorFive _ _ e _ _ _ => exact .linearFiveTwo e


variable [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V)

private theorem recognized (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hz : center (generalizedFitting D) = ⊥) (hff : IsFFModule ρ) :
    IrreducibleActionCase ρ (generalizedFitting D) (offenderSubgroup ρ) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨A,hA⟩ := h.exists_bestOffender hff
  exact centerless_actionCase ρ hz
    (ChapterB.SourceClassification.actionCase_of_bestOffender h.sqtk rfl h.quasisimple
      h.faithful h.irreducible hA.bestOffender)

/-- Native B.4.2 leaves exactly the natural or marked S₅ constituent for
an actual PSL₂ component, including the original field exponent. -/
theorem linearTwo_constituent (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hff : IsFFModule ρ) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (generalizedFitting D) 2 (2^n)) :
    LinearTwo.ConstituentCase ρ (generalizedFitting D) (offenderSubgroup ρ) n := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hz : center (generalizedFitting D) = ⊥ :=
    LinearTwo.NoStrongMoved.psl_center_bot _ e
  exact LinearTwo.constituentCase_of_full_list ρ
    ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,h.quasisimple⟩ hn
    ⟨F,hF,hfin,hcard,⟨e⟩⟩ (recognized ρ h hz hff)

/-- The actual even-degree unitary carrier is excluded from faithful
irreducible FF actions using the corrected native source classification. -/
theorem unitary_not_ff (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    {Q : Type*} [Field Q] [Finite Q]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 Q)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (hQ : Nat.card Q = 2 ^ (2*n))
    (hconj : ∀ x, J.conj x = x ^ (2^n))
    (e : generalizedFitting D ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    ¬ IsFFModule ρ := by
  intro hff
  -- The component model projection does not inspect the corrected offender clause.
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨A,hA⟩ := h.exists_bestOffender hff
  have hc := ChapterB.SourceClassification.actionCase_of_bestOffender h.sqtk rfl h.quasisimple
    h.faithful h.irreducible hA.bestOffender
  exact RankTwo.unitary_not_quasisimpleModel_even J hn heven hQ hconj
    (RankTwo.transport_quasisimpleModel e.symm (native_model ρ hc))

/-- The odd-degree ternary linear FF constituent has natural coordinates
and ratio one half, with its field recovered from the original marking. -/
theorem linearThree_natural (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hff : IsFFModule ρ) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2^n)
    (e : generalizedFitting D ≃* PSL(3,F)) :
    ∃ B : BinaryField, Nat.card B.Carrier = Nat.card F ∧
      offenderSubgroup ρ = generalizedFitting D ∧
      Nonempty (ActionEquiv (ρ.comp (generalizedFitting D).subtype) (linearNatural B 3)) ∧
      quadraticRatio ρ = 1 / 2 := by
  have hz : center (generalizedFitting D) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro g hg
    have hh := (centerCongr e ⟨g,hg⟩).property
    change e g ∈ center PSL(3,F) at hh
    rw [RankTwo.projectiveThree_center_eq_bot ho hF,mem_bot] at hh
    exact mem_bot.mpr (e.injective (hh.trans e.map_one.symm))
  exact RankTwo.natural_of_full_list ρ hn ho hF e (recognized ρ h hz hff)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.NativeRecognition
