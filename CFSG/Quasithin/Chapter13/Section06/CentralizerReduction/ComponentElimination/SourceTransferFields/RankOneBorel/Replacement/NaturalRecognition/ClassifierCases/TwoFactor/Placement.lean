module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.Quasisimple
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.Groups
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product

/-!
# Locating a rank-one component in the native two-factor alternative

A component lies in one of the two literal direct factors, by the component
normal-subgroup dichotomy and perfectness. The concrete actor isomorphisms
then exclude all SL₃ rows, including repeated and exceptional modules. In
the SL₂ row the component fills the factor; in the S₅ row the supplied
isomorphism carries it onto the actual alternating subgroup. Restriction
therefore leaves precisely the two module actions needed by 13.6.18.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(3),
printed p.105, and the first paragraph of 13.6.18, p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
private def legacyField (F : BinaryField) :
    CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField where
  Carrier := F.Carrier
  degree := F.degree
  degree_pos := F.degree_pos
  card_eq := F.card_eq

private def swapProduct {D : Type*} [Group D] {A B : Subgroup D}
    (p : InternalProduct A B) : InternalProduct B A where
  equiv := MulEquiv.prodComm.trans p.equiv
  apply_eq b a := by
    have ha : p.equiv (a,1) = a := by simpa using p.apply_eq a 1
    have hb : p.equiv (1,b) = b := by simpa using p.apply_eq 1 b
    calc
      p.equiv (a,b) = p.equiv ((1,b) * (a,1)) := by simp
      _ = (b : D) * (a : D) := by rw [map_mul, hb, ha]

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C A B : Subgroup D}

omit [Finite D] in
/-- A component of the literal internal product lies in one original factor. -/
theorem component_le_factor (hC : IsComponent D C) (p : InternalProduct A B) :
    C ≤ A ∨ C ≤ B := by
  let : A.Normal := (swapProduct p).second_normal
  let : B.Normal := p.second_normal
  rcases hC.normal_dichotomy A with h | ha
  · exact Or.inl h
  rcases hC.normal_dichotomy B with h | hb
  · exact Or.inr h
  have ht : (⊤ : Subgroup D) ≤ centralizer (C : Set D) := by
    rw [← p.sup_eq_top]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  have hc : ⁅C,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (le_top.trans ht)
  let := hC.2
  rw [commutator_eq_self] at hc
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  exact ((Subgroup.nontrivial_iff_ne_bot C).mp inferInstance hc).elim

/-- The two genuine actions left on a quotient summand after locating the
marked rank-one component. -/
inductive FactorComponentAction (U : Subrepresentation ρ) : Prop
  | natural (E : BinaryField)
      (action : ActionEquiv (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype)
        (linearNatural E 2))
  | alternatingFive
      (action : ActionEquiv (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype)
        (alternatingNatural 5))

omit [Finite D] in
private theorem moved_mono (h : C ≤ A) : moved ρ C ≤ moved ρ A := by
  apply Submodule.span_mono
  rintro _ ⟨g,hg,v,hv,rfl⟩
  exact ⟨g,h hg,v,hv,rfl⟩

/-- All five source rows are handled for either literal factor. In the S₅
row the given actor equivalence identifies the marked component with A₅. -/
theorem factor_action (hC : IsComponent D C) (hCA : C ≤ A)
    (F : BinaryField) (hF : 1 < F.degree) (e : C ≃* SL(2,F.Carrier))
    (U : Subrepresentation ρ) (h : SourceFactorCase ρ A U) :
    moved ρ C ≤ U.toSubmodule ∧ FactorComponentAction (C := C) U := by
  have hm : ClassicalGroup.IsPSL C 2 (2 ^ F.degree) :=
    ⟨F.Carrier, inferInstance, inferInstance, F.card_eq,
      ⟨e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩⟩
  cases h with
  | natural hu hn =>
    refine ⟨hu ▸ moved_mono hCA, ?_⟩
    cases hn with
    | linearTwo E a =>
      obtain ⟨a⟩ := a
      have heq := (CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.GroupComparisons.linearTwo hC hCA (by omega) hm (legacyField E) a.groupEquiv).1
      subst A
      exact .natural E a
    | linearThree E _ a =>
      obtain ⟨a⟩ := a
      exact (CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.GroupComparisons.not_linearThree
        hC hCA hm (legacyField E) a.groupEquiv).elim
    | symmetricFive a =>
      obtain ⟨a⟩ := a
      have hb := (CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.GroupComparisons.symmetricFive
        hC hCA (by omega) hm a.groupEquiv).1
      refine .alternatingFive ⟨((subgroupOfEquivOfLe hCA).symm.trans
        (a.groupEquiv.subgroupMap (C.subgroupOf A))).trans (MulEquiv.subgroupCongr hb),
        a.linearEquiv, ?_⟩
      intro g v
      exact a.intertwines ⟨g, hCA g.property⟩ v
  | doubleNatural E _ hu a =>
    obtain ⟨a⟩ := a
    exact (CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.GroupComparisons.not_linearThree
      hC hCA hm (legacyField E) a.groupEquiv).elim
  | exceptional hu a =>
    exact (CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.GroupComparisons.not_linearThree
      hC hCA hm (legacyField BinaryField.two) a.natural.groupEquiv).elim
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor
