module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Cases
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Applying the adequate classifier to the actual offender subgroup

Restriction to J(D,V) preserves faithfulness and supplies offender generation.
Its normality makes its two-core a normal two-subgroup of D; hence that core
vanishes. Pulling back J(D,V) in the given SQTK cover supplies the same original
group class in the B.5.3 hypothesis. The component is retained by the actual
subgroup inclusion and its original isomorphism to PSL₃(2).

The order-168 subgroup rules out the trivial actor and the S₃ alternative.
The other source alternatives remain intact, including every module clause.
This is applicability and branch reduction, not the module classification.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.3 and B.5.6,
printed pp.104–105, and the proof of 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier
open ChapterB ChapterB.QuasisimpleSource
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {𝒦 : GroupClass.{u}} {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

/-- Every B.5.3 hypothesis holds on the literal subgroup of best offenders. -/
theorem offender_hypothesis (h : ClassifierApplicability 𝒦 ρ C) :
    SourceInduction.FFHypothesis 𝒦 (ρ.comp (offenderSubgroup ρ).subtype) := by
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  have hn : ((pCore 2 J).map J.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hl : (pCore 2 J).map J.subtype ≤ pCore 2 D :=
    le_sSup ⟨hn, pCore_isPGroup.map _⟩
  rw [h.twoCore] at hl
  refine ⟨h.finite_module, h.faithful.comp J.subtype_injective,
    ((pCore 2 J).map_eq_bot_iff_of_injective J.subtype_injective).mp
      (le_bot_iff.mp hl), offenderSubgroup_restrict_eq_top ρ, ?_⟩
  obtain ⟨q⟩ := h.quotient
  exact ⟨q.subgroup J⟩

/-- The restricted component has the supplied actual model, through inclusion. -/
noncomputable def offender_component_equiv (h : ClassifierApplicability 𝒦 ρ C)
    (e : C ≃* Matrix.PSL3Two.PSL) :
    C.subgroupOf (offenderSubgroup ρ) ≃* Matrix.PSL3Two.PSL :=
  (subgroupOfEquivOfLe h.le_offenders).trans e

/-- Normality is relative to the actual classifier actor. -/
theorem offender_component_normal (h : ClassifierApplicability 𝒦 ρ C) :
    (C.subgroupOf (offenderSubgroup ρ)).Normal := by
  let : C.Normal := h.normal
  exact Subgroup.normal_subgroupOf

/-- The actual order-168 subgroup excludes a trivial ambient actor. -/
theorem nontrivial_of_equiv (e : C ≃* Matrix.PSL3Two.PSL) : Nontrivial D := by
  have hc : Nat.card C = 168 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact Function.Injective.nontrivial C.subtype_injective

/-- B.5.6(2) cannot contain the specified component. -/
theorem no_symmetricThree (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SourceInduction.SymmetricThreeCase ρ) : False := by
  have hc : Nat.card C = 168 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hd : Nat.card D = 6 := by
    rw [Nat.card_congr c.equiv.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    decide
  have hi := Nat.card_le_card_of_injective C.subtype C.subtype_injective
  omega

/-- Apply the full adequate implication with its actual cover and representation. -/
theorem offender_alternative (h : ClassifierApplicability 𝒦 ρ C)
    (e : C ≃* Matrix.PSL3Two.PSL)
    (classification : SourceInduction.AdequateClassificationInput.{u,v} 𝒦) :
    SourceInduction.NontrivialAdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype) := by
  let : Nontrivial (offenderSubgroup ρ) :=
    nontrivial_of_equiv (offender_component_equiv h e)
  exact (classification _ _ _ (offender_hypothesis h)).of_nontrivial _

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier
