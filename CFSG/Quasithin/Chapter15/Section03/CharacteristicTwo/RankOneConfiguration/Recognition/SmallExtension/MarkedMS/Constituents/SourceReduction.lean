module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.SourceReduction.Transfer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.SourceReduction.Branches
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.SourceReduction.SmallModels

/-!
# Source action inputs and transfer to the whole component module

The genuine SQTK cover, characteristic-two hypothesis and common Sylow
witness construct B.5.3 for J(I)* acting on U_I. Relative normality and
I = LS identify its generalized Fitting subgroup with the actual L*.
The inclusion U_L -> U_I identifies U_L equivariantly with [U_I,L*];
Irr+ and doubled coordinates transfer through that inclusion, retaining
the actual central quotient in the first case and the entire module in
the second.

Every B.5.6 branch is handled on that same actor. The full quasisimple
conclusion and the marked carrier orders leave either Irr+ on all of U_L
or actual doubled binary SL₃ coordinates. In the latter case, the original
marked intersection has order 24. The coordinate transfer uses the full
moved subrepresentation, never a splitting inferred from its central quotient.

`smallAction_of_source` preserves the requested full classification interface.
`smallAction_of_projectiveLine_source` uses the corrected projective-line
convention recorded in docs/quasithin-proof-basis.md. Neither proof uses the
outer alternative's disputed fixed-space splitting. `smallAction_of_local_source`
also constructs the elementary structure on U_L. Only the universal earlier
classification implication remains explicit, as permitted by this task.

After the actual small marking and relative component conclusions of
15.3.27 are supplied, rank one, minimality, solvable-invariant control and
15.3.29 are not needed again for this unmarked action specialization. The
field and order sieve directly excludes all larger actors, including the
even-degree SL₃ cases; it does not replace 15.3.27(3) by a block exclusion.
Constituent selection and the V₂ marking remain with the parent assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed pp.99–103, B.5.3–6, pp.104–105, and 15.3.26–31, pp.1130–1132.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
open Parabolics.Placement.ModelComparison
open EightGeometry.NaturalModule.Recognition
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- All source hypotheses and the full conditional classification concern
the same actual action; its generalized Fitting subgroup is identified
before any small-model or representation comparison. -/
theorem source_action_inputs (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (hf : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hVT : d.V ≤ (d.T : Subgroup G)) {κ : GroupClass.{u}} (hSQTK : IsSQTK κ I)
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} κ) :
    ∃ (hZI : d.Z ≤ I) (hU : IsElementaryAbelian 2 ((d.UI I).subgroupOf I)),
      let := hU
      FFHypothesis κ (d.thompsonStarAction I hZI) ∧
        FFAlternatives.SourceAlternative (d.thompsonStarAction I hZI) ∧
        IsQuasisimple (generalizedFitting (d.thompsonStar I)) ∧
        generalizedFitting (d.thompsonStar I) =
          (d.starImage I c.L).subgroupOf (d.thompsonStar I) := by
  obtain ⟨hZI, hU, hFF, _⟩ := thompson_source_inputs d hSQTK hVT ⟨P, hP⟩ hf c
  let := hU
  exact ⟨hZI, hU, hFF, classification.general _ _ _ hFF,
    thompson_fitting_quasisimple d c hn hI P hP (d.Z_le_S hVT),
    thompson_fitting_eq_component d c hn hI P hP (d.Z_le_S hVT)⟩


/-- The small-model calculation uses the corrected projective-line source
without reconstructing the obsolete irreducible offender clause. -/
theorem movedSmallAlternative_of_projectiveLineConclusion
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    (hcard : Nat.card L = 168 ∨ Nat.card L = 360 ∨ Nat.card L = 6048)
    (h : ProjectiveLine.QuasisimpleSourceConclusion ρ L) : MovedSmallAlternative ρ L := by
  have reduce (hcase : QuasisimpleActionCase ρ L h.sectionData) :
      MovedSmallAlternative ρ L :=
    movedSmallAlternative_of_sourceConclusion ρ L hcard
      { sectionData := h.sectionData
        fitting_eq := h.fitting_eq
        clause_one := hcase
        nonsplitting_iff := h.nonsplitting_iff
        clause_two := h.clause_two
        clause_three := h.clause_three
        clause_four := h.clause_four
        clause_five := h.clause_five
        clause_six := h.clause_six }
  cases h.clause_one with
  | irreducible hi _ _ _ _ => exact .single (h.sectionData.space_eq ▸ hi)
  | doubleThree F ht e ho hr => exact reduce (.doubleThree F ht e ho hr)
  | naturalDual n hn ht hnat => exact reduce (.naturalDual n hn ht hnat)
  | repeatedNatural n r hn hp hb ht hnat =>
    exact reduce (.repeatedNatural n r hn hp hb ht hnat)

/-- The requested whole-module alternative from the preserved full B.5.6
input, with both local comparison premises discharged. -/
theorem smallAction_of_source (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (hf : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hVT : d.V ≤ (d.T : Subgroup G)) (hYL : d.Yplus ≤ c.L)
    {κ : GroupClass.{u}} (hSQTK : IsSQTK κ I)
    (classification : CompleteClassificationInput.{u,u} κ)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)] :
    SmallActionAlternative (componentAction d c hn hI hf P hP)
      (d.starImage I c.L)
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) := by
  obtain ⟨hZI, hU, hFF, hB, hF, he⟩ :=
    source_action_inputs d c hn hI hf P hP hVT hSQTK classification
  let _ := hU
  obtain ⟨hsource⟩ := quasisimple_source_of_sourceAlternative _ hF hB
  rw [he] at hsource
  have hc : Nat.card ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) = 168 ∨
      Nat.card ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) = 360 ∨
      Nat.card ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) = 6048 := by
    simpa only [Nat.card_congr (componentThompsonEquiv d c).toEquiv] using
      marked_star_card d c hm
  exact smallAction_of_movedAlternative d c hn hI hf P hP hZI hYL
    (movedSmallAlternative_of_sourceConclusion _ _ hc hsource)
    (marked_intersection_card_of_star_card d c hm)

/-- Source-facing specialization using the corrected projective-line
convention. Only the universal earlier FF implication remains explicit. -/
theorem smallAction_of_projectiveLine_source (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (hf : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hVT : d.V ≤ (d.T : Subgroup G)) (hYL : d.Yplus ≤ c.L)
    {κ : GroupClass.{u}} (hSQTK : IsSQTK κ I)
    (classification : ProjectiveLine.CompleteClassificationInput.{u,u} κ)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)] :
    SmallActionAlternative (componentAction d c hn hI hf P hP)
      (d.starImage I c.L)
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) := by
  obtain ⟨hZI, hU, hFF, _⟩ := thompson_source_inputs d hSQTK hVT ⟨P, hP⟩ hf c
  let _ := hU
  have hF := thompson_fitting_quasisimple d c hn hI P hP (d.Z_le_S hVT)
  obtain ⟨hsource⟩ := quasisimple_source_of_projectiveLineAlternative _ hF
    (classification.general _ _ _ hFF)
  rw [thompson_fitting_eq_component d c hn hI P hP (d.Z_le_S hVT)] at hsource
  have hc : Nat.card ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) = 168 ∨
      Nat.card ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) = 360 ∨
      Nat.card ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) = 6048 := by
    simpa only [Nat.card_congr (componentThompsonEquiv d c).toEquiv] using
      marked_star_card d c hm
  exact smallAction_of_movedAlternative d c hn hI hf P hP hZI hYL
    (movedSmallAlternative_of_projectiveLineConclusion _ _ hc hsource)
    (marked_intersection_card_of_star_card d c hm)

/-- Construct the elementary structure as well as the entire action
alternative from the genuine local data and the marked small case. -/
theorem smallAction_of_local_source (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (hf : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hVT : d.V ≤ (d.T : Subgroup G)) (hYL : d.Yplus ≤ c.L)
    {κ : GroupClass.{u}} (hSQTK : IsSQTK κ I)
    (classification : ProjectiveLine.CompleteClassificationInput.{u,u} κ)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    let _ := component_internal_elementary d c hf P hP
    SmallActionAlternative (componentAction d c hn hI hf P hP)
      (d.starImage I c.L)
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) := by
  let _ := component_internal_elementary d c hf P hP
  exact smallAction_of_projectiveLine_source d c hn hI hf P hP hVT hYL hSQTK classification hm


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
