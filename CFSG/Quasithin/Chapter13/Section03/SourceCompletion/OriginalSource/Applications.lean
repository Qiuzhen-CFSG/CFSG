module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalSource.Module
public import CFSG.Quasithin.Chapter13.Section03.SourceComponentRigidity
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful
public import CFSG.Quasithin.Chapter14.Section08.SourceCases

/-!
# The original unitary source theorem and the actual D branch

The earlier faithful-family catalogue makes the original component maximal.
Chapter12 structure selects an actual Irr⁺ module; its seven-row theorem and
the earlier fixed-space clause construct the whole natural unitary marking.
The completed original argument then excludes the literal L/O₂(L) quotient.

For the source's faithful quotient L/C_L(V), the canonical surjection from
L/O₂(L) is bijective in the putative U₃(3) row: the five-model order bound
matches its image of order 6048. This preserves the actual quotient map.
The resulting exclusion supplies `UnitaryExclusion` and is applied to the
existing five-row Theorem D dispatcher with its multiple-overgroup guard.

The structural 12.2.2 and recognition 12.2.13 parameters still use their
preserved universal APIs. Their same-G,T specialization remains work in
`qt-d-13316-source`; the earlier source proofs and other D branches retain
final discharge at `qt-theorem-d`. No unconditional classification is claimed.
Source: Aschbacher--Smith 13.3.2,13.3.16--20 and 14.8.2,
printed pp.884--885,894--896,1079.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory ChapterE OriginalPlaneCentralizers
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Noncentrality.SupercriticalSource
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem maximal_of_source1332 (h : Hypothesis1331 T L)
    (h1332 : Source1332OneTwo T) : L ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hL := ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff
    T L).mp h.local_component).1
  obtain ⟨I,hI,hLI⟩ := Chapter1.exists_mem_LStar_ge hL
  have hf := Chapter1.Section02.Adequate.faithful_local_overgroup T
    (h.qtke.evenCharacteristic T) h.local_component hI.1 hLI
  have he := local_eq_of_midSize hI.1 hL hLI (h1332 I hf).2
  exact he.symm ▸ hI

/-- The original core quotient exclusion, with module and flag constructed
from the preceding source theorems. The universal structural/recognition
APIs are retained explicitly; this is not their ambient-local specialization. -/
theorem unitary_original_exclusion_of_module_sources
    (h : Hypothesis1331 T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : OriginalFixedModule1332At T L)
    (five : OriginalAlternatingFiveModules1332At T L) :
    ¬ ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 3 := by
  rintro ⟨K,_,_,J,hK,hJ,⟨eJ⟩⟩
  let eL := eJ.trans (J.projectiveEquivBinaryG2Derived hK hJ)
  have hmax := maximal_of_source1332 h h1332
  have h12 := unitary_original_hypothesis1223 h hmax eL
  obtain ⟨V,⟨D⟩⟩ := (structural G T L h12).2.1
  let := D.elementary
  obtain ⟨e,E,he⟩ := unitary_chosen_natural_marking h D eL (modules L V h12 D) fixed
  let s : Context T L V := ⟨h,hmax,eL,D,structural,e,E,he⟩
  exact unitary_original_false_without_local_premises s earlier h1332 fixed five

/-- Source 13.3.16 for the faithful quotient L/C_L(V), using the literal
map from L/O₂(L). Its surjectivity and the five-model bound force this map
to be an isomorphism in the putative U₃(3) row. -/
theorem unitary_original_faithful_quotient_exclusion
    (h : Hypothesis1331 T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : OriginalFixedModule1332At T L)
    (five : OriginalAlternatingFiveModules1332At T L) :
    letI := D.actionCentralizer_normal
    ¬ ClassicalGroup.IsPSU (L ⧸ (centralizer (V : Set G)).subgroupOf L) 3 3 := by
  let := D.actionCentralizer_normal
  rintro ⟨K,_,_,J,hK,hJ,⟨eJ⟩⟩
  have he : Nat.card (L ⧸ (centralizer (V : Set G)).subgroupOf L) = 6048 :=
    (Nat.card_congr eJ.toEquiv).trans
      (BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.card_projective J hK hJ)
  have hle := Nat.card_le_card_of_surjective D.coreToFaithful D.coreToFaithful_surjective
  have hcards := (h1332 L h.local_component).2.card
  have hcard : Nat.card (L ⧸ pCore 2 L) =
      Nat.card (L ⧸ (centralizer (V : Set G)).subgroupOf L) := by
    rw [he] at hle ⊢
    rcases hcards with hh | hh | hh | hh | hh <;>
      (change Nat.card (L ⧸ pCore 2 L) = _ at hh) <;> omega
  let e : (L ⧸ pCore 2 L) ≃*
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) :=
    MulEquiv.ofBijective D.coreToFaithful
      ((Nat.bijective_iff_surjective_and_card D.coreToFaithful).mpr
        ⟨D.coreToFaithful_surjective,hcard⟩)
  exact unitary_original_exclusion_of_module_sources h structural earlier modules
    h1332 fixed five ⟨K,inferInstance,inferInstance,J,hK,hJ,⟨e.trans eJ⟩⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion

namespace CFSG.Quasithin.Chapter14.Section08.SourceCases
open Subgroup Theory.GroupTheory Chapter12.Section02 Chapter13.Section03.SourceCompletion
open Chapter1.Section02.LocalModels
open Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Supply the actual D dispatcher with the proved unitary branch.
The module/catalogue inputs are requested only after its original multiple-
overgroup guard. Structure and 12.2.13 still use their preserved universal APIs. -/
theorem unitaryExclusion_of_source_inputs
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (modules : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (catalogue : Catalogue G)
    (fixed : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      OriginalFixedModule1332At T L)
    (five : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      OriginalAlternatingFiveModules1332At T L) : UnitaryExclusion G := by
  intro T L hmany d
  exact unitary_original_exclusion_of_module_sources (hypothesis1331 d)
    structural earlier (modules T hmany) (catalogue T L hmany d)
    (fixed T L hmany) (five T L hmany)

/-- Apply the constructed unitary exclusion in the existing five-row D split.
The independent nonunitary branches and earlier-source proofs remain with
`qt-theorem-d`; this application does not assert the final classification. -/
theorem theoremDModel_or_five_of_unitary_source_inputs
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (modules : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (catalogue : Catalogue G)
    (fixed : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      OriginalFixedModule1332At T L)
    (fiveModules : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      OriginalAlternatingFiveModules1332At T L)
    (caseOne : Chapter14.Section03.CaseOneSource.Earlier1332CaseOne.{u})
    (six : SixRecognition G) (nonabelian : NonabelianRecognition G)
    (abelian : AbelianRecognition G)
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) :
    ClassificationModels.IsTheoremDModel G ∨ ∃ L : Subgroup G,
      Maximal (Chapter13.Section08.TransvectionRecognition.Component.ModelExtension.Counterexample T) L ∧
      IsAlternating (L ⧸ pCore 2 L) 5 :=
  theoremDModel_or_five_counterexample structural caseOne catalogue
    (unitaryExclusion_of_source_inputs structural earlier modules catalogue fixed fiveModules)
    six nonabelian abelian h T hmany hne

end CFSG.Quasithin.Chapter14.Section08.SourceCases
