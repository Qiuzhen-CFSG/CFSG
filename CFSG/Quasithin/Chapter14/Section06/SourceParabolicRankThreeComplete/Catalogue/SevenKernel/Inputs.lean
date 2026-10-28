module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.Inputs
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Action
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs

/-!
# Relative block selection for the two original A₇ actions

These contracts isolate the two C.2.7 branches after the full original star
module has been classified. They retain all original Chapter 14 hypotheses
and the literal first-parabolic core. Neither contract assumes this core is
Sylow, a full A₇ two-core quotient, or the preferred-centralizer condition.
The source assembly must prove both contracts before claiming recovery.

Source: Aschbacher--Smith C.1.24(a), pp.130--131, C.2.7(3)(a),(b),(d),
pp.145--147, and original 14.6.10(5), p.1029.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
variable {G : Type*} [Group G] [Finite G]

/-- The full original star action, before recovering its possible cubic kernel. -/
noncomputable abbrev Data (T : Sylow 2 G) (M Mc I H2 : Subgroup G) :=
  AlternatingModels.ActionData
    (starRepresentation (sourceGeneratedComponent T M Mc I H2) (firstCore T M Mc I H2))
    (star T M Mc I H2)

/-- The natural six-space row retains the full actor and component marking. -/
def NaturalRow {T : Sylow 2 G} {M Mc I H2 : Subgroup G}
    (m : Data T M Mc I H2) : Prop :=
  ∃ a : ActionEquiv m.sectionData.space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 7)),
    (star T M Mc I H2).map a.groupEquiv.toMonoidHom = alternatingGroup (Fin 7)

/-- The exceptional row has full A₇ actor on the original moved four-space. -/
def ExceptionalRow {T : Sylow 2 G} {M Mc I H2 : Subgroup G}
    (m : Data T M Mc I H2) : Prop :=
  star T M Mc I H2 = ⊤ ∧ Module.finrank (ZMod 2) m.sectionData.space.toSubmodule = 4

/-- The genuine C.1.24 selection alternative on the original radical. -/
def SelectionConclusion (K R : Subgroup G) : Prop :=
  (∃ D : Subgroup (ChapterB.baumann (R.subgroupOf (K ⊔ R))),
    D.Characteristic ∧ D ≠ ⊥ ∧
      (D.map (ChapterB.baumann (R.subgroupOf (K ⊔ R))).subtype).Normal) ∨
    ChapterC.IsBlock (K.subgroupOf (K ⊔ R))

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Source block selection in the ordinary six-space branch. -/
def NaturalSelectionInput : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    (star T M Mc I d.H2 ≃* alternatingGroup (Fin 7)) →
    ∀ m : Data T M Mc I d.H2, NaturalRow m →
      SelectionConclusion (sourceGeneratedComponent T M Mc I d.H2) (firstCore T M Mc I d.H2)

/-- Source block selection in the exceptional four-space branch. -/
def ExceptionalSelectionInput : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    (star T M Mc I d.H2 ≃* alternatingGroup (Fin 7)) →
    ∀ m : Data T M Mc I d.H2, ExceptionalRow m →
      SelectionConclusion (sourceGeneratedComponent T M Mc I d.H2) (firstCore T M Mc I d.H2)

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel
