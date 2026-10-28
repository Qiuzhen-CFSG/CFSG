module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.LateSections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.SourceB42

/-!
# Removing the ratio-one rows of the corrected classification

The actual strong offender on the classified late section excludes every
ratio-one row of the corrected B.4.2 contract. The surviving component
models are SL₃ over a binary field, Sp₄ over a larger binary field, A₆,
SL₄(2), and SL₅(2), with actual group equivalences. The reducible B.5.1
rows have components on the same list.

This is not yet the comparison with the binary list from (l). In particular
the exceptional-model exclusions still need to compare the surviving
carriers with A₇, G₂(2)' and the triple cover. Module identifications are
retained separately by `exists_strong_source_section`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2,
printed p.86; B.5.1, pp.99–103; the first paragraph on p.1145.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases

open Subgroup Representation Representation.BinaryOffender
open ReducedModels ComponentReduction ModelReduction BinaryModels
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open scoped IsMulCommutative

/-- The corrected projective-line contract has the same surviving strict
rows, without ever using the legacy triple-cover offender convention. -/
theorem strict_model_of_corrected_case
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {J P : Subgroup D}
    (h : ProjectiveLine.IrreducibleActionCase ρ J P)
    (hq : quadraticRatio ρ ≠ 1) : StrictRatioModel J := by
  cases h with
  | linearTwo _ _ _ _ hr => exact (hq hr).elim
  | linearThree F _ e _ => exact Or.inl ⟨F, ⟨e.groupEquiv⟩⟩
  | symplectic F hn _ e _ => exact Or.inr (Or.inl ⟨F, hn, ⟨e.groupEquiv⟩⟩)
  | symplecticTwo e _ =>
    exact Or.inr (Or.inr (Or.inl ⟨e.subgroupEquiv.trans binarySymplecticDerivedEquiv⟩))
  | g2 _ _ _ _ _ hr => exact (hq hr).elim
  | g2Two _ _ hr => exact (hq hr).elim
  | symmetric _ _ _ _ hr => exact (hq hr).elim
  | alternatingSix _ _ _ hr => exact (hq hr).elim
  | alternatingSeven _ _ _ _ _ hr => exact (hq hr).elim
  | tripleSix _ _ hr => exact (hq hr).elim
  | binaryLinear d hd _ e _ =>
    rcases hd with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.groupEquiv⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.groupEquiv⟩)))
  | orthogonalSix _ _ _ _ hr => exact (hq hr).elim
  | symmetricEight _ e _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e.subgroupEquiv.trans alternatingEightLinearEquiv⟩)))
  | exteriorFive _ _ _ _ _ hr => exact (hq hr).elim

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (s : StrongPlacement r)

include s in
/-- Filter all four B.5.1 alternatives using the actual later strong
subgroup. This keeps the component as a subgroup of the late actor. -/
theorem strict_late_component_model
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ) :
    StrictRatioModel ((starImage H L).subgroupOf (lateActor r.placed.action)) := by
  obtain ⟨c, _, hq⟩ := exists_strong_source_section r s sections orbits source
  cases c.clause_one with
  | irreducible _ _ _ h _ => exact strict_model_of_corrected_case _ h hq
  | doubleThree F _ e _ _ => exact Or.inl ⟨F, ⟨e.groupEquiv⟩⟩
  | naturalDual d hd _ he =>
    obtain ⟨e⟩ := he
    rcases hd with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.groupEquiv⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.groupEquiv⟩)))
  | repeatedNatural d n hd _ _ _ he =>
    obtain ⟨e⟩ := he
    rcases hd with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.groupEquiv⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.groupEquiv⟩)))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases
