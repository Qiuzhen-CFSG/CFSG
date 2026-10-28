module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration.AlternatingSeven.Application
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration.DerivedG2.Application

/-!
# Applying exceptional generation to the original terminal seed

An actual equivalence with any of the four exceptional carriers supplies
the intrinsic generation premise of `exists_terminalPoint_of_component_generation`.
That theorem constructs the seed point from the given `r` and B.2.14 and
marks its literal stabilizer. The individual applications for A₇ and the
derived G₂(2) model are reexported from their own descendants.

The final adapters discharge all four exceptional premises of
`MarkedSeed.generation_of_models` and `exists_terminalPoint_of_binary_generation`.
The independent binary linear theorem and the earlier-source section,
orbit, corrected B.5.1, B.2.14 and 15.3.48 inputs remain with the terminal-seed
assembly owner. No exceptional generation or point-stabilizer equality is
assumed by these adapters.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the quotient
seed and point stabilizers in 15.3.49, printed pp.1144–1145.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration
open Subgroup Representation Representation.BinaryOffender ModelExclusions
open ReducedModels ComponentReduction ModelReduction BinaryModels
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- Discharge all four exceptional branches in the existing binary-model
adapter, retaining only the independent linear generation premise. -/
theorem generation_of_models_of_linear {D : Type*} [Group D] [Finite D]
    (hmodel : BinaryComponentModel D)
    (linear : ∀ n : ℕ, 3 ≤ n → n ≤ 5 →
      SylowThetaGeneration (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    SylowThetaGeneration D :=
  MarkedSeed.generation_of_models hmodel linear
    alternating_six alternating_seven triple_cover g2_derived

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]

/-- The proved alternating six branch marks the original quotient seed. -/
theorem exists_terminalPoint_of_alternating_six
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) (hi : Z.relIndex ZS = 2)
    (e : starImage H L ≃* alternatingGroup (Fin 6)) : Nonempty (TerminalPoint r) := by
  exact exists_terminalPoint_of_component_generation r sections orbits hB214 hZST h48 hi
    (alternating_six.of_mulEquiv e)

/-- The proved triple cover branch marks the original quotient seed. -/
theorem exists_terminalPoint_of_triple_cover
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) (hi : Z.relIndex ZS = 2)
    (e : starImage H L ≃* Atlas.Codes.HexEvenAutomorphisms) : Nonempty (TerminalPoint r) := by
  exact exists_terminalPoint_of_component_generation r sections orbits hB214 hZST h48 hi
    (triple_cover.of_mulEquiv e)

/-- Apply all exceptional generation theorems to the original binary-model
seed construction. The all-model owner supplies the separate linear theorem
and retains the original earlier-source hypotheses. -/
theorem exists_terminalPoint_of_binary_generation_of_linear
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) (hi : Z.relIndex ZS = 2)
    (linear : ∀ n : ℕ, 3 ≤ n → n ≤ 5 →
      SylowThetaGeneration (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    Nonempty (TerminalPoint r) :=
  exists_terminalPoint_of_binary_generation r sections orbits source hB214 hZST h48 hi
    linear alternating_six alternating_seven triple_cover g2_derived

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration
