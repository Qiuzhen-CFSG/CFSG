module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerate
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernel

/-!
# Conditional assembly of the nondegenerate model exclusions

The literal G.12 input construction and residual identification feed three
independent source obligations: recognition, symplectic residual exclusion,
and exclusion of the orthogonal and natural SL₂(4) rows. Once those explicit
premises are discharged, the existing same-constituent consumer yields the
faithful isotropic dual pair. This is a conditional assembly, not a proof
of the outstanding recognition or model obstructions.

Source: Aschbacher--Smith G.10.15, printed p.363.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)


include s

/-- Assemble the original nondegeneracy contradiction from recognition of the
actual action and the separate exclusions of its three residual model rows. -/
theorem not_nondegenerate_of_model_inputs
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hrecognition : ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i →
      ChapterG.Section12.ResidualModel
        (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I))
    (hsymplectic : (B.restrict I).Nondegenerate →
      s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
        (ChapterG.Section12.formStabilizer (B.restrict I)) → False)
    (horthogonal : (B.restrict I).Nondegenerate →
      ∀ q : QuadraticForm (ZMod 2) I, q.polarBilin = B.restrict I →
        s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
          q.isometrySubgroup → False)
    (hnatural : (B.restrict I).Nondegenerate →
      ChapterG.Section12.NaturalSL2Four s.constituentLinearAction.range → False) :
    ¬ (B.restrict I).Nondegenerate := by
  intro hnd
  rcases s.nondegenerate_models_of_recognition hproper hnd hrecognition with h | h | h
  · exact hsymplectic hnd h
  · obtain ⟨q,hq,h⟩ := h
    exact horthogonal hnd q hq h
  · exact hnatural hnd h

/-- The model obligations feed the published faithful-dual-pair consumer for
the very same selected constituent; they remain explicit until their owners
prove the recognition and exclusion theorems. -/
theorem faithful_data_of_nondegenerate_model_inputs
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hrecognition : ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i →
      ChapterG.Section12.ResidualModel
        (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I))
    (hsymplectic : (B.restrict I).Nondegenerate →
      s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
        (ChapterG.Section12.formStabilizer (B.restrict I)) → False)
    (horthogonal : (B.restrict I).Nondegenerate →
      ∀ q : QuadraticForm (ZMod 2) I, q.polarBilin = B.restrict I →
        s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
          q.isometrySubgroup → False)
    (hnatural : (B.restrict I).Nondegenerate →
      ChapterG.Section12.NaturalSL2Four s.constituentLinearAction.range → False) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected :=
  s.faithful_data_of_proper_not_nondegenerate hproper
    (s.not_nondegenerate_of_model_inputs hproper hrecognition hsymplectic horthogonal hnatural)

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
