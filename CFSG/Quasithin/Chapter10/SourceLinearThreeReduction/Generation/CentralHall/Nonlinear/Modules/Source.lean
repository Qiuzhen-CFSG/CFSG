module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedGeometry
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.Preparation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.RecognitionAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.CentralKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.MovedDomain
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.Recognition.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Source

/-!
# Assembly of the three nonlinear module rows from separated-seed analysis

The original source hypotheses supply the actual four-model component
catalogue and both cubic bounds. The earlier seed analysis, when proved,
then yields crossed centralization for every Sylow exchanger and subgroup
minimality of the literal moved central quotient. `Recognition.Source` now
uses these facts and the genuine Chapter K classifiers to construct the
natural, orthogonal or Suzuki coordinates with the original parameter bounds.
In this particular central Hall context, `CentralKernel` proves that the
moved central kernel vanishes, supplying whole-module coordinates.

Separated-seed analysis remains explicit; this module does not establish
`ModuleAnalysisAt` unconditionally. The existing conditional interfaces are
preserved alongside the assembly with recognition discharged.
`MovedCubic` now supplies the full local normalizer's cubic bound, its exact
centralizer kernel, and the simple irreducible component image with the
original L/O₂(L) marking. `MovedDomain` proves the remaining SQTK and F*
identities, supplying every Chapter K recognition-domain hypothesis.
Source: Aschbacher--Smith 3.2.6, 7.0.1 and 10.1.1--2, pp.581,695,741--742.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- Assembly retains precisely the two outstanding source implications. -/
theorem moduleAnalysis_of_seedAnalysis_and_recognition
    (hseed : SeedAnalysisAt T) (hrecognize : MovedRecognitionAt T) :
    ModuleAnalysisAt T := by
  intro L D H B c hnot
  obtain ⟨hlocal,hfull⟩ := cubic_bounds D c
  obtain ⟨t,ht,htn,hs⟩ := hseed L D H B c hnot hlocal hfull
  obtain ⟨geometry,hmin⟩ := geometry_and_minimality_of_separatedSeed D ht htn hs
  exact ⟨geometry,hrecognize L D H B c hnot (component_model D c.nonnormal)
    hlocal hfull geometry hmin⟩

/-- Exhaustive moved-module recognition is discharged. The original seed
construction remains with this central Hall source owner. -/
theorem moduleAnalysis_of_seedAnalysis (hseed : SeedAnalysisAt T) :
    ModuleAnalysisAt T :=
  moduleAnalysis_of_seedAnalysis_and_recognition T hseed
    (source_movedRecognitionAt (T := T))

/-- The central Hall context discharges the whole-module kernel obligations.
The two source classifications remain with this source assembly owner. -/
theorem moduleAnalysis_of_seedAnalysis_and_quotientRecognition
    (hseed : SeedAnalysisAt T) (hrecognize : MovedQuotientRecognitionAt T) :
    ModuleAnalysisAt T :=
  moduleAnalysis_of_seedAnalysis_and_recognition T hseed
    (movedRecognition_of_quotientRecognition hrecognize)

/-- The full local automizer's small-action hypotheses are now proved from
the original setup and the separated geometry. Exhaustive recognition and
seed analysis remain with this source owner. -/
theorem moduleAnalysis_of_seedAnalysis_and_smallRecognition
    (hseed : SeedAnalysisAt T) (hrecognize : MovedSmallRecognitionAt T) :
    ModuleAnalysisAt T :=
  moduleAnalysis_of_seedAnalysis_and_quotientRecognition T hseed
    (movedQuotientRecognition_of_smallRecognition hrecognize)

/-- Actual application to the original nonlinear Hall action. The seed,
recognition and independent Hall source producers must discharge all inputs. -/
theorem nonlinearTorus_of_seedAnalysis_recognition_and_hallGeometry
    (hseed : SeedAnalysisAt T) (hrecognize : MovedRecognitionAt T)
    (hhall : HallGeometryAt T) : NonlinearTorusAt T :=
  nonlinearTorus_of_moduleAnalysis_and_hallGeometry T
    (moduleAnalysis_of_seedAnalysis_and_recognition T hseed hrecognize) hhall

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
