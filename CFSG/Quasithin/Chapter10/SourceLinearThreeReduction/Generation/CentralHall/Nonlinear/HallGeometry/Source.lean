module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Basic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Product
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Borel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.TorusCoordinates
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.InvariantMarking
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Semilinear
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.FieldKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.PureField
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.ComponentAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Rows
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Transport
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Source

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.FixedVectors

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Natural.Action
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Natural.Source

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Orthogonal.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Suzuki.Source

/-!
# Assembly of the three original nonlinear Hall calculations

The natural and Suzuki action calculations contradict the nontrivial
faithful Hall action proved from the actual H-star data. A single compatible
orthogonal diagonal marking yields the two multiplicative characters and
therefore all fields of the original CartanCoordinates. The existing
nonlinear consumer then yields the literal action-image embedding.

All three Hall rows are proved: the natural and Suzuki actions are trivial,
and the orthogonal row gives the original exponent bound. ModuleAnalysisAt
remains the source obligation of the central Hall assembly. The older
conditional APIs are preserved.
Source: Aschbacher--Smith, 10.1.2(5) and 10.2.3, pp.742 and 745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- The three genuine row calculations complete the original Hall geometry. -/
theorem hallGeometry_of_rows
    (hnatural : NaturalActionTrivialAt T)
    (horthogonal : OrthogonalDiagonalAt T)
    (hsuzuki : SuzukiActionTrivialAt T) : HallGeometryAt T := by
  intro L D H B c geometry
  refine ⟨?_,?_,?_⟩
  · intro r hr e coordinates
    exact action_ne_one D c (hnatural L D H B c geometry r hr e coordinates)
  · intro n hn hlarge e coordinates
    obtain ⟨e',q,hq,hdiag⟩ :=
      horthogonal L D H B c geometry n hn hlarge e coordinates
    exact ⟨e',cartanCoordinates_of_pointwise D B c.hall_le n e' q hq hdiag⟩
  · intro m hm e coordinates
    exact action_ne_one D c (hsuzuki L D H B c geometry m hm e coordinates)

/-- Actual application to the original nonlinear action-image consumer.
The independent module recognition and all three row premises remain visible. -/
theorem nonlinearTorus_of_moduleAnalysis_and_rows
    (hmodules : ModuleAnalysisAt T)
    (hnatural : NaturalActionTrivialAt T)
    (horthogonal : OrthogonalDiagonalAt T)
    (hsuzuki : SuzukiActionTrivialAt T) : NonlinearTorusAt T :=
  nonlinearTorus_of_moduleAnalysis_and_hallGeometry T hmodules
    (hallGeometry_of_rows T hnatural horthogonal hsuzuki)

/-- The completed orthogonal source calculation leaves exactly the natural
and Suzuki row exclusions for the Hall geometry assembly. -/
theorem hallGeometry_of_natural_and_suzuki
    (hnatural : NaturalActionTrivialAt T)
    (hsuzuki : SuzukiActionTrivialAt T) : HallGeometryAt T :=
  hallGeometry_of_rows T hnatural (source_orthogonalDiagonalAt T) hsuzuki

/-- Application to the original nonlinear Hall image. Module recognition and
the two remaining row exclusions stay with the central Hall assembly owner. -/
theorem nonlinearTorus_of_moduleAnalysis_natural_and_suzuki
    (hmodules : ModuleAnalysisAt T)
    (hnatural : NaturalActionTrivialAt T)
    (hsuzuki : SuzukiActionTrivialAt T) : NonlinearTorusAt T :=
  nonlinearTorus_of_moduleAnalysis_and_hallGeometry T hmodules
    (hallGeometry_of_natural_and_suzuki T hnatural hsuzuki)

/-- The two completed row calculations leave only the Suzuki exclusion for
the original Hall geometry. Its discharge stays with the central Hall owner. -/
theorem hallGeometry_of_suzuki
    (hsuzuki : SuzukiActionTrivialAt T) : HallGeometryAt T :=
  hallGeometry_of_natural_and_suzuki T (source_naturalActionTrivialAt T) hsuzuki

/-- Application to the literal nonlinear Hall image. The remaining module
recognition and Suzuki premises belong to qt-d-10-nona5-central-hall-orders. -/
theorem nonlinearTorus_of_moduleAnalysis_and_suzuki
    (hmodules : ModuleAnalysisAt T)
    (hsuzuki : SuzukiActionTrivialAt T) : NonlinearTorusAt T :=
  nonlinearTorus_of_moduleAnalysis_and_hallGeometry T hmodules
    (hallGeometry_of_suzuki T hsuzuki)

/-- All three original nonlinear Hall calculations, with no row callbacks. -/
theorem source_hallGeometryAt : HallGeometryAt T :=
  hallGeometry_of_suzuki T (source_suzukiActionTrivialAt T)

/-- The original nonlinear torus conclusion now needs only module recognition.
Its discharge remains with qt-d-10-nona5-central-hall-orders. -/
theorem nonlinearTorus_of_moduleAnalysis (hmodules : ModuleAnalysisAt T) :
    NonlinearTorusAt T :=
  nonlinearTorus_of_moduleAnalysis_and_hallGeometry T hmodules (source_hallGeometryAt T)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
