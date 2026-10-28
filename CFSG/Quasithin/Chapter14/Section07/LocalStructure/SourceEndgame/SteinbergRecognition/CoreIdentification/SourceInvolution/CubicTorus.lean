module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus.FixedPoints
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus.Transporter
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus.OppositePlane

/-!
# The cubic torus geometry used in source 14.7.72

We construct an actual order-three J≤L₁ and an element of N_K(J) carrying
the original V-plane to an opposite plane. The source duality gives
Q_H∩C_G(J)≤C_H(U), and the two planes span the original U. This constructs
every field of SourceInvolution.TorusGeometry, without an involution,
splitting, conjugate-placement assumption, or any use of 14.7.73.

All data refer to one original critical path and the original qH. The
compatible upper marking and local actors are earlier qt-14-03/qt-14-07
inputs; source duality and [U,Q_H]=V₁ are 14.5.21. U₀=V₁ comes from the
preceding 14.7.72 generation branch. The enclosing involution assembly
retains their discharge and the independent parabolic-support input S≤L₁.
The separate Application module supplies the exact existing consumer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.72, printed pp.1075–1076 (PDF pp.1092–1093).
-/

public section
noncomputable section
open Subgroup Representation Matrix.SpecialLinearGroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The genuine cubic-torus geometry on the original H, U, V and quotient.
Only compatible earlier source inputs and the preceding U₀=V₁ conclusion
remain explicit. In particular S≤L₁ is not required for this construction. -/
theorem exists_torusGeometry_of_earlier (c : CriticalPath (L := L) F)
    (earlier : SourceEndgame.ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (actors : MarkedSpans.LocalActors d)
    (s : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) (hU0 : d.U₀ = F.Vi 1) :
    Nonempty (TorusGeometry F L) := by
  obtain ⟨t⟩ := exists_markedTorus d actors
  obtain ⟨n, hnK, hnN, hn⟩ := t.exists_mover d
  exact ⟨{
    torus := t.torus
    torus_le := t.torus_le d
    torus_card := t.torus_card d
    mover := n
    mover_mem := hnK
    mover_normalizes := hnN
    fixed_le := t.fixed_le d earlier.sectionCentralizer s hcomm hU0
    span := opposite_span d earlier.sectionCentralizer mark earlier.separation actors hU0 n hn }⟩


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus
