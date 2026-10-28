module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.ProjectiveGaschutz.FixedDetection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.ProjectiveGaschutz.CentralLift
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Root
public import Theory.Representation.SL2FourNaturalBorelFixedLifting.Gaschutz
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Construction

/-!
# The first actual Gaschütz application in14.7.74

The source quotient Q_H/C_H(U) is finite. Gaschütz fixed-vector lifting
therefore discharges the general lifting premise in the marked dual
fixed-space detector. The original left parabolic contains a Sylow subgroup
and has the prescribed Borel image. Perfection of K lowers the resulting
commutator bound into C_H(U) to U, and the original conjugate spans imply
that Q_C centralizes S. No new lifting or fixed-space premise is retained.

Source: Aschbacher–Smith,14.7.74,first paragraph,printed p.1077.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source ChiefFactors
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (a : Prior d) (c : CriticalPath (L := L) F) (e : Earlier d c)
  (mark : UpperMarking d)
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

include d structural a c e mark

/-- Gaschütz on the original finite Q_H/C_H(U) section. -/
theorem QC_K_le_C (s : CriticalIntersections.SourceDuality F X Y)
    (b : QKDualCoordinates d) : ⁅QC T L V,K F⁆ ≤ C F := by
  let := ProjectiveFixedDetection.section_finite s
  apply ProjectiveFixedDetection.QC_K_le_C_of_fixed_lift d a c e s b
    (compatibleBorel_of_upperMarking d structural mark).left_image
  intro N hN P y hy
  exact SL2FourNaturalBorelFixedLifting.exists_fixed_lift
    (FixedDetection.sectionAction s) N hN P y hy

/-- The actual source commutator bound, with both coordinate sections constructed. -/
theorem QC_K_le_U (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) :
    ⁅QC T L V,K F⁆ ≤ F.U := by
  obtain ⟨X,aX,mX,hs⟩ := CriticalIntersections.exists_sourceDuality d e.sectionCentralizer
  let := aX
  let := mX
  obtain ⟨s⟩ := hs
  obtain ⟨b⟩ := HAccounting.exists_qKDualCoordinates d e.sectionCentralizer s hcomm
  exact QC_K_le_U_of_centralizer_bound d c e (QC_K_le_C d structural a c e mark s b)

/-- The bound is consumed on the original span S=⟨U^L⟩. -/
theorem QC_centralizes_S (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) :
    QC T L V ≤ centralizer (S L F : Set G) :=
  LocalCollapse.QC_centralizes_S d a (QC_K_le_U d structural a c e mark hcomm)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
