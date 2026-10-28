module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Actions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Source

/-!
# The genuine moving orbit action from the original MS93 source

The independent higher commutator calculation now discharges the action
construction's only extra bound. The actual X/hat W is a finite elementary
abelian group, and its faithful SL3(2) action uses the unchanged source
projection. The equality C_Ga(X/hat W)=Q_a has no additional premise.

This supplies the faithful quotient action for the subsequent recognition
of its moving factor. It does not assert natural coordinates or the
independence of the two moving factors.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iv), printed p.899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The literal action kernel is the local two-core, from the original inputs. -/
theorem source_action_kernel (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    orbitActionKernel (Early.Orbit.SourceApplications.higherPath geometry p) = Q R (alpha R) :=
  orbitActionKernel_eq_Q common earlier p (OrbitGeometry.Source.Q_commutator_le common earlier p)

/-- The finite elementary quotient with its faithful original SL3(2) action.
No normality, action, kernel or geometric commutator bound remains an input. -/
theorem source_moving_module (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ∃ s : MovingModule source (Early.Orbit.SourceApplications.higherPath geometry p),
      let := s.normal
      IsElementaryAbelian 2 (MovingSpace (Early.Orbit.SourceApplications.higherPath geometry p)) ∧
        Function.Injective s.action := by
  have hQ := OrbitGeometry.Source.Q_commutator_le common earlier p
  obtain ⟨s⟩ := movingModule source earlier
    (Early.Orbit.SourceApplications.higherPath geometry p) hQ
  exact ⟨s,s.elementary earlier _ hQ,s.faithful common earlier p⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
