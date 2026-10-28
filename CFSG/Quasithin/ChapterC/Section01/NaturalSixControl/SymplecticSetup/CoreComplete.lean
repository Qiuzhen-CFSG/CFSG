module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.DistanceFourImpossible
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Complete
/-!
# The native symplectic core equals its specified moving layer

The native large-distance bound and terminal distance-four contradiction leave
critical distance two. The established distance-two reconstruction then identifies
the whole core with U. On each actual characteristic replacement this forces the
original alternating-block conclusion, with no radius or core-identification premise.

Source: MS93 (5.12), printed pp.924--927, followed by (3.6), pp.870--871;
the symplectic branch of Aschbacher--Smith C.1.37.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem criticalDistance_eq_two
    (hsq : IsSQTK KnownSimple.IsKnownSimple M) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom) :
    s.geometry.b R=2 := by
  let h := s.nativeCentralLayer hsq
  have hlarge := s.criticalDistance_le_four h u hfull
  have hfour := s.criticalDistance_ne_four h u hfull hsq
  have hpos := s.criticalDistance_pos
  have heven := s.geometry.even (alpha R) rfl
  change 0<s.geometry.b R at hpos
  change Even (s.geometry.b R) at heven
  rw [Nat.even_iff] at heven
  omega

theorem core_eq_U
    (hsq : IsSQTK KnownSimple.IsKnownSimple M) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom) :
    core R (alpha R)=U R (alpha R) :=
  s.core_eq_U_of_distance_two hsq u
    (by simpa only [Model.pointCore_eq_exceptional] using hfull)
    (s.criticalDistance_eq_two hsq u hfull)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)
local notation "R" => d.B.subgroupOf J
include d hm

theorem reducedSource_core_eq_U
    (r : CharacteristicReduction (L.subgroupOf J) R)
    (hfull : r.radical.map ((originalSource d hm).reduce r).projection=
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj d.relabeler.val⁻¹).toMonoidHom) :
    core r.radical (alpha r.radical)=U r.radical (alpha r.radical) :=
  ((originalSource d hm).reduce r).core_eq_U ((d.sqtk.subgroup J).subgroup r.overgroup) _
    (by simpa only [Model.pointCore_eq_exceptional] using hfull)

theorem reducedSource_alternatingBlock
    (r : CharacteristicReduction (L.subgroupOf J) R) : IsAlternatingBlock L 6 := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact hblock
  · exact (ms_block_of_reduced_core_eq_U d hm r (reducedSource_core_eq_U d hm r hfull)).2
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
