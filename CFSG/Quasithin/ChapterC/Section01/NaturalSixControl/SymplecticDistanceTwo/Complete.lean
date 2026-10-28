module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitNatural
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitNaturalTerminal
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CorePullback
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointFull
/-!
# The actual symplectic distance-two reconstruction

The Frattini-small branch identifies the whole core with the marked moving
layer. In the remaining branch, select the ordered critical orbits supplied
by the source. Their strict offender estimate gives full edge images. The
proved B5 natural-quotient recognition and the actual augmentation-cover
kernel calculation supply the linear data for the paired-orbit contradiction.
Thus the whole core equals U without a reconstruction, recognition, movement,
or coordinate premise beyond the native source and its specified point image.

On the original characteristic replacement, the existing line-image branch
already gives an alternating block. Combining that branch with the full-image
core equality removes the point-image assumption from the final original
alternating-block conclusion at critical distance two.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed pp.870--871,
used in Aschbacher--Smith C.1.37.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Stellmacher.PushingUp.AmalgamGraph CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem core_eq_U_of_distance_two
    (hsq : IsSQTK KnownSimple.IsKnownSimple M) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) : core R (alpha R) = U R (alpha R) := by
  let h := s.nativeCentralLayer hsq
  by_cases hsmall : core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)
  · exact s.core_eq_U_of_le_frattini_sup (alpha R) rfl h.X_commutator hsmall
  obtain ⟨c,b,B,hc,hab,hcb,_,_,_,hBQ,hnB,hcommB,_,_,_,hcomp,_,helem⟩ :=
    s.exists_ordered_elementary_criticalOrbits h t hfull hb hsmall
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hsmall
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  let := s.orbitQuotient_elementary hb hc hab hcb hne
  have hsurj : Function.Surjective s.projection :=
    s.projection_surjective_of_radical_image_le_conjugate t (by
      simpa only [Model.pointCore_eq_exceptional] using hfull.le)
  have himage := (s.criticalOrbit_images_full h t hfull hb hsmall hc hab hcb B hBQ hcommB hcomp).2.1
  obtain ⟨e,p,hp,hk,he,hfix⟩ := s.orbit_natural_quotient_fixed_le_moved
    hsq h t hfull hb hsmall hc hab hcb hsurj B hBQ hcommB hcomp
  exact (s.false_of_criticalOrbit_natural_quotient h t hfull hb hsmall hc hab hcb himage B hBQ hnB
    helem hsurj e p hp hk he hfix).elim
end Source

namespace SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T) (h : IntrinsicMSPair d)
include d h
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

theorem reducedSource_core_eq_U_of_distance_two
    (r : CharacteristicReduction (L.subgroupOf J) R)
    (hfull : r.radical.map ((originalSource d h).reduce r).projection =
      pointCore.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom)
    (hb : ((originalSource d h).reduce r).geometry.b r.radical = 2) :
    core r.radical (alpha r.radical) = U r.radical (alpha r.radical) :=
  ((originalSource d h).reduce r).core_eq_U_of_distance_two
    ((d.sqtk.subgroup J).subgroup r.overgroup) d.relabeler.val⁻¹ hfull hb

theorem reducedSource_alternatingBlock_of_distance_two
    (r : CharacteristicReduction (L.subgroupOf J) R)
    (hb : ((originalSource d h).reduce r).geometry.b r.radical = 2) :
    IsAlternatingBlock L 6 := by
  rcases reducedSource_block_or_full_point_image d h r with hblock | hfull
  · exact hblock
  · exact (ms_block_of_reduced_core_eq_U d h r
      (reducedSource_core_eq_U_of_distance_two d h r hfull hb)).2
end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
