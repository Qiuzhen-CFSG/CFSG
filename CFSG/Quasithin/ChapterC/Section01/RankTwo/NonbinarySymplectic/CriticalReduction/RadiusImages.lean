module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.InnerAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.RadiusAction
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank

/-!
# Radius images and their full kernels beyond distance four

The actual radius is elementary at distance greater than four. Its image in
an opposite vertex quotient is therefore an elementary subgroup of Sp₄(q),
whose proved two-rank gives the bound q³. The actual kernel is its intersection
with Q at that vertex. Factoring the radius quotient of order at least q⁴
through this image forces its kernel quotient to have order at least q.

Both estimates use the minimum characteristic replacement and original field
degree. They retain the full Z denominator. The image bound at distance four
and the final shifted-path exclusion are not asserted here.
Source: MS93 (5.2), printed p.914, and (5.8)--(5.11), pp.920--924.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full radius has image of order at most q³ at every reachable
opposite vertex when the critical distance exceeds four. -/
theorem Input.replacement_radius_image_le_cube_of_four_lt
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a z : Vertex d.radical} (ha : color d.radical a = false)
    (hz : color d.radical z = false)
    (hd : (cosetGraph d.radical).dist a z + 2 ≤ geometry.b d.radical) :
    (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F ^ 3 := by
  obtain ⟨E,hE,f,_,hfQ,_⟩ := h.replacement_inner_natural_action d geometry (by omega) hz
  have hV := radius_le_stabilizer_of_distance d.radical geometry ha hd
  let δ := f.comp (inclusion hV)
  have hc : Nat.card δ.range = (Q d.radical z).relIndex (V d.radical a) :=
    SourceComparison.quotient_image_card _ _ _ hV f hfQ
  let : IsElementaryAbelian 2 (V d.radical a) := V_elementary_of_four_lt d.radical ha hb
  let : IsElementaryAbelian 2 δ.range :=
    IsElementaryAbelian.of_surjective δ.rangeRestrict δ.rangeRestrict_surjective
  have hr : primeRank 2 (Matrix.symplecticGroup (Fin 2) E.Carrier) ≤ 3*n := by
    rw [Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank
      (show Nat.card E.Carrier=2^n by rw [E.card_eq,hE]) (by have := h.nonbinary; omega)]
  have hi := (primeRank_le_iff_elementary_card_le _).mp hr δ.range inferInstance
  rw [hc] at hi
  simpa only [h.field_card,←pow_mul,Nat.mul_comm n 3] using hi

/-- The actual radius kernel modulo the full central seed has order at least q. -/
theorem Input.replacement_radius_kernel_index_ge_field_of_four_lt
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t z : Vertex d.radical} (ha : color d.radical a = false)
    (hz : color d.radical z = false) (hat : Adjacent d.radical a t)
    (hd : (cosetGraph d.radical).dist a z + 2 ≤ geometry.b d.radical) :
    Nat.card F ≤ (Z d.radical a).relIndex (V d.radical a ⊓ Q d.radical z) := by
  have hlo := h.replacement_radius_index_ge_fourth_power d geometry (by omega) ha hat
  have hup := h.replacement_radius_image_le_cube_of_four_lt d geometry hb ha hz hd
  have hZQ : Z d.radical a ≤ Q d.radical z :=
    Z_le_Q_of_dist_lt d.radical a (geometry.exists_critical a ha)
      (by rw [geometry.distance_constant a ha]; change (cosetGraph d.radical).dist a z < geometry.b d.radical; omega)
  have hprod := relIndex_inf_mul_relIndex (Z d.radical a) (Q d.radical z) (V d.radical a)
  rw [inf_eq_left.mpr hZQ,inf_comm (Q d.radical z) (V d.radical a)] at hprod
  have hm := Nat.mul_le_mul_left ((Z d.radical a).relIndex (V d.radical a ⊓ Q d.radical z)) hup
  rw [hprod] at hm
  have hpos : 0 < Nat.card F ^ 3 := pow_pos (Nat.card_pos (α := F)) _
  have he : Nat.card F ^ 4 = Nat.card F * Nat.card F ^ 3 := by ring
  rw [he] at hlo
  nlinarith

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
