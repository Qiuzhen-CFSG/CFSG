module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedKernelComparison
/-!
# Transfer of the complete fixed two-core attachment

In the field-sized branch, the edge also factors as U_a Q_z. A commutator
of C_{Q_a}(L_a) with Z_z is therefore an individual commutator of U_a
with Z_z. Normality keeps it in the full L_a-fixed layer, and fixed-vector
lifting makes it trivial. The exact centralizer of Z_z in its stabilizer
then places the entire attachment in Q_z.

The final consumer derives the field-sized premise from the ORIGINAL
odd-index witness in the proper nonsylow branch. This does not replace that
witness by an odd-index hypothesis on the characteristic replacement.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (1.5)(ii) and the fixed-part comparisons in (3.7), pp.873--876.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full component-fixed part of the kernel centralizes the opposite
critical Z-layer; no fixed attachment is discarded. -/
theorem replacement_field_sized_fixedCore_centralizes_opposite
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    fixedCore d.radical a ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hQaT := Q_le_adjacent_h d.radical ht hat
  have hTz : Q d.radical t ≤ stabilizer d.radical z := by
    rw [Q_h_eq_edge d.radical ht hzt]
    exact inf_le_left
  have hZaT : Z d.radical a ≤ Q d.radical t := by
    rw [←(replacement_field_sized_paired_edges h d path hb hat hzt hsize).2]
    exact le_sup_right
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have htzQ : Z d.radical t ≤ Q d.radical z :=
    (Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt).trans
      ((g.omega_bound z path.end_color (by
        rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans
        (omegaCenter_le _))
  have hfactor : U d.radical a ⊔ Q d.radical z = Q d.radical t := by
    have hh := (replacement_field_sized_paired_edges h d path hb hat hzt hsize).2
    rw [(replacement_field_sized_central_layers h d path hb hat hzt hsize).2,
      ←sup_assoc,sup_of_le_left (htzQ.trans le_sup_left),sup_comm] at hh
    exact hh
  have hnQ : U d.radical a ≤ normalizer (Q d.radical z : Set (FreeAmalgam d.radical)) :=
    ((U_le_Z a).trans hZaT |>.trans hTz).trans (Q_normalized d.radical z)
  intro c hc v hv
  have hcT := hQaT hc.1
  have hcprod : c ∈ U d.radical a ⊔ Q d.radical z := hfactor.symm ▸ hcT
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hnQ] at hcprod
  obtain ⟨u,hu,q,hq,rfl⟩ := hcprod
  have hvq : Commute v q :=
    ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical z path.end_color)) hv q hq).symm
  have hcomm : ⁅v,u*q⁆=⁅v,u⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hvq]
    simp only [mul_one,mul_inv_cancel_right]
  have hvd : ⁅v,u*q⁆ ∈ fixedCore d.radical a :=
    le_normalizer_iff_commutator_le_right.mp
      (hZA.trans (fixedCore_normalized d.radical a)) (commutator_mem_commutator hv hc)
  rw [hcomm] at hvd
  have he := replacement_field_sized_value_in_fixed_eq_one h d path hb hat hzt hsize
    v hv u hu hvd.2
  have hfinal : Commute v (u*q) := commutatorElement_eq_one_iff_commute.mp (hcomm.trans he)
  exact hfinal.eq

/-- The entire fixed kernel lies in the opposite local two-core, using its
literal centralizer description. -/
theorem replacement_field_sized_fixedCore_le_opposite
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    fixedCore d.radical a ≤ Q d.radical z := by
  rw [←MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color]
  apply le_inf _ (replacement_field_sized_fixedCore_centralizes_opposite h d path hb hat hzt hsize)
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hTz : Q d.radical t ≤ stabilizer d.radical z := by
    rw [Q_h_eq_edge d.radical ht hzt]
    exact inf_le_left
  exact inf_le_left.trans ((Q_le_adjacent_h d.radical ht hat).trans hTz)

/-- Original-witness application retaining both complete fixed parts. -/
theorem replacement_proper_nonsylow_fixedCore_transfer
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    fixedCore d.radical a ≤ Q d.radical z ∧
      fixedCore d.radical a ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
  have hs := replacement_proper_nonsylow_card h d g hb hnsyl hne
  exact ⟨replacement_field_sized_fixedCore_le_opposite h d path hb hat hzt hs,
    replacement_field_sized_fixedCore_centralizes_opposite h d path hb hat hzt hs⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
