module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Source

/-!
# Excluding the terminal image of order two

The selected terminal layer has a two-coset image only if the source ordered
commutator is forced into the marked line.  The crossing subgroup needed for
the index-two calculation is not an extra hypothesis: if it were contained in
the center kernel, the neighboring intersection estimate and the shifted
critical path would make the selected backward layer normalize the selected
join, contrary to its defining failure of normalization.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.1)(vi), (3.5), and the paragraph after (4.4.1), printed p.892.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

private theorem commutator_le_sup_of_index_two {G : Type*} [Group G]
    (E H K F A : Subgroup G) (hFH : F ≤ H) (hi : K.relIndex H = 2)
    (hnot : ¬ F ≤ K) (hEK : ⁅E,H ⊓ K⁆ ≤ A) (hHA : H ≤ normalizer A) :
    ⁅E,H⁆ ≤ A ⊔ ⁅E,F⁆ := by
  obtain ⟨u, hu, hun⟩ := SetLike.not_le_iff_exists.mp hnot
  apply commutator_le.mpr
  intro e he h hh
  by_cases hhK : h ∈ K
  · exact mem_sup_left (hEK (commutator_mem_commutator he ⟨hh,hhK⟩))
  · have hfactor : u⁻¹ * h ∈ K := by
      have hm := (K.subgroupOf H).mul_mem_iff_of_index_two hi
        (a := ⟨u⁻¹,H.inv_mem (hFH hu)⟩) (b := ⟨h,hh⟩)
      exact hm.mpr (by simp only [mem_subgroupOf, inv_mem_iff, hun, hhK])
    have hc := hEK (commutator_mem_commutator he
      (show u⁻¹ * h ∈ H ⊓ K from ⟨H.mul_mem (H.inv_mem (hFH hu)) hh,hfactor⟩))
    have hn := (mem_normalizer_iff.mp (hHA (hFH hu)) _).mp hc
    have hp := (A ⊔ ⁅E,F⁆).mul_mem
      (mem_sup_right (commutator_mem_commutator he hu)) (mem_sup_left hn)
    have hid := commutatorElement_mul_right_eq_mul_conj e u (u⁻¹ * h)
    simp only [mul_inv_cancel_left] at hid
    rw [hid]
    simpa only [mul_assoc] using hp

private theorem normalizer_sup_of_commutator_le
    {G : Type*} [Group G] (E F V : Subgroup G)
    (hEF : ⁅E,F⁆ ≤ V) (hEV : E ≤ normalizer V)
    (hFV : F ≤ normalizer V) :
    E ≤ normalizer (F ⊔ V : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro e he x hx
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right F V hFV] at hx
  obtain ⟨f, hf, v, hv, rfl⟩ := hx
  have hcf : ⁅e,f⁆ ∈ V := hEF (commutator_mem_commutator he hf)
  have hef : e * f * e⁻¹ ∈ F ⊔ V := by
    have h := (F ⊔ V).mul_mem (mem_sup_right hcf) (mem_sup_left hf)
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using h
  have hev : e * v * e⁻¹ ∈ V := (le_normalizer_iff.mp hEV e he v hv)
  have h := (F ⊔ V).mul_mem hef (mem_sup_right hev)
  simpa only [mul_assoc, inv_mul_cancel_left] using h

namespace TerminalNeighbor
variable {a c : Vertex R} {w : BackwardWitness R geometry a c}

theorem index_two_commutator_bound [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2)
    (n : TerminalNeighbor w)
    (hi : (Q R c).relIndex (Z R n.vertex) = 2) :
    ⁅Z R n.vertex, Z R w.backward⁆ ≤
      ⁅⁅Z R n.vertex, Q R w.predecessor⁆, Z R w.backward⁆ ⊔ Z R w.predecessor := by
  let E := Z R w.backward
  let H := Z R n.vertex
  let K := Q R c
  let F := ⁅Z R n.vertex, Q R w.predecessor⁆
  let A := Z R w.predecessor
  have hn_dist : (cosetGraph R).dist n.vertex w.predecessor = 2 := by
    simpa [SimpleGraph.dist_comm] using n.distance
  have hlam_color : Stellmacher.PushingUp.AmalgamGraph.color R n.vertex = false :=
    (color_eq_of_dist_even R n.vertex w.predecessor
      (by rw [hn_dist]; decide)).trans
      w.predecessor_color
  have hHq : H ≤ Q R w.predecessor := by
    apply Z_le_Q_of_dist_lt R n.vertex (geometry.exists_critical n.vertex hlam_color)
    rw [geometry.distance_constant n.vertex hlam_color, hn_dist]
    exact lt_trans (by decide : 2 < 4) hb
  have hqH : Q R w.predecessor ≤ normalizer H := by
    apply (Q_le_stabilizer_of_dist_two R w.predecessor n.vertex w.predecessor_color
      (by simpa using n.distance)).trans
    exact Z_normalized R n.vertex
  have hFH : F ≤ H := by
    simpa only [F, H, commutator_comm] using
      le_normalizer_iff_commutator_le_left.mp hqH
  have hEK : ⁅E, H ⊓ K⁆ ≤ A := by
    rw [commutator_comm]
    exact neighboring_intersection_commutator_le common hb ha hd w
      hn_dist.le
  have hEA : E ≤ normalizer A := by
    have hpath := (w.shifted ha (by omega : 2 ≤ geometry.b R)).reverse common
    exact hpath.endpoint_Z_le_start_stabilizer (by omega) |>.trans (Z_normalized R _)
  have hHA : H ≤ normalizer A := hHq.trans
    ((show Q R w.predecessor ≤ stabilizer R w.predecessor from fun _ hx => hx.1).trans
      (Z_normalized R w.predecessor))
  have hnot : ¬ F ≤ K := by
    intro hFK'
    have hFint : F ≤ H ⊓ K := le_inf hFH hFK'
    have hEF : ⁅E,F⁆ ≤ A := (commutator_mono le_rfl hFint).trans hEK
    have hFA : F ≤ normalizer A := hFH.trans hHA
    apply n.not_normalizes
    exact normalizer_sup_of_commutator_le E F A hEF hEA hFA
  have hbound := commutator_le_sup_of_index_two E H K F A hFH hi hnot hEK hHA
  simpa only [E, H, F, A, commutator_comm, sup_comm] using hbound

theorem image_index_ne_two [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2)
    (n : TerminalNeighbor w) :
    (Q R c).relIndex (Z R n.vertex) ≠ 2 := by
  intro hi
  have hbound := n.index_two_commutator_bound common hb ha hd hi
  exact n.triple_noncontainment common hb ha hbound

end TerminalNeighbor
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
