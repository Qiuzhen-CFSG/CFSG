module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualMovers

/-!
# Individual neighboring movers on the whole original edge layer

MS93 (5.3) puts the original edge Z-layer in U times the residual-fixed
core. Its central factor is fixed by the whole vertex stabilizer. Thus
fixed-subgroup comparisons on the whole U-layer lift to the original
edge Z, even when the actors belong to a different selected edge.

The unequal neighboring mover already fixes exactly the same subgroup
of U as that selected edge. The lift transfers the original mover's
individual edge-Z fixed clause to every neighboring mover. The concrete
contained-image selector and backward-path applications are in
ContainedNeighborSelection and ContainedNeighborPaths. All central
attachments and the original degree are retained.

Source: MS93 (5.3), (5.5)(b), printed pp.915--917.
-/

public noncomputable section
open scoped Pointwise
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Fixed-subgroup comparison on the entire moving layer lifts to the
original edge Z. MS93 (5.3) places that edge layer in U times the full
residual-fixed core; its intersection with Z is ambient-fixed. -/
theorem Input.replacement_edge_fixed_mono_of_U
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E D : Subgroup (FreeAmalgam d.radical))
    (hES : E ≤ stabilizer d.radical a) (hDS : D ≤ stabilizer d.radical a)
    (hfixed : U d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical)) ≤
      U d.radical a ⊓ centralizer (D : Set (FreeAmalgam d.radical))) :
    Z d.radical t ⊓ centralizer (E : Set (FreeAmalgam d.radical)) ≤
      Z d.radical t ⊓ centralizer (D : Set (FreeAmalgam d.radical)) := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have ht : color d.radical t ≠ false := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    exact Ne.symm hh
  have htZ := adjacent_Z_le d.radical ha hat
  have htJ : Z d.radical t ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    intro v hv y hy
    rw [Z,if_neg ht] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2 y ((Subgroup.SmallMover.join_le _ _ _ _) hy)
  have hZX : Z d.radical a ≤ X d.radical a := Z_le_X_of_positive d.radical a ha
    (geometry.exists_critical a ha) (by rw [geometry.distance_constant a ha]; exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha
  have hS : Ltilde d.radical a ⊔ Q d.radical a = S := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have hN : fixedCore d.radical a ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (show fixedCore d.radical a ≤ S from fun _ hx => hx.1.1).trans (U_normalized a)
  intro z hz
  have hzUD := h.replacement_small_mover_X_centralizer d geometry hb ha hat
    ⟨hZX (htZ hz.1),htJ hz.1⟩
  have hzprod : z ∈ (U d.radical a : Set (FreeAmalgam d.radical)) *
      (fixedCore d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hN]
    exact hzUD
  obtain ⟨u,hu,c,hc,he⟩ := hzprod
  have hcZ : c ∈ Z d.radical a := by
    have hh := (Z d.radical a).mul_mem ((Z d.radical a).inv_mem (U_le_Z a hu)) (htZ hz.1)
    simpa only [←he,inv_mul_cancel_left] using hh
  have hcS : c ∈ centralizer (S : Set (FreeAmalgam d.radical)) := by
    have hSL : Ltilde d.radical a ≤ centralizer ({c} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hc.2 y hy)
    have hSQ : Q d.radical a ≤ centralizer ({c} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr
        ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha)) hcZ y hy)
    intro y hy
    exact mem_centralizer_singleton_iff.mp ((sup_le hSL hSQ) (hS.symm ▸ hy))
  have huE : u ∈ centralizer (E : Set (FreeAmalgam d.radical)) := by
    have hh := (centralizer (E : Set (FreeAmalgam d.radical))).mul_mem hz.2
      ((centralizer (E : Set (FreeAmalgam d.radical))).inv_mem (centralizer_le hES hcS))
    simpa only [←he,mul_inv_cancel_right] using hh
  refine ⟨hz.1,?_⟩
  rw [←he]
  exact (centralizer (D : Set (FreeAmalgam d.radical))).mul_mem
    (hfixed ⟨hu,huE⟩).2 (centralizer_le hDS hcS)

/-- At any selected edge, an unequal neighboring mover has the same fixed
subgroup as that entire edge on the original edge Z. The two edges need not
coincide; all central attachments are retained. -/
theorem Input.replacement_unequal_selected_edge_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t w v : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (hne : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical w) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical w) (Nat.card F^2)) :
    Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical v)
        (Q d.radical v) (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical t ⊓ centralizer (Q d.radical w : Set (FreeAmalgam d.radical)) := by
  let E := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
    (Q d.radical w) (Nat.card F^2)
  have hEQ : E ≤ Q d.radical w := Subgroup.SmallMover.join_le _ _ _ _
  have hQS : Q d.radical w ≤ stabilizer d.radical a :=
    fun _ hy => hy.2 a (adjacent_symm d.radical haw)
  apply le_antisymm
  · exact h.replacement_edge_fixed_mono_of_U d geometry hb ha hat E (Q d.radical w)
      (hEQ.trans hQS) hQS
      (h.replacement_unequal_individual_edge_fixed d geometry hb ha haw hvw hne).2.le
  · exact inf_le_inf_left _ (centralizer_le hEQ)

/-- The individual whole-edge fixed clause transfers from the original mover
at a selected edge to every neighboring mover there, without identifying them. -/
theorem Input.replacement_neighbor_edge_fixed_of_original
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t w v : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (hfixed : Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical v)
      (Q d.radical v) (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  by_cases he : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical w) (Nat.card F^2) = Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical w) (Nat.card F^2)
  · rwa [he]
  apply le_antisymm
  · rw [h.replacement_unequal_selected_edge_fixed d geometry hb ha hat haw hvw he]
    exact (inf_le_inf_left _ (centralizer_le (Subgroup.SmallMover.join_le _ _ _ _))).trans_eq hfixed
  · exact inf_le_inf_left _ (centralizer_le ((Subgroup.SmallMover.join_le _ _ _ _).trans
      (fun _ hy => hy.2 a (adjacent_symm d.radical haw))))


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
