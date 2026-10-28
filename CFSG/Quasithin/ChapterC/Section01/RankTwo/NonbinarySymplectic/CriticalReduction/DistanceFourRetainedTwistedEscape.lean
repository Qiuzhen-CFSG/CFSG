module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRetainedTwistedVanishing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourEqualSmallCriticalFixed
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalPaths
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourKernelNormality

/-!
# Directed escape of the original full kernel under the retained twist

If the original kernel lay in the twisted kernel, mixed-kernel vanishing
would make both actual endpoints normalize its join with the original seed.
Its mover is normalized using the actual backward root index, derived from
nonfixedness. All three retained generators then normalize the same small
radius subgroup, forcing a B-index incompatible with the original strict
movement. No endpoint or selector is replaced and no generator is removed.
Source: MS93 (5.12)(3), printed pp.926--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

set_option maxHeartbeats 800000 in
/-- The full original kernel escapes the full twisted kernel for the same
three-generator configuration and both reciprocal fixed-space certificates. -/
theorem Input.replacement_distance_four_retained_twisted_kernel_not_le
    {geometry : Geometry d.radical} {a z u w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (r k : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a)
    (hk : k ∈ stabilizer d.radical a)
    (hru : act d.radical r (path.walk.getVert 2)=u)
    (hrw : act d.radical r (path.walk.getVert 1)=w)
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1))
        (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) :
          Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)))
    (hfixa : (Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hterminal : Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
        (Q d.radical (path.walk.getVert 3)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 3))
        (Nat.card F^2))
    (hterminalmove : (centralizer (Subgroup.SmallMover.join
        (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 3)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F^2)
    (hfixe : (Z d.radical (path.walk.getVert 2) ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
          (Q d.radical (path.walk.getVert 3)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical (path.walk.getVert 2) ⊓ centralizer
        (stabilizer d.radical (path.walk.getVert 2) : Set (FreeAmalgam d.radical)))
    (hkn : k ∈ normalizer ((Z d.radical a ⊓ Z d.radical (path.walk.getVert 2) :
      Subgroup (FreeAmalgam d.radical)) : Set _))
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hfirst : back.walk.getVert 1=w)
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hgen : (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
        Z d.radical (act d.radical k z)=stabilizer d.radical a) :
    ¬ Z d.radical u ⊓ Q d.radical (path.walk.getVert 2) ≤
      Z d.radical u ⊓ Q d.radical (act d.radical k (path.walk.getVert 2)) := by
  intro hcontain
  let e := path.walk.getVert 2
  let W := Z d.radical u ⊓ Q d.radical e
  let Y := W ⊔ Z d.radical a
  let J := Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
    (Q d.radical w) (Nat.card F^2)
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hb2 : 2 < geometry.b d.radical := by omega
  have hka : act d.radical k a=a := hk
  have hra : act d.radical r a=a := hr
  have he : color d.radical e=false := back.end_color
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0<path.walk.length))
  have het : Adjacent d.radical e (path.walk.getVert 1) := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (path.walk.adj_getVert_succ (by omega : 1<path.walk.length)))
  have haw : Adjacent d.radical a w := by
    rw [←hra,←hrw]
    exact (adjacent_act_iff d.radical r _ _).mpr hat
  have huw : Adjacent d.radical u w := by
    rw [←hru,←hrw]
    exact (adjacent_act_iff d.radical r _ _).mpr het
  have hZVu : Z d.radical u ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius haw huw)
  have hWQa : W ≤ Q d.radical a := inf_le_left.trans
    (hZVu.trans (geometry.V_le_Q hb2 a path.start_color))
  have hez : (cosetGraph d.radical).dist e z=2 := by
    dsimp only [e]
    rw [path.dist_end,path.length_eq_b,hb]
  have hzero := h.replacement_distance_four_retained_twisted_kernel_vanishing d path hb
    r k hr hk hru hrw hequal hJm hmove hfixa hterminal hterminalmove hfixe hkn
  have hzero₀ := h.replacement_distance_four_retained_twisted_kernel_vanishing d path hb
    r 1 hr (stabilizer d.radical a).one_mem hru hrw hequal hJm hmove hfixa
    hterminal hterminalmove hfixe (normalizer _).one_mem
  simp only [act_one] at hzero₀
  have hnormal (j : FreeAmalgam d.radical) (hj : j ∈ stabilizer d.radical a)
      (hWe : W ≤ Q d.radical (act d.radical j e))
      (hfix : W ≤ centralizer ((Z d.radical (act d.radical j z) ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
      Z d.radical (act d.radical j z) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    have hja : act d.radical j a=a := hj
    have hWS : W ≤ stabilizer d.radical (act d.radical j z) := hWe.trans
      (Q_le_stabilizer_of_dist_le_two _ _
        (by rw [action_preserves_color]; exact he)
        (by rw [action_preserves_color]; exact path.end_color)
        (by rw [dist_act,hez]))
    have hle := h.replacement_critical_fixed_intersection_displacement d (path.act j)
      (by omega) W hWS (by simpa only [hja] using hWQa) (by simpa only [hja] using hfix)
    rw [hja] at hle
    have hRZa : ⁅Z d.radical a,Z d.radical (act d.radical j z)⁆ ≤ Z d.radical a := by
      simpa only [hja] using critical_commutator_le_start_seed (path.act j)
    apply normalizes_join_of_commutators _ W (Z d.radical a)
    · exact (hle.trans hRZa).trans le_sup_right
    · rw [commutator_comm]
      exact hRZa.trans le_sup_right
  have hZn := hnormal k hk (hcontain.trans inf_le_right)
    (hcontain.trans (commutator_eq_bot_iff_le_centralizer.mp hzero))
  have hzN : Z d.radical z ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    simpa only [act_one] using hnormal 1 (stabilizer d.radical a).one_mem
      (by simpa only [act_one] using (show W ≤ Q d.radical e from inf_le_right))
      (by simpa only [act_one] using (commutator_eq_bot_iff_le_centralizer.mp hzero₀))
  obtain ⟨hroot,_⟩ := h.replacement_distance_four_equal_small_nonfixed_backward_root d path hb
    r hr hru hrw hequal hJm hfixa back hnot
  have hJW : J ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    have hh := unequal_first_mover_normalizes_critical_kernel h d back hb4 hroot
    simpa only [hfirst] using hh
  have hJS : J ≤ stabilizer d.radical a := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ haw))
  have hJN : J ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    (le_inf hJW (hJS.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hLN : Ltilde d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    apply (Ltilde_le_stabilizer a).trans
    rw [←hgen]
    exact sup_le (sup_le hJN hzN) hZn
  have hSV : Z d.radical u ⊔ Z d.radical a ≤ V d.radical a := neighbor_seed_join_le_radius haw huw
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hSV.trans
      ((geometry.V_le_Q hb2 a path.start_color).trans (fun _ hx => hx.1)))) (inclusion_injective _)
  have hbound := h.replacement_neighbor_seed_index_le_cube d geometry hb4 path.start_color haw huw
  have hiY : (Z d.radical a).relIndex Y ≤ Nat.card F^3 :=
    (relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
      ((neighbor_seed_join_index_le geometry (by omega) path.start_color haw huw).trans hbound)
  have hYB := h.replacement_small_radius_le_B d geometry hb2 path.start_color Y
    ((sup_le_sup inf_le_left le_rfl).trans hSV) hLN
    (hiY.trans_lt (Nat.pow_lt_pow_right (by exact Finite.one_lt_card) (by decide : 3<4)))
  have hWB : W ≤ B d.radical a (geometry.Z_normal a) := le_sup_left.trans hYB
  let := finite_Z d.radical u
  have hsmallZ := relIndex_le_of_le_left hWB (L := Z d.radical u) index_ne_zero_of_finite
  rw [inf_relIndex_left,hroot] at hsmallZ
  have hmoveu : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical u) := by
    rw [←hru,movingIndex_act geometry hb2 path.start_color r hr]
    exact hmove
  exact hmoveu.not_ge (((B d.radical a (geometry.Z_normal a)).relIndex_le_of_le_right
    (U_le_Z u) index_ne_zero_of_finite).trans hsmallZ)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
