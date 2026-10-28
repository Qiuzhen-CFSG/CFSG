module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalizedRootBudget
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourKernelNormality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalPaths

/-!
# The full kernel join for the same root successor

Retain W = Z_v intersect Q_a, the entire preceding seed Z_u, and the actual
critical successor v to a whose directed image has order q. Its first mover
normalizes W. The literal full comparison then makes the original endpoint
Z_e normalize W joined with Z_u. This works with the root equality q itself.

When the preceding critical image has order at least q squared, the
escaping-actor comparison proves the stronger bound [W,Z_e] <= [Z_u,Z_e]
without any fixed-radius assumption. The same selected generating pair, if
it contains L_u, therefore gives the full B_u budget for both Z_v and the
original Z_a. Individual residual generation is retained as an explicit
input; the existing three-generator certificate is not shortened.
Source: MS93 (5.12)(1)--(2), printed pp.925--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A large preceding critical image forces the full original kernel actor
into the critical displacement, without assuming radius fixedness. -/
theorem Input.replacement_distance_four_large_full_kernel_comparison
    {geometry : Geometry d.radical} {a z u v s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (hlarge : Nat.card F^2 ≤
      (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)) :
    ⁅Z d.radical v ⊓ Q d.radical a,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ := by
  obtain ⟨_,hWS,hcent,_,_⟩ := full_comparison_actor h d path hb back hus hvs
  by_contra hbad
  have hs := h.replacement_critical_index_lt_square_of_escape d back (by omega)
    (Z d.radical v ⊓ Q d.radical a) hWS hcent (by
      rw [commutator_comm]
      exact hbad)
  exact (not_lt_of_ge hlarge) hs

/-- The original preceding endpoint normalizes the full kernel join.
This needs neither a fixed radius nor an additional root successor. -/
theorem Input.replacement_distance_four_large_full_kernel_endpoint_normalized
    {geometry : Geometry d.radical} {a z u v s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (hlarge : Nat.card F^2 ≤
      (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)) :
    Z d.radical (path.walk.getVert 2) ≤
      normalizer (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  have hR : ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤ Z d.radical u :=
    critical_commutator_le_start_seed back
  apply normalizes_join_of_commutators
  · rw [commutator_comm]
    exact (h.replacement_distance_four_large_full_kernel_comparison d path hb back
      hus hvs hlarge).trans (hR.trans le_sup_right)
  · rw [commutator_comm]
    exact hR.trans le_sup_right

/-- The literal full comparison and the actual root successor normalize
the unchanged full join under its mover and original preceding endpoint. -/
theorem Input.replacement_distance_four_root_full_comparison_normalized
    {geometry : Geometry d.radical} {a z u v s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (next : CriticalPath d.radical geometry v a) (hfirst : next.walk.getVert 1=s)
    (hroot : (Q d.radical a).relIndex (Z d.radical v)=Nat.card F)
    (hcompare : ⁅Z d.radical v ⊓ Q d.radical a,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅Z d.radical v ⊓ Q d.radical a,
          X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) :
    Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2) ≤
      normalizer (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let W := Z d.radical v ⊓ Q d.radical a
  let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
    (Q d.radical s) (Nat.card F^2)
  have hJW : J ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    have hh := unequal_first_mover_normalizes_critical_kernel h d next (by omega) hroot
    simpa only [hfirst] using hh
  have hJS : J ≤ stabilizer d.radical u :=
    (Subgroup.SmallMover.join_le _ _ _ _).trans
      (fun _ hx => hx.2 u (adjacent_symm _ hus))
  have hJn : J ≤ normalizer ((W ⊔ Z d.radical u :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (le_inf hJW (hJS.trans (Z_normalized d.radical u))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hAn := (full_comparison_actor h d path hb back hus hvs).2.2.2.2
  have hAW : ⁅W,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp hAn
  have hR : ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤ Z d.radical u :=
    critical_commutator_le_start_seed back
  have hEW : ⁅Z d.radical (path.walk.getVert 2),W⁆ ≤ W ⊔ Z d.radical u := by
    rw [commutator_comm]
    exact hcompare.trans (sup_le (hR.trans le_sup_right) (hAW.trans le_sup_left))
  have hEu : ⁅Z d.radical (path.walk.getVert 2),Z d.radical u⁆ ≤ W ⊔ Z d.radical u := by
    rw [commutator_comm]
    exact hR.trans le_sup_right
  exact sup_le hJn (normalizes_join_of_commutators (Z d.radical (path.walk.getVert 2))
    W (Z d.radical u) hEW hEu)

/-- A large preceding image discharges the full comparison for the same
root successor, preserving the directed root equality and both actors. -/
theorem Input.replacement_distance_four_large_root_full_kernel_normalized
    {geometry : Geometry d.radical} {a z u v s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (hlarge : Nat.card F^2 ≤
      (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (next : CriticalPath d.radical geometry v a) (hfirst : next.walk.getVert 1=s)
    (hroot : (Q d.radical a).relIndex (Z d.radical v)=Nat.card F) :
    Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2) ≤
      normalizer (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  exact h.replacement_distance_four_root_full_comparison_normalized d path hb back
    hus hvs next hfirst hroot
    ((h.replacement_distance_four_large_full_kernel_comparison d path hb back
      hus hvs hlarge).trans le_sup_left)

/-- Residual generation by these same two actors gives the full original
seed budgets, with root equality q and the retained selector y. -/
theorem Input.replacement_distance_four_large_root_full_seed_budget
    {geometry : Geometry d.radical} {a z u v s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (hlarge : Nat.card F^2 ≤
      (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (next : CriticalPath d.radical geometry v a) (hfirst : next.walk.getVert 1=s)
    (hroot : (Q d.radical a).relIndex (Z d.radical v)=Nat.card F)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (hres : Ltilde d.radical u ≤ Subgroup.SmallMover.join (U d.radical v)
      (Q d.radical v) (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2)) :
    (Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u ≤
        B d.radical u (geometry.Z_normal u) ∧
      (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical v) ≤ Nat.card F ∧
      (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical a) ≤ Nat.card F := by
  have hn := hres.trans (h.replacement_distance_four_large_root_full_kernel_normalized
    d path hb back hus hvs hlarge next hfirst hroot)
  obtain ⟨hY,hv⟩ := h.replacement_distance_four_normalized_neighbor_kernel_budget d
    geometry hb back.start_color hus hvs hn
  have ha := h.replacement_distance_four_normalized_selected_seed_budget d
    geometry hb back.start_color hus hvs y hy hya hn
  exact ⟨hY,hv.trans_eq hroot,ha.trans_eq hroot⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
