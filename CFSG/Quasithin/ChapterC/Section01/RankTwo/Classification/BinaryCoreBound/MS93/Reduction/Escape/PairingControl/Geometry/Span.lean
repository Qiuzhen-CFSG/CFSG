module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Paths
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The normalizer span after step (6)

Every P-conjugate of the backward radius-two group is centered two steps
from alpha. When b > 6, critical minimality makes it commute with V_alpha,
and hence with R_0. The step-(6) bound puts W in T_(alpha'-3); the selected
centralizer equality then puts W in Q_(alpha'-2). The initial edge identity
bounds [W,Z_alpha'] by R_0, so P together with Z_alpha' normalizes W.

The bound in (6) and the local generation equality are explicit premises of
these deductions, not asserted source consequences in this module.
Source: MS93 (1993), (4.3.2), final paragraph of p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : MS93.Geometry R}
variable {p : Counterexample geometry}

namespace BackwardChoice

theorem P_le_stabilizer (choice : BackwardChoice p) : choice.P ≤ stabilizer R p.a :=
  inf_le_left

theorem start_le_W (choice : BackwardChoice p) : V R p.a ≤ choice.W := le_sup_right

theorem back_le_W (choice : BackwardChoice p) : V R choice.back ≤ choice.W := by
  have h := le_iSup (fun g : choice.P =>
    NormalizerTransfer.rightConjugate (V R choice.back) g) 1
  have h' : V R choice.back ≤ NormalizerTransfer.conjugatesIn (V R choice.back) choice.P := by
    intro x hx
    apply h
    exact ⟨x, hx, by simp⟩
  exact h'.trans le_sup_left

theorem P_normalizes_W (choice : BackwardChoice p) :
    choice.P ≤ normalizer (choice.W : Set (FreeAmalgam R)) :=
  (le_inf (NormalizerTransfer.conjugatesIn_normalized _ _)
    (choice.P_le_stabilizer.trans (V_normalized p.a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem W_centralizes_start (choice : BackwardChoice p) (hb : 6 < geometry.b R) :
    choice.W ≤ centralizer (V R p.a : Set (FreeAmalgam R)) := by
  apply sup_le
  · apply iSup_le
    intro g
    have hga : act R (g : FreeAmalgam R) p.a = p.a := choice.P_le_stabilizer g.property
    change (V R choice.back).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom ≤ _
    rw [← V_act]
    apply V_centralizes_V_of_distance
      (by rw [action_preserves_color]; exact moving_color p.color_a choice.moving) p.color_a
    have hd := dist_act R (g : FreeAmalgam R) choice.back p.a
    rw [hga, SimpleGraph.dist_comm (u := choice.back), choice.moving.1] at hd
    omega
  · apply V_centralizes_V_of_distance p.color_a p.color_a
    simpa using (show 4 < geometry.b R by omega)

theorem W_centralizes_radius (choice : BackwardChoice p) [Finite M]
    (hb : 6 < geometry.b R) :
    choice.W ≤ centralizer (radiusCommutator p.a p.a' : Set (FreeAmalgam R)) :=
  (choice.W_centralizes_start hb).trans (centralizer_le p.radius_le_start)

theorem W_le_stabilizer (choice : BackwardChoice p) (hb : 4 ≤ geometry.b R) :
    choice.W ≤ stabilizer R p.a := by
  apply sup_le
  · apply iSup_le
    intro g
    have hga : act R (g : FreeAmalgam R) p.a = p.a := choice.P_le_stabilizer g.property
    change (V R choice.back).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom ≤ _
    rw [← V_act]
    apply V_le_stabilizer_of_distance
      (by rw [action_preserves_color]; exact moving_color p.color_a choice.moving)
    have hd := dist_act R (g : FreeAmalgam R) choice.back p.a
    rw [hga, SimpleGraph.dist_comm (u := choice.back), choice.moving.1] at hd
    omega
  · apply V_le_stabilizer_of_distance p.color_a
    simpa using (show 2 ≤ geometry.b R by omega)

variable [Finite M]

/-- Step (6), followed by (4), gives the stronger endpoint-side kernel bound. -/
theorem W_le_predecessor_kernel (choice : BackwardChoice p)
    (selected : CentralizerChoice p) (hb : 6 < geometry.b R)
    {d : Vertex R} (hd : Before p.a p.a' d 4) (hW : choice.W ≤ Q R d) :
    choice.W ≤ Q R p.c := by
  have hdt : Adjacent R d selected.t := hd.adjacent (geometry := geometry) selected.before
  have hct : Adjacent R p.c selected.t :=
    adjacent_symm R (selected.before.adjacent (geometry := geometry) p.before)
  have ht : color R selected.t = true := by
    have hn := adjacent_color_ne R hct
    rw [p.before_color] at hn
    cases h : color R selected.t <;> simp_all
  rw [← selected.centralizer_eq]
  exact le_inf (hW.trans (Q_le_adjacent_h R ht hdt)) (choice.W_centralizes_radius hb)

/-- This uses the actual initial R_0 edge identity, not a new pairing bound. -/
theorem commutator_end_le_radius (choice : BackwardChoice p) (initial : InitialFacts p)
    (hW : choice.W ≤ Q R p.c) :
    ⁅choice.W, Z R p.a'⁆ ≤ radiusCommutator p.a p.a' := by
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by have := initial.six_le; omega)
  have hct : Adjacent R p.c t := p.before.adjacent (geometry := geometry) ht
  have hcol : color R t = true := by
    have hn := adjacent_color_ne R ht.endpoint_adjacent
    rw [p.end_color] at hn
    cases h : color R t <;> simp_all
  rw [initial.radius_eq_edge t ht, edgeDisplacement, commutator_comm]
  exact commutator_mono le_rfl (hW.trans (Q_le_adjacent_h R hcol hct))

theorem local_generators_normalize_W (choice : BackwardChoice p) (initial : InitialFacts p)
    (hW : choice.W ≤ Q R p.c) :
    choice.P ⊔ Z R p.a' ≤ normalizer (choice.W : Set (FreeAmalgam R)) := by
  apply sup_le choice.P_normalizes_W
  apply le_normalizer_iff_commutator_le_left.mpr
  exact (choice.commutator_end_le_radius initial hW).trans
    (p.radius_le_start.trans choice.start_le_W)

/-- Relative local normality, with the source generation equality still explicit. -/
theorem W_normal (choice : BackwardChoice p) (initial : InitialFacts p)
    (hW : choice.W ≤ Q R p.c) (hgen : choice.P ⊔ Z R p.a' = stabilizer R p.a) :
    (choice.W.subgroupOf (stabilizer R p.a)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [← hgen]
  exact choice.local_generators_normalize_W initial hW

end BackwardChoice
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry
