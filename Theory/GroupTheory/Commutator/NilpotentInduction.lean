module
public import Mathlib.GroupTheory.Nilpotent

/-!
# Induction through the central series of a containing nilpotent group

Suppose W and P lie in a nilpotent subgroup N and P normalizes W. If every
subgroup Y of W whose commutator with P lies in Z already lies in Z, then
W lies in Z. Intersect W with the ascending central series of N and apply
the hypothesis successively. Neither normality of Z nor finiteness is needed.

This elementary induction is used in the center-free original symplectic
case of MS93 (3.6), pp.870--871, to exhaust the opposite natural layer.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem le_of_nilpotent_commutator_induction (N W P Z : Subgroup G)
    [Group.IsNilpotent N] (hWN : W ≤ N) (hPN : P ≤ N)
    (hn : P ≤ normalizer W)
    (hstep : ∀ Y : Subgroup G, Y ≤ W → ⁅Y,P⁆ ≤ Z → Y ≤ Z) : W ≤ Z := by
  have hseq (n : ℕ) : W ⊓ (Subgroup.upperCentralSeries N n).map N.subtype ≤ Z := by
    induction n with
    | zero => simp
    | succ n ih =>
      apply hstep _ inf_le_left
      apply le_trans (le_inf
        (le_normalizer_iff_commutator_le_left.mp hn |>.trans' (commutator_mono inf_le_left le_rfl))
        ?_) ih
      have hmap := map_mono (f := N.subtype) (commutator_upperCentralSeries_top_le (G := N) n)
      rw [map_commutator, ←MonoidHom.range_eq_map, range_subtype] at hmap
      exact (commutator_mono inf_le_right hPN).trans hmap
  obtain ⟨n,hn⟩ := Group.IsNilpotent.nilpotent' (G := N)
  have h := hseq n
  rwa [hn, ←MonoidHom.range_eq_map, range_subtype, inf_of_le_left hWN] at h
end Theory.GroupTheory
