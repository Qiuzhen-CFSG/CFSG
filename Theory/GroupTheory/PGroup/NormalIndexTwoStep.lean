module

public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Normal steps of index two

Between two distinct ambient-normal subgroups of a finite two-group, choose
an ambient-normal intermediate subgroup of relative index two over the smaller
one. In the quotient, this is the existence of a normal subgroup of order two
inside a nontrivial normal subgroup.

This exposes the normal-step argument from `CyclicFourSectionFixedPoints` for
use in MacWilliams, Trans. AMS 150 (1970), §3(iv), 1.2.2, printed p.368.
-/

namespace Subgroup

/-- A strict inclusion of normal subgroups in a finite two-group contains
an ambient-normal step of index two. -/
public theorem exists_normal_index_two_step (P : Type*) [Group P] [Finite P] (hP : IsPGroup 2 P)
    (W H : Subgroup P) [W.Normal] [H.Normal] (hWH : W < H) :
    ∃ X : Subgroup P, X.Normal ∧ W ≤ X ∧ X ≤ H ∧ W.relIndex X = 2 := by
  let q := QuotientGroup.mk' W
  let Q := P ⧸ W
  let B := H.map q
  let : B.Normal := (inferInstance : H.Normal).map q (QuotientGroup.mk'_surjective W)
  have hB : B ≠ ⊥ := by
    intro hb
    have hh := (map_eq_bot_iff H).mp hb
    rw [QuotientGroup.ker_mk'] at hh
    exact (not_le_of_gt hWH) hh
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB
  have hQ : IsPGroup 2 Q := hP.to_quotient W
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  obtain ⟨n, hn⟩ := (hQ.to_subgroup B).exists_card_eq
  have hnpos : 1 ≤ n := by
    have hp : 1 < Nat.card B := Finite.one_lt_card
    by_contra hh
    have : n = 0 := by omega
    rw [hn, this] at hp
    norm_num at hp
  obtain ⟨Y, hYn, hYB, hYc⟩ :=
    exists_normal_subgroup_card_pow_of_normal B inferInstance hn 1 hnpos
  let : Y.Normal := hYn
  let X := Y.comap q
  have hWX : W ≤ X := by
    intro w hw
    change q w ∈ Y
    rw [show q w = 1 from (QuotientGroup.eq_one_iff _).mpr hw]
    exact Y.one_mem
  refine ⟨X, inferInstance, hWX, ?_, ?_⟩
  · calc
      X ≤ B.comap q := comap_mono hYB
      _ = H := comap_map_eq_self (by simpa only [q, QuotientGroup.ker_mk'] using hWH.le)
  · have hc : Nat.card (X.map q) = 2 := by
      rw [map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective W)]; exact le_top)]
      simpa using hYc
    rwa [← relIndex_ker, QuotientGroup.ker_mk'] at hc


end Subgroup
