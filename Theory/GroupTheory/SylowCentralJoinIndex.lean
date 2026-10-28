module
public import Mathlib.GroupTheory.Sylow

/-!
# The central-layer index in an actual Sylow subgroup

Let R be a Sylow two-subgroup of a finite group and let C,N be normal
subgroups, with C contained in R. If CN has index dividing two, then RN
is the whole group and the index of CN equals the index of
(R intersection N)(R intersection C) inside the original R.

The index of RN divides both two and the odd index of R, hence is one.
Normality of C allows the intersection of CN with R to distribute over C.
The relative-index identity for the normal subgroup CN then gives the exact
index inside R. No centrality or quaternion model is needed for this transfer.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article p26. There
C is the central Sylow kernel and N the actual normal SL2 constituent;
this identifies the original-group extension index with its Sylow geometry.
-/

namespace Sylow
public theorem sup_normal_eq_top_and_join_index
    {G : Type*} [Group G] [Finite G] (R : Sylow 2 G)
    (C N : Subgroup G) [C.Normal] [N.Normal]
    (hCR : C ≤ (R : Subgroup G)) (hindex : (C ⊔ N).index ∣ 2) :
    (R : Subgroup G) ⊔ N = ⊤ ∧
      (N.comap (R : Subgroup G).subtype ⊔ C.comap (R : Subgroup G).subtype).index =
        (C ⊔ N).index := by
  have hd : ((R : Subgroup G) ⊔ N).index ∣ 2 :=
    (Subgroup.index_dvd_of_le (sup_le_sup_right hCR N)).trans hindex
  have hodd : ¬ 2 ∣ ((R : Subgroup G) ⊔ N).index := by
    intro h
    exact R.not_dvd_index (h.trans (Subgroup.index_dvd_of_le le_sup_left))
  have htop : (R : Subgroup G) ⊔ N = ⊤ := by
    apply Subgroup.index_eq_one.mp
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · exact (hodd (by rw [h])).elim
  have hlocal : N.comap (R : Subgroup G).subtype ⊔ C.comap (R : Subgroup G).subtype =
      (C ⊔ N).comap (R : Subgroup G).subtype := by
    apply le_antisymm ?_ ?_
    · exact sup_le (Subgroup.comap_mono le_sup_right) (Subgroup.comap_mono le_sup_left)
    · intro x hx
      obtain ⟨c, hc, n, hn, he⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      change c * n = (x : G) at he
      have hnR : n ∈ (R : Subgroup G) := by
        have h := (R : Subgroup G).mul_mem ((R : Subgroup G).inv_mem (hCR hc)) x.property
        simpa only [← he, inv_mul_cancel_left] using h
      have hprod : (⟨c, hCR hc⟩ : R) * ⟨n, hnR⟩ = x := by
        apply Subtype.ext
        exact he
      rw [← hprod]
      exact (N.comap (R : Subgroup G).subtype ⊔ C.comap (R : Subgroup G).subtype).mul_mem
        ((show C.comap (R : Subgroup G).subtype ≤ _ from le_sup_right) hc)
        ((show N.comap (R : Subgroup G).subtype ≤ _ from le_sup_left) hn)
  refine ⟨htop, ?_⟩
  rw [hlocal]
  change (C ⊔ N).relIndex (R : Subgroup G) = (C ⊔ N).index
  rw [← Subgroup.relIndex_sup_right, sup_left_comm, htop, sup_top_eq,
    Subgroup.relIndex_top_right]
end Sylow
