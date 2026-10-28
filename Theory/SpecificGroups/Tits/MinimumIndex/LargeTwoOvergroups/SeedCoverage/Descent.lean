module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Schreier
public import Mathlib.Order.Atoms.Finite

/-!
# Five maximal-subgroup steps suffice for order-64 coverage

Starting with order 2048, every maximal step in the marked two-group halves
the order. An order-64 subgroup is contained in a maximal subgroup at each of
five steps. At the last step its containment is equality by cardinality.
This argument uses no assumed orders for the candidate rows.

Source: the maximal-index theorem for finite p-groups and the Parrott normal
form enumeration. The finite `Step` premises are discharged separately.
-/

public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
open Theory.GroupTheory.SubgroupEnumeration

/-- One maximal step, retaining containment and the exact next order. -/
theorem descend_step (l : Nat) (hstep : ∀ i, Step l i)
    (H : Subgroup S) (hH : Nat.card H = 64) (i : Fin (nodeCount l))
    (hle : H ≤ node l i) {n : Nat} (hcard : Nat.card (node l i) = 2 * n)
    (hn : 64 < 2 * n) :
    ∃ (j : Fin (nodeCount (l + 1))) (c : S),
      H.map (MulAut.conj c).toMonoidHom ≤ node (l + 1) j ∧
      Nat.card (node (l + 1) j) = n := by
  classical
  let : Finite (Subgroup S) := Finite.of_injective (fun H : Subgroup S => (H : Set S))
    SetLike.coe_injective
  have hlt : H < node l i := lt_of_le_of_ne hle (by
    intro he
    have := congrArg (fun K : Subgroup S => Nat.card K) he
    omega)
  obtain ⟨K, hHK, hK⟩ := exists_le_covBy_of_lt hlt
  obtain ⟨j, c, hc⟩ := hstep i K hK
  have hi := relIndex_two_of_covBy
    (IsPGroup.of_card (n := 11) atlas1600SylowTwoSubgroup_card) hK
  have hm := (K.subgroupOf (node l i)).card_mul_index
  have he := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.le).toEquiv
  change Nat.card (K.subgroupOf (node l i)) * K.relIndex (node l i) =
    Nat.card (node l i) at hm
  rw [he, hi, hcard] at hm
  have hKcard : Nat.card K = n := by omega
  refine ⟨j, c, ?_, ?_⟩
  · rw [← hc]
    exact Subgroup.map_mono hHK
  · rw [← hc, Subgroup.card_map_of_injective (MulAut.conj c).injective, hKcard]

/-- The last layer is literally the originally published seed family. -/
theorem terminal_node_map (i : Fin 122) : (node 5 i).map S.subtype = seed i := by
  rw [node, MonoidHom.map_closure, ← Set.range_comp]
  change Subgroup.closure (Set.range (fun k : Fin (seedIndices i).length =>
    atlas1600SylowTwoNormalForm ((seedIndices i)[k]))) =
    Subgroup.closure {x | ∃ n ∈ seedIndices i, atlas1600SylowTwoNormalForm n = x}
  congr 1
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, List.getElem_mem k.isLt, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hn
    exact ⟨k, congrArg atlas1600SylowTwoNormalForm hk⟩

private theorem map_conj_conj (H : Subgroup S) (a b : S) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

/-- Conditional assembly of all five finite layers. No candidate orders are
assumed: the last containment becomes equality at order 64. -/
theorem coverage_of_steps (hroot : node 0 0 = ⊤)
    (hsteps : ∀ l < 5, ∀ i, Step l i)
    (Q : Subgroup Atlas1600Group) (hle : Q ≤ S) (hQ : Nat.card Q = 64) :
    ∃ (i : Fin 122) (s : S), Q.map (MulAut.conj s.val).toMonoidHom = seed i := by
  let H := Q.subgroupOf S
  have hH : Nat.card H = 64 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans hQ
  have hrootcard : Nat.card (node 0 0) = 2 * 1024 := by
    rw [hroot, Nat.card_congr (Subgroup.topEquiv (G := S)).toEquiv]
    exact atlas1600SylowTwoSubgroup_card
  obtain ⟨i1, c1, h1, hc1⟩ := descend_step 0 (hsteps 0 (by decide)) H hH 0
    (by rw [hroot]; exact le_top) hrootcard (by decide)
  obtain ⟨i2, c2, h2, hc2⟩ := descend_step 1 (n := 512) (hsteps 1 (by decide)) _
    (by rwa [Subgroup.card_map_of_injective (MulAut.conj c1).injective]) i1 h1 hc1 (by decide)
  rw [map_conj_conj] at h2
  obtain ⟨i3, c3, h3, hc3⟩ := descend_step 2 (n := 256) (hsteps 2 (by decide)) _
    (by rwa [Subgroup.card_map_of_injective (MulAut.conj (c2 * c1)).injective]) i2 h2 hc2 (by decide)
  rw [map_conj_conj] at h3
  obtain ⟨i4, c4, h4, hc4⟩ := descend_step 3 (n := 128) (hsteps 3 (by decide)) _
    (by rwa [Subgroup.card_map_of_injective (MulAut.conj (c3 * (c2 * c1))).injective])
    i3 h3 hc3 (by decide)
  rw [map_conj_conj] at h4
  obtain ⟨i5, c5, h5, hc5⟩ := descend_step 4 (n := 64) (hsteps 4 (by decide)) _
    (by rwa [Subgroup.card_map_of_injective (MulAut.conj (c4 * (c3 * (c2 * c1)))).injective])
    i4 h4 hc4 (by decide)
  rw [map_conj_conj] at h5
  let c : S := c5 * (c4 * (c3 * (c2 * c1)))
  have he : H.map (MulAut.conj c).toMonoidHom = node 5 i5 :=
    Subgroup.eq_of_le_of_card_ge h5 (by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hH, hc5])
  have hm := congrArg (Subgroup.map S.subtype) he
  rw [terminal_node_map] at hm
  refine ⟨i5, c, ?_⟩
  have hf : S.subtype.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj c.val).toMonoidHom.comp S.subtype := by
    ext x
    rfl
  rw [Subgroup.map_map, hf, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hle] at hm
  exact hm

end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
end
