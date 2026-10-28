module

public import Theory.GroupTheory.SmallIndexSolvable
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect subgroups and quotients with small kernels

The coset action of a perfect subgroup on at most four points is trivial,
because its permutation image is both perfect and solvable. Consequently,
if the kernel of a homomorphism has order at most four and lies in a perfect
subgroup, every proper subgroup has proper image. A subgroup surjecting onto
the codomain would have at most as many cosets as there are kernel elements.

This supplies the lifting step over the order-three center in Aschbacher,
*Sporadic Groups* (1994), 47.10, printed p.266.
-/

public section

namespace Subgroup

/-- Perfect subgroups lie in every subgroup of index at most four. -/
theorem le_of_isPerfect_of_index_le_four {G : Type*} [Group G] [Finite G] (L U : Subgroup G)
    [Group.IsPerfect L] (hi : U.index ≤ 4) : L ≤ U := by
  classical
  let : Fintype (G ⧸ U) := Fintype.ofFinite _
  change Nat.card (G ⧸ U) ≤ 4 at hi
  have hc : Fintype.card (G ⧸ U) ≤ Fintype.card (Fin 4) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hi
  let e : (G ⧸ U) ↪ Fin 4 :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (G ⧸ U)) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let f := MulAction.toPermHom G (G ⧸ U)
  have hz : L.map f = ⊥ := by
    let : Group.IsPerfect (L.map f) := Group.IsPerfect.map f
    by_contra h
    let : Nontrivial (L.map f) := (Subgroup.nontrivial_iff_ne_bot _).mpr h
    exact Group.IsPerfect.not_isSolvable (L.map f) inferInstance
  have hk : L ≤ f.ker := (map_eq_bot_iff L).mp hz
  exact hk.trans (by rw [← U.normalCore_eq_ker]; exact U.normalCore_le)

/-- A kernel of order at most four contained in a perfect subgroup cannot
allow a proper subgroup to surject onto the codomain. -/
theorem map_ne_top_of_ker_le_perfect {G Q : Type*} [Group G] [Group Q] [Finite G]
    (f : G →* Q) (C U : Subgroup G) [Group.IsPerfect C]
    (hkC : f.ker ≤ C) (hk : Nat.card f.ker ≤ 4) (hU : U ≠ ⊤) : U.map f ≠ ⊤ := by
  intro hmap
  have hsurj : Function.Surjective (fun k : f.ker => (QuotientGroup.mk k.val : G ⧸ U)) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu, he⟩ := (show f g ∈ U.map f by rw [hmap]; trivial)
    refine ⟨⟨g * u⁻¹, ?_⟩, ?_⟩
    · simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    · apply QuotientGroup.eq.mpr
      simpa using hu
  have hi : U.index ≤ 4 := (Nat.card_le_card_of_surjective _ hsurj).trans hk
  have hker : f.ker ≤ U := hkC.trans (le_of_isPerfect_of_index_le_four C U hi)
  apply hU
  have hh := congrArg (Subgroup.comap f) hmap
  simpa only [comap_map_eq, sup_of_le_left hker, comap_top] using hh

end Subgroup
