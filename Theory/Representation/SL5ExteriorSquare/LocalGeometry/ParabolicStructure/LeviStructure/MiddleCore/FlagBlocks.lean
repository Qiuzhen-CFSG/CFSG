module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Blocks
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular

/-!
# Small diagonal blocks of the middle residual-flag groups

For either middle parabolic, the join of the small-block kernel with the
standard flag group is exactly the preimage of the upper unitriangular SL₂.
Both inclusions use the literal diagonal blocks: an upper triangular pair
lifts to an upper triangular five-dimensional matrix.

Source: Aschbacher–Smith, Lemma 12.5.2(1–2), printed p.817/PDF p.834.
-/

@[expose] public section
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare.MiddleCore
open SL5TenDimensional
open Theory.SpecificGroups.LinearSylowNormalizers

/-- The standard upper unitriangular subgroup of the small SL₂ block. -/
abbrev smallUnipotent : Subgroup SL(2, ZMod 2) := unipotent 2 (ZMod 2)

private theorem binary_upper_mem_unipotent {n : ℕ} (a : SL(n, ZMod 2))
    (ha : a.val.IsUpperTriangular) : a ∈ unipotent n (ZMod 2) := by
  apply (mem_unipotent n (ZMod 2) a).mpr
  refine ⟨(mem_borel n (ZMod 2) a).mpr ha, fun i => ?_⟩
  have hd := a.property
  rw [Matrix.det_of_isUpperTriangular ha] at hd
  have hp : (∏ j, a.val j j) ≠ 0 := by rw [hd]; exact one_ne_zero
  have hi := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hi

private theorem flag_iff_upper (g : Group) :
    g ∈ flagGroup ↔ g.val.IsUpperTriangular := by
  constructor
  · intro hg i j hji
    have hk : j.val + 1 < 5 := by change j.val < i.val at hji; omega
    exact (mem_parabolic_iff_lowerLeft_zero (j.val + 1) g).mp
      ((Subgroup.mem_iInf.mp hg) ⟨j.val + 1, hk⟩) i j
        (by change j.val < i.val at hji; omega) (by omega)
  · intro hg
    apply Subgroup.mem_iInf.mpr
    intro k
    apply (mem_parabolic_iff_lowerLeft_zero _ g).mpr
    intro i j hi hj
    exact hg (by change j.val < i.val; omega)

private theorem flag_blocks_upper (k : ℕ) (hk : k ≤ 5) (g : parabolic k) :
    g.val ∈ flagGroup ↔
      (parabolicLeviHom k hk g).1.val.IsUpperTriangular ∧
      (parabolicLeviHom k hk g).2.val.IsUpperTriangular := by
  rw [flag_iff_upper]
  constructor
  · intro h
    constructor
    · intro i j hji
      rw [parabolicLeviHom_fst_entry]
      exact h hji
    · intro i j hji
      rw [parabolicLeviHom_snd_entry]
      exact h (by change k+j.val < k+i.val; exact Nat.add_lt_add_left hji k)
  · rintro ⟨ha, hd⟩ i j hji
    change j.val < i.val at hji
    by_cases hi : i.val < k
    · have hj : j.val < k := lt_trans hji hi
      exact (parabolicLeviHom_fst_entry k hk g ⟨i.val, hi⟩ ⟨j.val, hj⟩).symm.trans
        (ha hji)
    · by_cases hj : j.val < k
      · exact (mem_parabolic_iff_lowerLeft_zero k g.val).mp g.property i j
          (Nat.le_of_not_gt hi) hj
      · have hei : (⟨k + (i.val-k), by omega⟩ : Fin 5) = i := Fin.ext (by dsimp; omega)
        have hej : (⟨k + (j.val-k), by omega⟩ : Fin 5) = j := Fin.ext (by dsimp; omega)
        have he := parabolicLeviHom_snd_entry k hk g
          ⟨i.val-k, by omega⟩ ⟨j.val-k, by omega⟩
        rw [hei, hej] at he
        exact he.symm.trans (hd (by change j.val-k < i.val-k; omega))

private theorem two_small_flag_image :
    (flagGroup.subgroupOf (parabolic 2)).map parabolicTwoSmallBlock = smallUnipotent := by
  apply le_antisymm
  · rintro a ⟨g, hg, rfl⟩
    exact binary_upper_mem_unipotent _ ((flag_blocks_upper 2 (by decide) g).mp hg).1
  · intro a ha
    obtain ⟨g, hg⟩ := parabolicLeviHom_surjective 2 (by decide) (a, 1)
    refine ⟨g, ?_, congrArg Prod.fst hg⟩
    apply (flag_blocks_upper 2 (by decide) g).mpr
    rw [hg]
    exact ⟨(mem_borel 2 (ZMod 2) a).mp ((mem_unipotent 2 (ZMod 2) a).mp ha).1, Matrix.blockTriangular_one⟩

private theorem three_small_flag_image :
    (flagGroup.subgroupOf (parabolic 3)).map parabolicThreeSmallBlock = smallUnipotent := by
  apply le_antisymm
  · rintro a ⟨g, hg, rfl⟩
    exact binary_upper_mem_unipotent _ ((flag_blocks_upper 3 (by decide) g).mp hg).2
  · intro a ha
    obtain ⟨g, hg⟩ := parabolicLeviHom_surjective 3 (by decide) (1, a)
    refine ⟨g, ?_, congrArg Prod.snd hg⟩
    apply (flag_blocks_upper 3 (by decide) g).mpr
    rw [hg]
    exact ⟨Matrix.blockTriangular_one, (mem_borel 2 (ZMod 2) a).mp ((mem_unipotent 2 (ZMod 2) a).mp ha).1⟩

/-- H₂: the large-block subgroup joined with the actual standard flag group. -/
noncomputable def twoFlag : Subgroup Group := parabolicTwoLargeBlock ⊔ flagGroup

/-- H₃, with the reversed 3+2 block convention. -/
noncomputable def threeFlag : Subgroup Group := parabolicThreeLargeBlock ⊔ flagGroup

theorem twoFlag_le : twoFlag ≤ parabolic 2 :=
  sup_le parabolicTwoLargeBlock_le (flagGroup_le_parabolic 2 (by decide))

theorem threeFlag_le : threeFlag ≤ parabolic 3 :=
  sup_le parabolicThreeLargeBlock_le (flagGroup_le_parabolic 3 (by decide))

theorem twoFlag_eq_small_preimage : twoFlag =
    (smallUnipotent.comap parabolicTwoSmallBlock).map (parabolic 2).subtype := by
  rw [← two_small_flag_image, Subgroup.comap_map_eq, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le (flagGroup_le_parabolic 2 (by decide)), sup_comm]
  rfl

theorem threeFlag_eq_small_preimage : threeFlag =
    (smallUnipotent.comap parabolicThreeSmallBlock).map (parabolic 3).subtype := by
  rw [← three_small_flag_image, Subgroup.comap_map_eq, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le (flagGroup_le_parabolic 3 (by decide)), sup_comm]
  rfl

@[simp] theorem mem_twoFlag (g : parabolic 2) :
    g.val ∈ twoFlag ↔ parabolicTwoSmallBlock g ∈ smallUnipotent := by
  rw [twoFlag_eq_small_preimage]
  exact Subgroup.mem_map_iff_mem (parabolic 2).subtype_injective

@[simp] theorem mem_threeFlag (g : parabolic 3) :
    g.val ∈ threeFlag ↔ parabolicThreeSmallBlock g ∈ smallUnipotent := by
  rw [threeFlag_eq_small_preimage]
  exact Subgroup.mem_map_iff_mem (parabolic 3).subtype_injective

end Representation.SL5ExteriorSquare.MiddleCore
