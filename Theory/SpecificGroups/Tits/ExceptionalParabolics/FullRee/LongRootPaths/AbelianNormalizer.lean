module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.RootRelations
public import Theory.GroupTheory.AbelianExponentFourRecognition

/-!
# The marked C₄ × C₄ in the full Ree five-normalizer

The actual roots q=u₁ and s=s₅ commute and have distinct nontrivial squares.
They generate the indicated group of order16. Both normalize the specified
five-rotation, and the cyclic diagonal <s q⁻¹> has square z. These marks are
retained for the original J.4 complement and Q₀ intersection calculations.
Source: Aschbacher--Smith J.4.7, printed pp.442--443.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
open Subgroup ReeF4
open Tits.InvolutionRootGeometry.BinaryDerivedFusion
open RootRelations

/-- The literal cyclic group of order five. -/
def five : Subgroup (Model 0) := zpowers rotation

/-- Its actual ambient normalizer. -/
def fiveNormalizer : Subgroup (Model 0) := normalizer (five : Set (Model 0))

/-- The actual abelian 2-part of its first-parabolic normalizer. -/
def I : Subgroup (Model 0) := zpowers s ⊔ zpowers q

/-- The marked cyclic diagonal whose square is the initial long root z. -/
def Iz : Subgroup (Model 0) := zpowers (s*q⁻¹)

theorem q_square : q^2 = u := by
  apply toSplitGroup_injective 0
  rw [map_pow, q, fixedU_matrix, u, Atlas.a, atlasEmbedding_generator_matrix]
  simp only [pow_two, DerivedTits.Realization.assignment]

theorem s_four : s^4 = 1 := by
  have h : atlas1600ParrottAssignment .s5 ^ 4 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using
      atlas1600ParrottAssignment_relations .i_s5
  simpa only [s, map_pow, map_one] using congrArg atlasEmbedding h

private theorem u_two : u^2 = 1 := by
  have h : atlas1600ParrottAssignment .s1 ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using
      atlas1600ParrottAssignment_relations .i_s1
  simpa only [u, Atlas.a, map_pow, map_one] using congrArg atlasEmbedding h

theorem q_four : q^4 = 1 := by
  calc q^4 = (q^2)^2 := by rw [← pow_mul]
       _ = 1 := by rw [q_square, u_two]

private theorem atlas_separation :
    atlas1600ParrottAssignment .s1 ≠ 1 ∧
      (atlas1600ParrottAssignment .s5)^2 ≠ 1 ∧
      (atlas1600ParrottAssignment .s5)^2 ≠ atlas1600ParrottAssignment .s1 := by
  have h1 : (atlas1600ParrottAssignment .s1).val 0 = 930 := by
    rw [atlas1600ParrottAssignment_val]
    decide +kernel
  have h5 : ((atlas1600ParrottAssignment .s5)^2).val 0 = 1193 := by
    change ((atlas1600ParrottAssignment .s5).val ^ 2) 0 = 1193
    rw [atlas1600ParrottAssignment_val]
    decide +kernel
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  · have hh := congrArg (fun x : Atlas1600Group => x.val 0) h
    rw [h1] at hh
    exact (by decide : (930 : Fin 1600) ≠ 0) hh
  · have hh := congrArg (fun x : Atlas1600Group => x.val 0) h
    rw [h5] at hh
    exact (by decide : (1193 : Fin 1600) ≠ 0) hh
  · have hh := congrArg (fun x : Atlas1600Group => x.val 0) h
    rw [h5, h1] at hh
    exact (by decide : (1193 : Fin 1600) ≠ 930) hh

theorem q_square_ne : q^2 ≠ 1 := by
  rw [q_square]
  exact fun h => atlas_separation.1 (atlasEmbedding_injective (by simpa only [u, Atlas.a, map_one] using h))

theorem s_square_ne : s^2 ≠ 1 := by
  exact fun h => atlas_separation.2.1 (atlasEmbedding_injective (by
    simpa only [s, map_pow, map_one] using h))

theorem squares_distinct : s^2 ≠ q^2 := by
  rw [q_square]
  exact fun h => atlas_separation.2.2 (atlasEmbedding_injective (by
    simpa only [s, u, Atlas.a, map_pow] using h))

theorem q_order : orderOf q = 4 := orderOf_eq_four_of_fourth_power q_four q_square_ne

theorem s_order : orderOf s = 4 := orderOf_eq_four_of_fourth_power s_four s_square_ne

theorem I_card : Nat.card I = 16 := by
  have hd := disjoint_zpowers_of_order_four_distinct_squares s_order q_order squares_distinct
  have hc (a : zpowers s) (b : zpowers q) : Commute (a : Model 0) (b : Model 0) := by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp a.property
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp b.property
    rw [← hm, ← hn]
    exact q_commutes_s.symm.zpow_zpow m n
  let f := (zpowers s).subtype.noncommCoprod (zpowers q).subtype hc
  have hf : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ hc).mpr
      ⟨Subtype.val_injective, Subtype.val_injective, by simpa using hd⟩
  have hr : f.range = I := by
    exact (MonoidHom.noncommCoprod_range _ _ hc).trans (by simp only [range_subtype, I])
  have he := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  rw [hr, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, s_order, q_order] at he
  exact he.symm

theorem I_equiv : Nonempty (I ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let a : I := ⟨s, mem_sup_left (mem_zpowers _)⟩
  let b : I := ⟨q, mem_sup_right (mem_zpowers _)⟩
  exact nonempty_mulEquiv_c4_square_of_independent_roots I_card a b
    (Subtype.ext s_four) (Subtype.ext q_four)
    (fun h => s_square_ne (congrArg Subtype.val h))
    (fun h => q_square_ne (congrArg Subtype.val h))
    (fun h => squares_distinct (congrArg Subtype.val h))
    (Subtype.ext q_commutes_s.symm.eq)

theorem q_mem_sylow : q ∈ S := fixedU_zero_mem_unipotent

theorem s_mem_sylow : s ∈ S := by
  apply atlas_sylow_map_le
  apply mem_map_of_mem
  rw [ExceptionalParabolics.S, atlas1600SylowTwoSubgroup_eq]
  exact subset_closure (by simp)

theorem I_le_sylow : I ≤ S := sup_le (zpowers_le.mpr s_mem_sylow) (zpowers_le.mpr q_mem_sylow)

private theorem normalizes_of_rotation {x : Model 0} (hx : x*rotation = rotation^3*x) :
    x ∈ fiveNormalizer := by
  rw [fiveNormalizer, mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [five, MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    change x*rotation*x⁻¹ ∈ zpowers rotation
    rw [mul_inv_eq_of_eq_mul hx]
    exact pow_mem (mem_zpowers _) _
  · rw [card_map_of_injective (MulAut.conj x).injective]

theorem I_le_normalizer : I ≤ fiveNormalizer :=
  sup_le (zpowers_le.mpr (normalizes_of_rotation s_rotation))
    (zpowers_le.mpr (normalizes_of_rotation q_rotation))

theorem diagonal_square : (s*q⁻¹)^2 = z := by
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using u_two)
  rw [q_commutes_s.symm.inv_right.mul_pow, inv_pow, q_square, hu]
  have hz : z = u*s^2 := by
    simp only [z, atlas1600R5_eq, map_mul, map_pow, u, Atlas.a, s]
  rw [hz]
  simpa only [q_square] using (q_commutes_s.symm.pow_pow 2 2).eq

theorem z_ne_one : z ≠ 1 := fun h => atlas1600R5_ne_one
  (atlasEmbedding_injective (by simpa only [z, map_one] using h))

theorem diagonal_order : orderOf (s*q⁻¹) = 4 := by
  apply orderOf_eq_four_of_fourth_power
  · rw [q_commutes_s.symm.inv_right.mul_pow, s_four, inv_pow, q_four, inv_one, mul_one]
  · rw [diagonal_square]
    exact z_ne_one

theorem Iz_card : Nat.card Iz = 4 := by rw [Iz, Nat.card_zpowers, diagonal_order]

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
