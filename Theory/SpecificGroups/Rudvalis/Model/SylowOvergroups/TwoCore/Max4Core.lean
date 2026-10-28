module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoCore.Max4Core.Identities
public import Theory.GroupTheory.PCoreFromTwoNormalizers
public import Theory.AtlasPort.OtherSporadic.GroupTheory.ThreeTranspositionFrames

/-!
# A nontrivial intrinsic two-core in the fourth Rudvalis local subgroup

The three commuting involutions checked in `Max4Core.Identities` generate a
two-subgroup. Their conjugation identities show that the two actual max4
generators normalize it, so its copy inside max4 is normal and lies in
O₂(max4). The displayed element z is nonidentity.

This construction uses no cardinality bound or exhaustive subgroup list.
Source application: Aschbacher--Smith, Proposition 1.3.4, printed p.511
(PDF p.528), citing [Asc86b]; the concrete word sources are attributed in
SylowOvergroups.Definitions and Model.PermutationData.
-/

namespace Rudvalis.SylowOvergroups.TwoCore

open Subgroup Max4Core

private theorem x_inv : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using x_sq)

private theorem y_inv : y⁻¹ = y ^ 2 :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_succ'] using y_cube)

private theorem z₁_sq : z₁ ^ 2 = 1 := by
  rw [z₁, ← y_inv]
  calc
    (y⁻¹ * z * y) ^ 2 = y⁻¹ * z ^ 2 * y := by
      simpa only [inv_inv] using (conj_pow (a := y⁻¹) (b := z) (i := 2))
    _ = 1 := by rw [z_sq]; simp

private theorem z₂_sq : z₂ ^ 2 = 1 := by
  have he : z₂ = x⁻¹ * z₁ * x := by rw [x_inv]; rfl
  rw [he]
  calc
    (x⁻¹ * z₁ * x) ^ 2 = x⁻¹ * z₁ ^ 2 * x := by
      simpa only [inv_inv] using (conj_pow (a := x⁻¹) (b := z₁) (i := 2))
    _ = 1 := by rw [z₁_sq]; simp

private def seed : Subgroup Model := closure {z, z₁, z₂}

private theorem z_mem_seed : z ∈ seed := subset_closure (by simp)
private theorem z₁_mem_seed : z₁ ∈ seed := subset_closure (by simp)
private theorem z₂_mem_seed : z₂ ∈ seed := subset_closure (by simp)

private theorem seed_isPGroup : IsPGroup 2 seed := by
  apply Atlas.GroupTheory.commuting_involution_closure_isTwoGroup
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact z_sq
    · exact z₁_sq
    · exact z₂_sq
  · intro g hg k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hk
    rcases hg with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl
    · exact Commute.refl _
    · exact z_comm_z₁
    · exact z_comm_z₂
    · exact z_comm_z₁.symm
    · exact Commute.refl _
    · exact z₁_comm_z₂
    · exact z_comm_z₂.symm
    · exact z₁_comm_z₂.symm
    · exact Commute.refl _

private theorem seed_le_max4 : seed ≤ max4 := by
  have hx : x ∈ max4 := subset_closure (by simp [x])
  have hy : y ∈ max4 := subset_closure (by simp [y])
  have hz : z ∈ max4 := max4.pow_mem
    (max4.mul_mem (max4.mul_mem (max4.mul_mem
      (max4.mul_mem (max4.mul_mem hx (max4.pow_mem hy 2)) hx) hy) hx) hy) 8
  have hz₁ : z₁ ∈ max4 := max4.mul_mem (max4.mul_mem (max4.pow_mem hy 2) hz) hy
  have hz₂ : z₂ ∈ max4 := max4.mul_mem (max4.mul_mem hx hz₁) hx
  apply (closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact hz
  · exact hz₁
  · exact hz₂

private theorem mem_normalizer_generated {G : Type*} [Group G] [Finite G]
    (s : Set G) (g : G)
    (h : ∀ k ∈ s, g * k * g⁻¹ ∈ closure s) :
    g ∈ normalizer (closure s : Set G) := by
  have hh : closure s ≤ (closure s).comap (MulAut.conj g).toMonoidHom :=
    (closure_le _).mpr h
  exact mem_normalizer_fintype fun k hk => hh hk

private theorem mem_normalizer_seed (g : Model)
    (hz : g * z * g⁻¹ ∈ seed)
    (hz₁ : g * z₁ * g⁻¹ ∈ seed)
    (hz₂ : g * z₂ * g⁻¹ ∈ seed) :
    g ∈ normalizer (seed : Set Model) := by
  apply mem_normalizer_generated {z, z₁, z₂}
  intro k hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with rfl | rfl | rfl
  · exact hz
  · exact hz₁
  · exact hz₂

private theorem max4_le_normalizer_seed : max4 ≤ normalizer (seed : Set Model) := by
  have hx : x ∈ normalizer (seed : Set Model) := by
    apply mem_normalizer_seed
    · rw [x_inv, x_z_x]
      exact z_mem_seed
    · rw [x_inv]
      exact z₂_mem_seed
    · rw [x_inv]
      have he : x * z₂ * x = z₁ := by
        calc
          x * z₂ * x = (x * x) * z₁ * (x * x) := by simp only [z₂, mul_assoc]
          _ = z₁ := by rw [← pow_two, x_sq]; simp
      rw [he]
      exact z₁_mem_seed
  have hy : y ∈ normalizer (seed : Set Model) := by
    apply mem_normalizer_seed
    · rw [y_inv, y_z_y_sq]
      exact seed.mul_mem z_mem_seed z₁_mem_seed
    · rw [y_inv]
      have he : y * z₁ * y ^ 2 = z := by
        calc
          y * z₁ * y ^ 2 = y ^ 3 * z * y ^ 3 := by simp only [z₁, pow_succ, pow_zero, one_mul, mul_assoc]
          _ = z := by rw [y_cube]; simp
      rw [he]
      exact z_mem_seed
    · rw [y_inv, y_z₂_y_sq]
      exact seed.mul_mem z₁_mem_seed z₂_mem_seed
  apply (closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact hx
  · exact hy

/-- The concrete fourth ATLAS word subgroup has nontrivial intrinsic two-core. -/
public theorem max4_pCore_ne_bot : pCore 2 max4 ≠ ⊥ := by
  apply pCore_ne_bot_of_normalized_nontrivial max4 seed seed_le_max4 seed_isPGroup
  · intro h
    exact z_ne_one (mem_bot.mp (h ▸ z_mem_seed))
  · exact max4_le_normalizer_seed

end Rudvalis.SylowOvergroups.TwoCore
