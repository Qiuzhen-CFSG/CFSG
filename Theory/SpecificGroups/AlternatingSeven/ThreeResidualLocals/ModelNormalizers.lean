module

public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers.InvolutionGeometry
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers.BlockCalculations
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers.PairedCalculations
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Tactic

/-!
# Normalizers and three-prime residuals of the three concrete A₄ actions

Square-one elements recover the invariant four-point block or pair partition.
The block stabilizer is parametrized by S₄ × S₃, and the triple-transposition
centralizer by 48 distinct words. The small action calculations give the exact
normalizers and show that their cubic elements lie in A₄ × C₃ or the paired A₄.
The reverse residual inclusions follow from explicit cubic generators.

Source: the A₇ branch of Aschbacher–Smith 15.3.43, printed p.1140, with the
cycle structure in 1.1.5(3)(d), printed pp.501–502. These are intrinsic model
calculations; the classification of embeddings is a separate argument.
-/

public section
open Equiv Subgroup
open scoped Pointwise
namespace AlternatingSeven.ThreeResidualLocals

/-- The block used by the coordinates is literally `{0,1,2,3}`. -/
theorem fourPointSet_eq : fourPointSet = ({0, 1, 2, 3} : Set (Fin 7)) := by
  ext a
  change a.val < 4 ↔ a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3
  decide +revert +kernel

/-- The coordinate condition is the usual setwise stabilizer of the literal block. -/
theorem fourPointSetwiseStabilizer_eq_stabilizer :
    fourPointSetwiseStabilizer =
      MulAction.stabilizer Perm7 ({0, 1, 2, 3} : Set (Fin 7)) := by
  rw [← fourPointSet_eq]
  ext g
  change (∀ a, a ∈ fourPointSet ↔ g a ∈ fourPointSet) ↔
    g • fourPointSet = fourPointSet
  constructor
  · intro h
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).mp ha
    · intro hb
      exact ⟨g⁻¹ b, (h _).mpr (by simpa using hb), by simp⟩
  · intro h a
    constructor
    · intro ha
      rw [← h]
      exact ⟨a, ha, rfl⟩
    · intro ha
      rw [← h] at ha
      obtain ⟨b, hb, he⟩ := ha
      exact g.injective he ▸ hb

theorem naturalFour_normalizer_eq_fourPointSetwiseStabilizer :
    normalizer (naturalFour : Set Perm7) = fourPointSetwiseStabilizer := by
  apply le_antisymm natural_normalizer_le_fourPoint
  intro g hg
  rw [← blockHom_range] at hg
  obtain ⟨p, rfl⟩ := hg
  change blockHom p ∈ normalizer (closure {naturalThree, fourFlip} : Set Perm7)
  rw [mem_normalizer_pair_closure_iff]
  change blockHom p * naturalThree * (blockHom p)⁻¹ ∈ naturalFour ∧
    blockHom p * fourFlip * (blockHom p)⁻¹ ∈ naturalFour
  rw [naturalFour_eq_explicit]
  exact blockHom_normalizes_natural p

theorem diagonalFour_normalizer_eq :
    normalizer (diagonalFour : Set Perm7) =
      fourPointSetwiseStabilizer ⊓ alternatingGroup (Fin 7) := by
  have hi (p : Perm (Fin 4) × Perm (Fin 3)) :
      blockHom p ∈ normalizer (diagonalFour : Set Perm7) ↔
      blockHom p ∈ alternatingGroup (Fin 7) := by
    change blockHom p ∈ normalizer (closure {diagonalThree, fourFlip} : Set Perm7) ↔ _
    rw [mem_normalizer_pair_closure_iff]
    change (blockHom p * diagonalThree * (blockHom p)⁻¹ ∈ diagonalFour ∧
      blockHom p * fourFlip * (blockHom p)⁻¹ ∈ diagonalFour) ↔ _
    rw [diagonalFour_eq_explicit]
    exact blockHom_normalizes_diagonal_iff p
  apply le_antisymm
  · intro g hg
    have hb := diagonal_normalizer_le_fourPoint hg
    refine ⟨hb, ?_⟩
    rw [← blockHom_range] at hb
    obtain ⟨p, rfl⟩ := hb
    exact (hi p).mp hg
  · rintro g ⟨hb, he⟩
    rw [← blockHom_range] at hb
    obtain ⟨p, rfl⟩ := hb
    exact (hi p).mpr he

theorem pairedFour_normalizer_eq :
    normalizer (pairedFour : Set Perm7) = centralizer ({pairing} : Set Perm7) := by
  apply le_antisymm paired_normalizer_le_centralizer
  intro g hg
  obtain ⟨i, rfl⟩ := (mem_centralizer_pairing_iff_word g).mp hg
  exact pairedWord_mem_normalizer i

theorem normalizer_naturalFour_card : Nat.card
    (normalizer (naturalFour : Set Perm7)) = 144 := by
  rw [naturalFour_normalizer_eq_fourPointSetwiseStabilizer, fourPointSetwiseStabilizer_card]

theorem normalizer_pairedFour_card : Nat.card
    (normalizer (pairedFour : Set Perm7)) = 48 := by
  rw [pairedFour_normalizer_eq, centralizer_pairing_card]

private theorem card_inf_of_param {ι : Type*} (H K : Subgroup Perm7) (f : ι → Perm7)
    (hinj : Function.Injective f) (hmem : ∀ i, f i ∈ H)
    (hsurj : ∀ h ∈ H, ∃ i, f i = h) :
    Nat.card (H ⊓ K : Subgroup Perm7) = Nat.card {i : ι // f i ∈ K} := by
  let ff : {i : ι // f i ∈ K} → ↥(H ⊓ K) := fun i => ⟨f i, hmem i, i.property⟩
  symm
  apply Nat.card_eq_of_bijective ff
  constructor
  · intro i j hij
    exact Subtype.ext (hinj (congrArg Subtype.val hij))
  · intro g
    obtain ⟨i, hi⟩ := hsurj g g.property.1
    refine ⟨⟨i, ?_⟩, ?_⟩
    · rw [hi]
      exact g.property.2
    · exact Subtype.ext hi

local instance : Fintype (Perm (Fin 4)) := fintypePerm
local instance : Fintype (Perm (Fin 3)) := fintypePerm

private theorem even_block_card : Nat.card
    (fourPointSetwiseStabilizer ⊓ alternatingGroup (Fin 7) : Subgroup Perm7) = 72 := by
  rw [card_inf_of_param _ _ blockHom blockHom_injective
    (fun i => blockHom_range ▸ (show blockHom i ∈ blockHom.range from ⟨i, rfl⟩))
    (by intro g hg; rw [← blockHom_range] at hg; exact hg)]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem normalizer_diagonalFour_card : Nat.card
    (normalizer (diagonalFour : Set Perm7)) = 72 := by
  rw [diagonalFour_normalizer_eq, even_block_card]

theorem alternating_normalizer_naturalFour_card : Nat.card
    (alternatingGroup (Fin 7) ⊓ normalizer (naturalFour : Set Perm7) : Subgroup Perm7) = 72 := by
  rw [naturalFour_normalizer_eq_fourPointSetwiseStabilizer, inf_comm, even_block_card]

theorem alternating_normalizer_diagonalFour_card : Nat.card
    (alternatingGroup (Fin 7) ⊓ normalizer (diagonalFour : Set Perm7) : Subgroup Perm7) = 72 := by
  rw [diagonalFour_normalizer_eq, inf_left_comm, inf_idem, even_block_card]

theorem alternating_normalizer_pairedFour_card : Nat.card
    (alternatingGroup (Fin 7) ⊓ normalizer (pairedFour : Set Perm7) : Subgroup Perm7) = 24 := by
  rw [pairedFour_normalizer_eq, inf_comm]
  rw [card_inf_of_param _ _ pairedWord pairedWord_injective pairedWord_mem_centralizer
    (fun g hg => (mem_centralizer_pairing_iff_word g).mp hg)]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem threeResidual_le_of_cubes (B K : Subgroup Perm7)
    (h : ∀ g ∈ B, g ^ 3 = 1 → g ∈ K) :
    (primePowerGenerated 3 B).map B.subtype ≤ K := by
  rw [map_primePowerGenerated_eq_order_three_closure (MonoidHom.id Perm7)
    (fun _ _ hh => hh) B]
  apply (closure_le _).mpr
  rintro g ⟨hg, h3⟩
  apply h g hg
  rw [← h3]
  exact pow_orderOf_eq_one g

theorem natural_threeResidual_eq (J : Subgroup Perm7)
    (hJ : alternatingGroup (Fin 7) ≤ J) :
    (primePowerGenerated 3 (J ⊓ normalizer (naturalFour : Set Perm7) : Subgroup Perm7)).map
      (J ⊓ normalizer (naturalFour : Set Perm7)).subtype = expandedFour := by
  apply le_antisymm _ (expandedFour_le_natural_threeResidual J hJ)
  apply threeResidual_le_of_cubes
  rintro g ⟨_, hn⟩ h3
  rw [naturalFour_normalizer_eq_fourPointSetwiseStabilizer, ← blockHom_range] at hn
  obtain ⟨p, rfl⟩ := hn
  exact blockHom_cube_mem_expanded p h3

theorem diagonal_threeResidual_eq (J : Subgroup Perm7)
    (hJ : alternatingGroup (Fin 7) ≤ J) :
    (primePowerGenerated 3 (J ⊓ normalizer (diagonalFour : Set Perm7) : Subgroup Perm7)).map
      (J ⊓ normalizer (diagonalFour : Set Perm7)).subtype = expandedFour := by
  apply le_antisymm _ (expandedFour_le_diagonal_threeResidual J hJ)
  apply threeResidual_le_of_cubes
  rintro g ⟨_, hn⟩ h3
  have hb := diagonal_normalizer_le_fourPoint hn
  rw [← blockHom_range] at hb
  obtain ⟨p, rfl⟩ := hb
  exact blockHom_cube_mem_expanded p h3

theorem paired_threeResidual_eq (J : Subgroup Perm7)
    (hJ : alternatingGroup (Fin 7) ≤ J) :
    (primePowerGenerated 3 (J ⊓ normalizer (pairedFour : Set Perm7) : Subgroup Perm7)).map
      (J ⊓ normalizer (pairedFour : Set Perm7)).subtype = pairedFour := by
  apply le_antisymm _ (pairedFour_le_paired_threeResidual J hJ)
  apply threeResidual_le_of_cubes
  rintro g ⟨_, hn⟩ h3
  rw [pairedFour_normalizer_eq] at hn
  obtain ⟨i, rfl⟩ := (mem_centralizer_pairing_iff_word g).mp hn
  exact pairedWord_cube_mem i h3

theorem natural_threeResidual_card (J : Subgroup Perm7)
    (hJ : alternatingGroup (Fin 7) ≤ J) :
    Nat.card ((primePowerGenerated 3
      (J ⊓ normalizer (naturalFour : Set Perm7) : Subgroup Perm7)).map
      (J ⊓ normalizer (naturalFour : Set Perm7)).subtype) = 36 := by
  rw [natural_threeResidual_eq J hJ, expandedFour_card]

theorem diagonal_threeResidual_card (J : Subgroup Perm7)
    (hJ : alternatingGroup (Fin 7) ≤ J) :
    Nat.card ((primePowerGenerated 3
      (J ⊓ normalizer (diagonalFour : Set Perm7) : Subgroup Perm7)).map
      (J ⊓ normalizer (diagonalFour : Set Perm7)).subtype) = 36 := by
  rw [diagonal_threeResidual_eq J hJ, expandedFour_card]

theorem natural_threeResidual_ne (J : Subgroup Perm7)
    (hJ : alternatingGroup (Fin 7) ≤ J) :
    (primePowerGenerated 3 (J ⊓ normalizer (naturalFour : Set Perm7) : Subgroup Perm7)).map
      (J ⊓ normalizer (naturalFour : Set Perm7)).subtype ≠ naturalFour := by
  rw [natural_threeResidual_eq J hJ]
  exact expandedFour_ne_naturalFour

theorem diagonal_threeResidual_ne (J : Subgroup Perm7)
    (hJ : alternatingGroup (Fin 7) ≤ J) :
    (primePowerGenerated 3 (J ⊓ normalizer (diagonalFour : Set Perm7) : Subgroup Perm7)).map
      (J ⊓ normalizer (diagonalFour : Set Perm7)).subtype ≠ diagonalFour := by
  rw [diagonal_threeResidual_eq J hJ]
  exact expandedFour_ne_diagonalFour

theorem paired_threeResidual_card (J : Subgroup Perm7)
    (hJ : alternatingGroup (Fin 7) ≤ J) :
    Nat.card ((primePowerGenerated 3
      (J ⊓ normalizer (pairedFour : Set Perm7) : Subgroup Perm7)).map
      (J ⊓ normalizer (pairedFour : Set Perm7)).subtype) = 12 := by
  rw [paired_threeResidual_eq J hJ, pairedFour_card]

end AlternatingSeven.ThreeResidualLocals
