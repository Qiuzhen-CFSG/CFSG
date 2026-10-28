module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.PointParabolic.MathieuOverlap.Elementary
public import Theory.GroupTheory.PRadical.NormalizerRestriction

/-!
# The native symmetric-linear point two-local

The literal max4 point parabolic carries a certified elementary subgroup of
order at least `2^11`, normalized by the whole parabolic.  Its full ambient
normalizer is therefore a genuine two-local, retaining the literal native
subgroup and the inclusion of the point parabolic.  The radical consumer keeps
that ambient normalizer as the actual local denominator.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Section 2.3,
p.493; the native point-parabolic elementary certificate is in
`SymmetricLinear.PointParabolic.MathieuOverlap.Elementary`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover
open Janko4.LocalStructure.SymmetricLinear

theorem pointParabolic_le_nativeMax4 (j : Fin 5) :
    pointParabolic j ≤ max4Subgroup := by
  unfold pointParabolic
  exact map_subtype_le _

/-- A native point-parabolic elementary subgroup, chosen for each point. -/
noncomputable def nativePointElementary (j : Fin 5) : Subgroup Model :=
  Classical.choose (MathieuOverlap.pointParabolic_large_elementary j)

theorem nativePointElementary_le (j : Fin 5) : nativePointElementary j ≤ pointParabolic j := by
  exact (Classical.choose_spec (MathieuOverlap.pointParabolic_large_elementary j)).1

theorem nativePointElementary_le_nativeMax4 (j : Fin 5) :
    nativePointElementary j ≤ max4Subgroup :=
  (nativePointElementary_le j).trans (pointParabolic_le_nativeMax4 j)

theorem nativePointElementary_elementary (j : Fin 5) : IsElementaryAbelian 2 (nativePointElementary j) := by
  exact (Classical.choose_spec (MathieuOverlap.pointParabolic_large_elementary j)).2.1

theorem nativePointElementary_card_lower (j : Fin 5) :
    2048 ≤ Nat.card (nativePointElementary j) := by
  exact (Classical.choose_spec
    (MathieuOverlap.pointParabolic_large_elementary j)).2.2.1

theorem nativePointElementary_nontrivial (j : Fin 5) : nativePointElementary j ≠ ⊥ := by
  intro h
  have hc := nativePointElementary_card_lower j
  rw [h, card_bot] at hc
  omega

theorem pointParabolic_le_nativePointNormalizer (j : Fin 5) :
    pointParabolic j ≤ normalizer (nativePointElementary j : Set Model) := by
  exact (Classical.choose_spec
    (MathieuOverlap.pointParabolic_large_elementary j)).2.2.2

/-- The ambient normalizer of the native point elementary subgroup is a
literal two-local. -/
@[expose] def nativePointNormalizer (j : Fin 5) : Subgroup Model :=
  normalizer (nativePointElementary j : Set Model)

theorem nativePointNormalizer_isTwoLocal (j : Fin 5) : IsTwoLocal (nativePointNormalizer j) := by
  let _ := nativePointElementary_elementary j
  exact ⟨nativePointElementary j, nativePointElementary_nontrivial j,
    IsElementaryAbelian.isPGroup 2 _, rfl⟩

theorem pointParabolic_le_nativePointNormalizer' (j : Fin 5) :
    pointParabolic j ≤ nativePointNormalizer j :=
  pointParabolic_le_nativePointNormalizer j

/-- Literal radical restriction for a radical whose whole normalizer lies in
this native point-local normalizer. -/
theorem radical_local_of_nativePointNormalizer
    (P : Subgroup Model) (hP : P.IsPRadical 2)
    (j : Fin 5) (hNP : normalizer (P : Set Model) ≤ nativePointNormalizer j) :
    let M := nativePointNormalizer j
    IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  dsimp only
  let M : Subgroup Model := nativePointNormalizer j
  have hPM : P ≤ M := P.le_normalizer.trans hNP
  have hNN : normalizer (P : Set Model) ≤ normalizer (M : Set Model) :=
    hNP.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hNN
  refine ⟨nativePointNormalizer_isTwoLocal j, hNP, hPM, ?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hNN, hcore, ?_⟩
  · rw [← subgroupOf_normalizer_eq hPM, map_subgroupOf_eq_of_le hNP]
  · rw [hcore, map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.ElementaryNormalizerCover
