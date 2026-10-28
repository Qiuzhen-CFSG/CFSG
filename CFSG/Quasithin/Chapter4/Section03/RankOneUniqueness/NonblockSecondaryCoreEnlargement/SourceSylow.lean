module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceConstruction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The original Sylow intersection and crossing action

The original S is Sylow in H and normalizes K₂. Restriction to K₂S and
normal intersection therefore make the literal S∩K₂ Sylow in K₂. Its
image is Sylow in the actual secondary action image. No replacement
Sylow or abstract parabolic is selected.

The original crossing normalizes the image of S and has square in that
image, while moving the image of R₂. These are the source inputs for the
linear-four parabolic frame; they impose no involution or field-bit condition.
Source: Aschbacher–Smith, original 4.3.3–5,4.3.11–16, pp.614–618.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The literal original Sylow intersection is Sylow in the secondary residual. -/
theorem secondary_original_sylow (D : Chapter12.Section02.ChosenModule T L V) :
    Chapter1.IsSylowIn 2 (S c ⊓ secondary c) (secondary c) := by
  let J := secondary c ⊔ S c
  have hJH : J ≤ c.H := sup_le
    (secondary_le_original.trans (map_subtype_le _)) inf_le_right
  have hSJ : Chapter1.IsSylowIn 2 (S c) J :=
    (show Chapter1.IsSylowIn 2 (S c) c.H from c.sylow).restrict le_sup_right hJH
  let : ((secondary c).subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (secondary c).le_normalizer (sylow_normalizes_secondary D))
  exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSJ le_sup_left
    (inferInstance : ((secondary c).subgroupOf J).Normal).isSubnormal

namespace EndgameSieve.SecondaryActionData

/-- The same S∩K₂ maps to a Sylow subgroup of the actual secondary image. -/
theorem original_sylow_image (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    Chapter1.IsSylowIn 2 (image s (S c ⊓ secondary c)) (secondaryImage s) := by
  have hK : secondary c ≤ rootNormalizer c := s.secondary_le.trans (map_subtype_le _)
  have hs : Chapter1.IsSylowIn 2
      ((S c ⊓ secondary c).subgroupOf (rootNormalizer c))
      ((secondary c).subgroupOf (rootNormalizer c)) := by
    apply (Chapter1.IsSylowIn.map_iff (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective).mp
    rw [map_subgroupOf_eq_of_le (inf_le_right.trans hK),map_subgroupOf_eq_of_le hK]
    exact secondary_original_sylow D
  exact Chapter1.Section02.IndexTwo.isSylowIn_map hs s.action

omit [Finite G] in
/-- Normalization and the square relation survive through the same source action. -/
theorem crossing_sylow_image (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
    (image s (S c)).map (MulAut.conj (s.action t)).toMonoidHom = image s (S c) ∧
      s.action t ^ 2 ∈ image s (S c) := by
  let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
  let S₀ := (S c).subgroupOf (rootNormalizer c)
  have ht : t ∈ normalizer (S₀ : Set (rootNormalizer c)) := by
    apply mem_normalizer_iff.mpr
    intro x
    change (x : G) ∈ S c ↔ ((t : G) * (x : G) * (t : G)⁻¹) ∈ S c
    exact mem_normalizer_iff.mp c.crossing_normalizes (x : G)
  refine ⟨mem_normalizer_iff_map_conj_eq.mp
    (S₀.le_normalizer_map s.action (mem_map_of_mem s.action ht)),?_⟩
  rw [←map_pow]
  exact mem_map_of_mem s.action (show t ^ 2 ∈ S₀ from c.crossing_square)

/-- The source actor preserves S-star and its intersection with the full inner group,
but moves R₂-star. This is the same original crossing, not a selected involution. -/
theorem crossing_image_geometry (s : SecondaryActionData c n)
    {d : MSData c n} (m : RootCoordinates d) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
    (image s (S c)).map (MulAut.conj (s.action t)).toMonoidHom = image s (S c) ∧
      s.action t ^ 2 ∈ image s (S c) ∧
      (image s (S c) ⊓ componentImage s).map (MulAut.conj (s.action t)).toMonoidHom =
        image s (S c) ⊓ componentImage s ∧
      (radicalImage s).map (MulAut.conj (s.action t)).toMonoidHom ≠ radicalImage s := by
  dsimp only
  obtain ⟨hs,h2⟩ := crossing_sylow_image s D
  refine ⟨hs,h2,?_,s.crossing_moves_radical_image m hn D⟩
  apply mem_normalizer_iff_map_conj_eq.mp
  apply inf_normalizer_le_normalizer_inf
  refine ⟨mem_normalizer_iff_map_conj_eq.mpr hs,?_⟩
  rw [componentImage_eq_inner,normalizer_eq_top]
  trivial

end EndgameSieve.SecondaryActionData
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
