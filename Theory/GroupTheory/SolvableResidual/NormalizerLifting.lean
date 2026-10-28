module
public import Theory.GroupTheory.SolvableResidual.NormalSupplement
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Normalizers of perfect subgroups through solvable kernels

If the solvable kernel of a homomorphism normalizes a perfect subgroup R,
the inverse image of the normalizer of its image is exactly N(R).
The full inverse image of the subgroup is R ker(f); its solvable residual
recovers the original R. Thus no equality with the full preimage is needed.

Source application: Aschbacher--Smith 5.1.13, printed pp.636--637,
refs/quasithin.pdf, lifting normalization of the original residual.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Normalization of the image lifts to the same perfect subgroup. -/
theorem normalizer_map_comap_eq_of_perfect (f : G →* H) (R : Subgroup G)
    [Group.IsPerfect R] [Group.IsSolvable f.ker]
    (hk : f.ker ≤ normalizer (R : Set G)) :
    (normalizer (R.map f : Set H)).comap f = normalizer (R : Set G) := by
  apply le_antisymm
  · have he := map_solvableResidual_sup_eq_of_perfect_normalized R f.ker hk
    have hn := normalizer_le_normalizer_characteristic_image (R ⊔ f.ker)
      (solvableResidual (R ⊔ f.ker : Subgroup G))
    rw [he] at hn
    have hh := (R.map f).le_normalizer_comap f
    rw [comap_map_eq] at hh
    exact hh.trans hn
  · exact map_le_iff_le_comap.mp (R.le_normalizer_map f)
end Subgroup
