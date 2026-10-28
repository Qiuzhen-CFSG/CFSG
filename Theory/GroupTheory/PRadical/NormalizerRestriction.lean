module
public import Theory.GroupTheory.PRadical.NormalComponentImages

/-!
# Radicality inside a normalizer-invariant overgroup

If R is p-radical and N(R) normalizes an overgroup L of R, then R remains
p-radical inside L. The intrinsic normalizer core in L is invariant under
N(R), so radical saturation puts it in R; the reverse inclusion is automatic.
No normality of L in the whole ambient group is needed.

Source: the normalizer saturation argument in Aschbacher (1981), 8.2(4),
used for the parabolic rank-one reductions in Aschbacher–Smith C.2.7.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem IsPRadical.normalizer_core_subgroupOf
    {R : Subgroup G} (hR : R.IsPRadical p) (L : Subgroup G) (hRL : R ≤ L)
    (hn : normalizer (R : Set G) ≤ normalizer (L : Set G)) :
    (normalizer (R.subgroupOf L : Set L)).pCoreIn p = R.subgroupOf L := by
  let Y := L ⊓ normalizer (R : Set G)
  have hNY : normalizer (R : Set G) ≤ normalizer (Y : Set G) :=
    (le_inf hn (normalizer (R : Set G)).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hYR : Y.pCoreIn p ≤ R :=
    le_of_normalizer_le_normalizer_of_pCore_normalizer_le R _ hR.isPGroup
      (isPGroup_pCoreIn p Y) hR.2.le
      (hNY.trans (normalizer_le_normalizer_characteristic_image Y (pCore p Y)))
  have he : Y.pCoreIn p = R := le_antisymm hYR
    (le_pCoreIn_of_normalizes hR.isPGroup (le_inf hRL R.le_normalizer) inf_le_right)
  apply map_injective L.subtype_injective
  rw [map_pCoreIn_of_injective p _ _ L.subtype_injective,
    ←subgroupOf_normalizer_eq hRL,subgroupOf_map_subtype,inf_comm,
    he,map_subgroupOf_eq_of_le hRL]

theorem IsPRadical.subgroupOf_of_normalizer_normalizes
    {R : Subgroup G} (hR : R.IsPRadical p) (L : Subgroup G) (hRL : R ≤ L)
    (hn : normalizer (R : Set G) ≤ normalizer (L : Set G)) :
    (R.subgroupOf L).IsPRadical p := by
  refine ⟨?_,hR.normalizer_core_subgroupOf L hRL hn⟩
  intro he
  have hh := congrArg (map L.subtype) he
  rw [map_subgroupOf_eq_of_le hRL,map_bot] at hh
  exact hR.1 hh
end Subgroup
