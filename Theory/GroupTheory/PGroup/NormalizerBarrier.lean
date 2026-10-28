module

public import Mathlib.GroupTheory.Nilpotent

/-!
# Containing p-overgroups by their normalizers

If every p-subgroup between `U` and `M` has its ambient normalizer in `M`,
then every finite p-overgroup of `U` lies in `M`. Intersect such an overgroup
`V` with `M`; the intersection is self-normalizing in `V`, hence equals `V`
by the normalizer condition for finite p-groups.

This is the elementary argument underlying Aschbacher–Smith, *The
Classification of Quasithin Groups*, combined manuscript (1 March 2004),
Lemma 2.3.2(1), p. 521.
-/

namespace Subgroup

/-- A normalizer condition on p-subgroups inside `M` also controls p-overgroups
of `U` in the ambient group. -/
public theorem p_overgroup_le_of_normalizers_le
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {U V M : Subgroup G} [Finite V]
    (hV : IsPGroup p V) (hUV : U ≤ V) (hUM : U ≤ M)
    (hnorm : ∀ W : Subgroup G, IsPGroup p W → U ≤ W → W ≤ M →
      normalizer (W : Set G) ≤ M) : V ≤ M := by
  let W := V ⊓ M
  have hWV : W ≤ V := inf_le_left
  have hWp : IsPGroup p W :=
    hV.of_injective (inclusion hWV) (inclusion_injective hWV)
  have hWM := hnorm W hWp (le_inf hUV hUM) inf_le_right
  let : Group.IsNilpotent V := hV.isNilpotent
  have hself : normalizer (W.subgroupOf V : Set V) = W.subgroupOf V := by
    apply le_antisymm _ le_normalizer
    rw [← subgroupOf_normalizer_eq hWV]
    intro x hx
    exact ⟨x.property, hWM hx⟩
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := V)) _ hself
  exact (subgroupOf_eq_top.mp htop).trans inf_le_right

end Subgroup
