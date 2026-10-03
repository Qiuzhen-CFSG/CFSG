module

public import Stellmacher.ElementaryAbelianMaxJ

/-!
# Closing a normalizer tower using the elementary Thompson subgroup

Let `P` satisfy the normalizer condition, as finite nilpotent groups do.
If the elementary Thompson subgroup of `N_P(S)` is `S`, then `N_P(S) = P`.
Indeed, automorphism transport of the Thompson subgroup shows that the
normalizer of `N_P(S)` in `P` already normalizes `S`. Thus `N_P(S)` is
self-normalizing in `P`, so the normalizer condition forces equality.

This isolates the last step in Stellmacher Section 11, case (II), from the
finite-group calculation establishing the Thompson equality. It does not
assume that equality follows just from the order of `S` or its normalizer.
Source: `refs/latex/stellmacher-n-group.tex`, lines 2092–2095.
-/

namespace Stellmacher

/-- A normalizer whose elementary Thompson subgroup is the original subgroup
fills any overgroup satisfying the normalizer condition. -/
public theorem inf_normalizer_eq_of_thompson_eq
    {G : Type*} [Group G] (P S : Subgroup G)
    (hP : NormalizerCondition P)
    (hJ : elementaryAbelianMaxJ
      (P ⊓ Subgroup.normalizer (S : Set G)) = S) :
    P ⊓ Subgroup.normalizer (S : Set G) = P := by
  let N := P ⊓ Subgroup.normalizer (S : Set G)
  have hNP : N ≤ P := inf_le_left
  have hNS : Subgroup.normalizer (N : Set G) ≤
      Subgroup.normalizer (S : Set G) := by
    intro element helement
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at helement ⊢
    change N.map (MulAut.conj element).toMonoidHom = N at helement
    change S.map (MulAut.conj element).toMonoidHom = S
    rw [← hJ, ← elementaryAbelianMaxJ_map_equiv, helement]
  have hself : Subgroup.normalizer (N.subgroupOf P : Set P) = N.subgroupOf P := by
    apply le_antisymm
    · rw [← Subgroup.subgroupOf_normalizer_eq hNP]
      intro element helement
      exact ⟨element.property, hNS helement⟩
    · exact Subgroup.le_normalizer
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
    hP (N.subgroupOf P) hself
  exact le_antisymm hNP (Subgroup.subgroupOf_eq_top.mp htop)

end Stellmacher
