module

public import Theory.GroupTheory.PRadical
public import Mathlib.Order.Atoms

/-!
# Maximal subgroups with nontrivial p-core

In a group with trivial p-core, a maximal subgroup M with nontrivial
O_p(M) is the full normalizer of that core's ambient image. Indeed, M
normalizes the image, and a larger normalizer would make it a nontrivial
normal p-subgroup of the ambient group. The image is consequently p-radical.

This separates the normalizer calculation from the exclusion of maximal
subgroups with trivial p-core in Sylow-overgroup arguments. Source application:
Aschbacher--Smith, *The Classification of Quasithin Groups*, printed p.511,
using the Sylow-overgroup analysis cited there as [Asc86b].
-/

namespace Subgroup

variable {G : Type*} [Group G] {p : ℕ}

/-- A maximal subgroup with nontrivial intrinsic p-core is its full ambient
normalizer when the ambient p-core is trivial. -/
public theorem normalizer_map_pCore_eq_of_isCoatom
    (M : Subgroup G) (hM : IsCoatom M) (hG : pCore p G = ⊥)
    (hcore : pCore p M ≠ ⊥) :
    normalizer ((pCore p M).map M.subtype : Set G) = M := by
  let U := (pCore p M).map M.subtype
  have hU : U ≠ ⊥ := fun h =>
    hcore (((pCore p M).map_eq_bot_iff_of_injective M.subtype_injective).mp h)
  have hMN : M ≤ normalizer (U : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore p M).le_normalizer_map M.subtype
  rcases hM.le_iff.mp hMN with htop | heq
  · have hnormal : U.Normal := normalizer_eq_top_iff.mp htop
    have hle : U ≤ pCore p G := le_sSup ⟨hnormal, pCore_isPGroup.map M.subtype⟩
    exact (hU (bot_unique (hle.trans_eq hG))).elim
  · exact heq

/-- The ambient core image in the preceding normalizer calculation is a
nontrivial p-radical subgroup. -/
public theorem isPRadical_map_pCore_of_isCoatom
    (M : Subgroup G) (hM : IsCoatom M) (hG : pCore p G = ⊥)
    (hcore : pCore p M ≠ ⊥) :
    IsPRadical p ((pCore p M).map M.subtype) := by
  refine ⟨fun h => hcore
    (((pCore p M).map_eq_bot_iff_of_injective M.subtype_injective).mp h), ?_⟩
  rw [normalizer_map_pCore_eq_of_isCoatom M hM hG hcore]

end Subgroup
