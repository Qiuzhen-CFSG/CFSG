module
public import Theory.GroupTheory.PerfectSylowPreservingAction
public import Theory.GroupTheory.SolvableNormalizerExtension
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# A solvable supplement containing the Sylow two-subgroup

Intersect the given Sylow subgroup with the solvable residual. Its
normalizer is solvable, since the intrinsic Sylow normalizer and the
residual quotient are solvable. Frattini's argument makes this normalizer
a supplement to the residual. Thus an escaping Sylow overgroup has an
escaping residual whenever all solvable Sylow overgroups are contained
in the prescribed subgroup.

Source: the opening of Aschbacher--Smith 10.3.3, printed p.756.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem exists_solvable_sylow_supplement (S : Sylow 2 G) :
    ∃ N : Subgroup G, Group.IsSolvable N ∧ (S : Subgroup G) ≤ N ∧
      N ⊔ solvableResidual G = ⊤ := by
  let R := solvableResidual G
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal R
  let N := normalizer ((P : Subgroup R).map R.subtype : Set G)
  let : Group.IsSolvable (normalizer (P : Set R)) := P.normalizer_isSolvable_two
  refine ⟨N, normalizer_map_subtype_isSolvable R (P : Subgroup R), ?_,
    P.normalizer_sup_eq_top⟩
  change (S : Subgroup G) ≤ normalizer ((P : Subgroup R).map R.subtype : Set G)
  rw [hP, subgroupOf_map_subtype]
  apply le_normalizer_iff.mpr
  intro s hs x hx
  exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hx.1)
    ((S : Subgroup G).inv_mem hs), (inferInstance : R.Normal).conj_mem x hx.2 s⟩

end Theory.GroupTheory
