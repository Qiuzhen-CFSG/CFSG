module

public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Perfect normal subgroups supplemented by two-groups

In a finite group, every subgroup containing the solvable residual has the
same embedded solvable residual. If a perfect normal subgroup is supplemented
by a two-subgroup, it is both the solvable residual and the two-residual.
These statements distinguish the two-residual from the two-core.

The centralizer application uses the subgroup C^∞T rather than all of C;
an odd abelian quotient of C need not be absorbed by T.
Source: standard residual calculus, as used in Aschbacher--Smith,
E.1.2(E2), printed p.210.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Restricting to a subgroup containing the residual does not change its image. -/
theorem map_solvableResidual_eq_of_residual_le (H : Subgroup G) (hH : solvableResidual G ≤ H) :
    (solvableResidual H).map H.subtype = solvableResidual G :=
  le_antisymm (map_solvableResidual_le H.subtype)
    (le_map_solvableResidual_of_isPerfect _ H hH)

/-- A perfect normal subgroup with a two-subgroup supplement is both residuals. -/
theorem residuals_of_perfect_normal_sup_twoGroup (D P : Subgroup G) [D.Normal] [Group.IsPerfect D]
    (hP : IsPGroup 2 P) (hgen : D ⊔ P = ⊤) :
    pResidual 2 G = D ∧ solvableResidual G = D := by
  have hq := isPGroup_quotient_of_sup_eq_top D P hP hgen
  let : Group.IsNilpotent (G ⧸ D) := hq.isNilpotent
  have hs : solvableResidual G = D := le_antisymm
    (solvableResidual_le_of_solvable_quotient D) (le_solvableResidual_of_isPerfect D)
  refine ⟨le_antisymm (sInf_le ⟨inferInstance, hq⟩) ?_, hs⟩
  rw [← hs]
  apply le_sInf
  rintro N ⟨hn, hN⟩
  let := hn
  let : Group.IsNilpotent (G ⧸ N) := hN.isNilpotent
  exact solvableResidual_le_of_solvable_quotient N

/-- The two-residual and solvable residual agree in a normalized perfect supplement. -/
theorem pResidual_eq_solvableResidual_of_perfect_sup_twoGroup (D P : Subgroup G) [Group.IsPerfect D]
    (hP : IsPGroup 2 P) (hn : P ≤ normalizer (D : Set G)) :
    pResidual 2 (D ⊔ P : Subgroup G) = solvableResidual (D ⊔ P : Subgroup G) := by
  let K := D ⊔ P
  let N := D.subgroupOf K
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hn)
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show D ≤ K from le_sup_left)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (show D ≤ K from le_sup_left)).symm.surjective
  have hsup : N ⊔ P.subgroupOf K = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show D ≤ K from le_sup_left),
      map_subgroupOf_eq_of_le (show P ≤ K from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨hp, hs⟩ := residuals_of_perfect_normal_sup_twoGroup N (P.subgroupOf K) hP.comap_subtype hsup
  exact hp.trans hs.symm

/-- Normal subgroups with solvable quotient contain the full residual, and their
own residual is the same embedded subgroup. -/
theorem map_solvableResidual_eq_of_solvable_quotient (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)] :
    (solvableResidual N).map N.subtype = solvableResidual G :=
  map_solvableResidual_eq_of_residual_le N (solvableResidual_le_of_solvable_quotient N)

/-- The equality of embedded residuals gives their actual inclusion equivalence. -/
noncomputable def solvableResidualEquivOfSolvableQuotient (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)] : solvableResidual N ≃* solvableResidual G :=
  ((solvableResidual N).equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_solvableResidual_eq_of_solvable_quotient N))

end Subgroup
