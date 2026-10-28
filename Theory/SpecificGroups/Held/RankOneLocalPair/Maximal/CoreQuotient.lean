module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Transport
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# A normal PSL₃(2) section in the intrinsic two-core quotient

If a normal subgroup N of G has N/O₂(N) isomorphic to the actual matrix
PSL₃(2), and G/N is a two-group, its image J in G/O₂(G) supplies the desired
normal section. The existing core-intersection theorem identifies J with
N/O₂(N). The quotient by J is a surjective image of G/N.

This handles both the inner Held local and its possible outer extension in
Aschbacher–Smith E.1.14(4), printed p.214. The concrete matrix equivalence
is a separate input; an ATLAS shape or an order does not supply it.
-/

@[expose] public section

namespace Held.RankOneLocalPair
open Subgroup

/-- The normal subgroup is the literal image in the ambient core quotient, with both quotient maps retained. -/
theorem hasPSL3TwoCoreQuotient_of_normal {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal]
    (e : N ⧸ pCore 2 N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hQ : IsPGroup 2 (G ⧸ N)) : HasPSL3TwoCoreQuotient G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let J := N.map q
  have hJ : J.Normal := inferInstance
  let := hJ
  refine ⟨J, hJ, ⟨(N.coreQuotientEquivImage 2).symm.trans e⟩, ?_⟩
  let f : G →* (G ⧸ pCore 2 G) ⧸ J := (QuotientGroup.mk' J).comp q
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective J).comp (QuotientGroup.mk'_surjective _)
  have hker : N ≤ f.ker := by
    intro n hn
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_map_of_mem q hn)
  exact hQ.of_surjective (QuotientGroup.lift N f hker)
    (QuotientGroup.lift_surjective_of_surjective N f hf hker)

/-- A matrix equivalence of the entire core quotient gives the required normal section. -/
theorem hasPSL3TwoCoreQuotient_of_equiv {G : Type*} [Group G]
    (e : G ⧸ pCore 2 G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    HasPSL3TwoCoreQuotient G := by
  refine ⟨⊤, inferInstance, ⟨Subgroup.topEquiv.trans e⟩, ?_⟩
  intro x
  refine ⟨0, ?_⟩
  simp only [pow_zero, pow_one]
  induction x using QuotientGroup.induction_on with
  | H x => exact (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_top x)

end Held.RankOneLocalPair
