module

public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The quotient above the two-three core

The subgroup O₂,₃(G) is the inverse image of O₃(G/O₂(G)), with this
specific order of the two cores. The natural quotient is consequently
isomorphic to (G/O₂(G))/O₃(G/O₂(G)). A normal three-subgroup with two-group
quotient is the entire three-core: its quotient cannot contain a nontrivial
image of a three-group.

This identifies the normal kernels in the extension notation used in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Proposition
8.2.2(1), printed p.715 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A normal three-subgroup with two-group quotient is the three-core. -/
theorem threeCore_eq_of_twoGroup_quotient (N : Subgroup G) [N.Normal]
    (hN : IsPGroup 3 N) (hquot : IsPGroup 2 (G ⧸ N)) : N = pCore 3 G := by
  have hle : N ≤ pCore 3 G := le_sSup ⟨inferInstance, hN⟩
  apply le_antisymm hle
  have hi := (pCore_isPGroup (p := 3) (G := G)).map (QuotientGroup.mk' N)
  have ht := hquot.to_subgroup ((pCore 3 G).map (QuotientGroup.mk' N))
  have hd := hi.disjoint_of_coprime ht (by decide : Nat.Coprime 3 2)
  have hb : (pCore 3 G).map (QuotientGroup.mk' N) = ⊥ := by
    simpa only [inf_idem] using hd.eq_bot
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  change QuotientGroup.mk' N x = 1
  simpa only [hb, mem_bot] using mem_map_of_mem (QuotientGroup.mk' N) hx

/-- The literal quotient above O₂,₃(G), using the actual two-core map. -/
noncomputable def twoThreeCoreQuotientEquiv (G : Type*) [Group G] :
    G ⧸ (pCore 3 (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) ≃*
      (G ⧸ pCore 2 G) ⧸ pCore 3 (G ⧸ pCore 2 G) :=
  QuotientGroup.equivOfSurjectiveComap (QuotientGroup.mk' (pCore 2 G))
    (QuotientGroup.mk'_surjective _) _ _ rfl

/-- A marked extension of a two-group by a three-group in G/O₂(G)
identifies the quotient by O₂,₃(G), without any splitting assumption. -/
noncomputable def twoThreeCoreQuotientEquivOfExtension
    {D : Type*} [Group D] (hD : IsPGroup 2 D)
    (N : Subgroup (G ⧸ pCore 2 G)) [N.Normal] (hN : IsPGroup 3 N)
    (e : (G ⧸ pCore 2 G) ⧸ N ≃* D) :
    G ⧸ (pCore 3 (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) ≃* D := by
  have hn : N = pCore 3 (G ⧸ pCore 2 G) :=
    threeCore_eq_of_twoGroup_quotient N hN (hD.of_equiv e.symm)
  exact (twoThreeCoreQuotientEquiv G).trans
    ((QuotientGroup.quotientMulEquivOfEq hn.symm).trans e)

end Theory.GroupTheory
