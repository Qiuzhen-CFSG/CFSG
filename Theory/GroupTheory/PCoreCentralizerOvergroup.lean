module

public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.PCoreImage

/-!
# Detecting characteristic p inside a core-centralizer overgroup

If a subgroup N has characteristic p and contains C_G(O_p(G)), then G
has characteristic p. The latter centralizer is normal in N, so inherits
characteristic p. Its own p-core lies in O_p(G) and is therefore central
in the centralizer. Thus the centralizer is a p-group.

This criterion supplies the local-overgroup step in Aschbacher–Smith
2.3.9(7), printed p.526. It uses intrinsic cores and relative normality.
-/

namespace Subgroup

/-- A characteristic-p overgroup of the core centralizer detects
characteristic p in the whole finite group. -/
public theorem centralizer_pCore_le_of_overgroup
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (N : Subgroup G)
    (hN : centralizer (pCore p N : Set N) ≤ pCore p N)
    (hCN : centralizer (pCore p G : Set G) ≤ N) :
    centralizer (pCore p G : Set G) ≤ pCore p G := by
  let C := centralizer (pCore p G : Set G)
  have hC : centralizer (pCore p C : Set C) ≤ pCore p C := by
    have ht := normal_core_selfCentralizing hN (C.subgroupOf N)
    exact (Theory.Quasithin.centralizer_pCore_le_iff p (subgroupOfEquivOfLe hCN)).mp ht
  have hcore : C.pCoreIn p ≤ pCore p G :=
    le_sSup ⟨by change ((pCore p C).map C.subtype).Normal; infer_instance,
      isPGroup_pCoreIn p C⟩
  have htop : centralizer (pCore p C : Set C) = ⊤ := by
    apply top_unique
    intro x _ y hy
    apply Subtype.ext
    exact mem_centralizer_iff.mp x.property (y : G)
      (hcore (mem_map.mpr ⟨y, hy, rfl⟩))
  intro x hx
  apply hcore
  refine mem_map.mpr ⟨⟨x, hx⟩, hC ?_, rfl⟩
  rw [htop]
  trivial

end Subgroup
