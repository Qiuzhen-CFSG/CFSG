module
public import Theory.GroupTheory.CComponent.ExceptionalQuotients

/-!
# The three-prime core in a two-group extension

Let K be normal with two-group quotient. If K/O₂(K) has trivial
three-prime core, then O₃′(G)=O₂(G). The intersection with K is O₂(K),
so restricting G → G/K makes O₃′(G) an extension of two-groups.
This upgrades the component comparison to equality of ambient kernels.

Source application: Aschbacher–Smith 13.4.7, printed p.900.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.CComponentExceptionalQuotient
variable {G : Type*} [Group G] [Finite G]

/-- A two-group extension preserves the absence of odd three-prime kernels. -/
theorem primeCore_eq_twoCore_of_twoGroup_quotient
    (K : Subgroup G) [K.Normal] (hquot : IsPGroup 2 (G ⧸ K))
    (hmodel : pPrimeCore 3 (K ⧸ pCore 2 K) = ⊥) :
    pPrimeCore 3 G = pCore 2 G := by
  let N := pPrimeCore 3 G
  have hk : N.comap K.subtype = pCore 2 K :=
    core_comap K (inferInstance : K.Normal).isSubnormal hmodel
  let f : N →* (G ⧸ K) := (QuotientGroup.mk' K).comp N.subtype
  have hker : IsPGroup 2 f.ker := by
    have hle : f.ker.map N.subtype ≤ K.pCoreIn 2 := by
      rintro x ⟨y,hy,rfl⟩
      have hyK : (y : G) ∈ K := (QuotientGroup.eq_one_iff _).mp hy
      exact mem_map.mpr ⟨⟨y,hyK⟩,hk ▸ y.property,rfl⟩
    exact ((isPGroup_pCoreIn 2 K).to_le hle).of_equiv
      (f.ker.equivMapOfInjective N.subtype N.subtype_injective).symm
  have hN : IsPGroup 2 N := by
    have ht := (hquot.to_subgroup (⊤ : Subgroup (G ⧸ K))).comap_of_ker_isPGroup f hker
    simpa using ht.of_equiv Subgroup.topEquiv
  have hNP : N ≤ pCore 2 G := le_sSup ⟨inferInstance,hN⟩
  have hcop : Nat.Coprime 3 (Nat.card (pCore 2 G)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact le_antisymm hNP (le_sSup ⟨inferInstance,hcop⟩)
end Theory.GroupTheory.CComponentExceptionalQuotient
