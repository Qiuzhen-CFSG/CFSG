module

public import Theory.PGroupCore

/-!
# Lifting the p-core through a homomorphism with p-group kernel

For a surjective homomorphism with p-group kernel, the preimage of the
quotient p-core is the original p-core. Its order is the product of the
kernel order and quotient p-core order. The proof uses closure of p-groups
under extensions and the maximality of the p-core among normal p-subgroups.

This is the standard p-core lifting argument; it applies in particular to
the normalizer action of a centric subgroup in characteristic p.
-/

namespace MonoidHom

/-- A surjection with p-group kernel lifts the target p-core exactly. -/
public theorem comap_pCore_of_ker_isPGroup
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) :
    (pCore p H).comap f = pCore p G := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_ker_isPGroup f hker⟩
  · apply Subgroup.map_le_iff_le_comap.mp
    have hn : ((pCore p G).map f).Normal := Subgroup.Normal.map inferInstance f hf
    exact le_sSup ⟨hn, pCore_isPGroup.map f⟩

/-- Kernel-image counting for the lifted p-core. -/
public theorem card_pCore_of_ker_isPGroup
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) :
    Nat.card (pCore p G) = Nat.card f.ker * Nat.card (pCore p H) := by
  have hpre := f.comap_pCore_of_ker_isPGroup hf hker
  have hkerle : f.ker ≤ pCore p G := le_sSup ⟨inferInstance, hker⟩
  have hmap : (pCore p G).map f = pCore p H := by
    rw [← hpre, Subgroup.map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  have hcount := (f.ker.subgroupOf (pCore p G)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv] at hcount
  change Nat.card f.ker * f.ker.relIndex (pCore p G) = _ at hcount
  rw [Subgroup.relIndex_ker, hmap] at hcount
  exact hcount.symm

end MonoidHom
