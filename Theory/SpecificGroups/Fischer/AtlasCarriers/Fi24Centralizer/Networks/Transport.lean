module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Words
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Networks.Comparison
/-!
# Intertwining the certified networks with the original Fi24 carrier

Multiplication, inverse and power preserve the original source action on the
embedded letters. Since the letter inclusion is injective, a network identity
therefore proves the corresponding relation in the actual ATLAS subgroup.
-/
public section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection.Networks

@[expose] def Intertwines (g : Carrier) (p : Equiv.Perm (Fin 524288)) : Prop :=
  ∀ i : Fin 306936,
    Fin.castLE (by decide) (inclusion g i) = p (Fin.castLE (by decide) i)

theorem Intertwines.one : Intertwines 1 1 := by intro i; rfl

theorem Intertwines.mul {g h : Carrier} {p q : Equiv.Perm (Fin 524288)}
    (hg : Intertwines g p) (hh : Intertwines h q) : Intertwines (g*h) (p*q) := by
  intro i
  change Fin.castLE (by decide) (inclusion g (inclusion h i)) =
    p (q (Fin.castLE (by decide) i))
  rw [hg, hh]

theorem Intertwines.inv {g : Carrier} {p : Equiv.Perm (Fin 524288)}
    (hg : Intertwines g p) : Intertwines g⁻¹ p⁻¹ := by
  intro i
  apply p.injective
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have H := hg ((inclusion g)⁻¹ i)
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at H
  simpa only [map_inv] using H.symm

theorem Intertwines.pow {g : Carrier} {p : Equiv.Perm (Fin 524288)}
    (hg : Intertwines g p) (n : Nat) : Intertwines (g^n) (p^n) := by
  induction n with
  | zero => simpa using Intertwines.one
  | succ n ih => simpa only [pow_succ] using ih.mul hg

theorem Intertwines.eq_one {g : Carrier} {p : Equiv.Perm (Fin 524288)}
    (hg : Intertwines g p) (hp : p=1) : g=1 := by
  apply inclusion_injective
  apply Equiv.ext
  intro i
  apply Fin.castLE_injective (by decide : 306936≤524288)
  simpa only [hp, Equiv.Perm.one_apply, map_one] using hg i

theorem a_intertwines : Intertwines a permA := by
  intro i
  exact (permA_source i).symm

theorem b_intertwines : Intertwines b permB := by
  intro i
  exact (permB_source i).symm
end Sporadic.Fischer.Fi24Prime.CentralizerSection.Networks
