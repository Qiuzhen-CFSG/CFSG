module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.KernelResidual

/-!
# Two-subgroups in the marked cyclic source core

The local generation witness has an odd prime-power kernel of index two.
Coprimality therefore makes every two-subgroup have order at most two.
The relative version applies to intersections with the actual starred core,
without imposing an order bound on the ambient action group.

Source: Aschbacher--Smith 15.1.13(4), printed p.1091, singleton cases.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem LocalGeneration.two_subgroup_card_le_two (l : LocalGeneration ρ)
    (A : Subgroup G) (hA : IsPGroup 2 A) : Nat.card A ≤ 2 := by
  let : Fact l.prime.Prime := ⟨l.prime_prime⟩
  obtain ⟨n,hn⟩ := hA.exists_card_eq
  obtain ⟨k,hk⟩ := l.pgroup.exists_card_eq
  have hd : Nat.card A ∣ Nat.card l.kernel * 2 := by
    rw [←l.kernel_index_two,l.kernel.card_mul_index]
    exact card_subgroup_dvd_card A
  have hcop : Nat.Coprime (Nat.card A) (Nat.card l.kernel) := by
    rw [hn,hk]
    exact l.prime_odd.coprime_two_left.pow n k
  exact Nat.le_of_dvd (by decide) (hcop.dvd_of_dvd_mul_left hd)

theorem LocalGeneration.two_subgroup_inf_card_le_two
    (K : Subgroup G) (l : LocalGeneration (ρ.comp K.subtype))
    (A : Subgroup G) (hA : IsPGroup 2 A) : Nat.card (A ⊓ K : Subgroup G) ≤ 2 := by
  let e := subgroupOfEquivOfLe (show A ⊓ K ≤ K from inf_le_right)
  have hp : IsPGroup 2 ((A ⊓ K).subgroupOf K) := hA.to_inf_left.of_equiv e.symm
  have hb := l.two_subgroup_card_le_two _ hp
  rwa [Nat.card_congr e.toEquiv] at hb
end CFSG.Quasithin.ChapterD.CyclicSource
