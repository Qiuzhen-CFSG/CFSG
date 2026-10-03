module

public import Stellmacher.MainDefs

/-!
# Overgroups of the two-core inherit characteristic two

If `C_G(O₂(G)) ≤ O₂(G)`, then every subgroup containing `O₂(G)` has
characteristic two. Finiteness, solvability and normality of that overgroup
are unnecessary. The companion theorem treats `K ≤ L` in an ambient group
and returns characteristic two of the literal subgroup `K` when it contains
the ambient image of `O₂(L)`.

Restricting the ambient two-core to the overgroup preserves normality and
its two-group property, so this restriction lies in the overgroup's own
two-core. An element centralizing that larger two-core centralizes the
ambient two-core. The ambient characteristic-two hypothesis therefore places
it in the restricted two-core, which proves the desired containment.
The nested-subgroup companion transports this containment through the
canonical subgroup equivalence; a private isomorphism argument uses the
existing invariance of the two-core.

This source-neutral inheritance fact supplies the characteristic-two
hypothesis for the selected local factor in Stellmacher's (6.1). It uses
the established `IsCharacteristicTwoType` definition from `MainDefs`.
-/

namespace Stellmacher

public theorem characteristicTwo_of_contains_core
    {G : Type*} [Group G]
    (hchar : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (K : Subgroup G) (hcore : pCore 2 G ≤ K) :
    IsCharacteristicTwoType K := by
  let Q := (pCore 2 G).subgroupOf K
  have hQnormal : Q.Normal := inferInstance
  have hQtwo : IsPGroup 2 Q :=
    (pCore_isPGroup (p := 2) (G := G)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hcore).symm
  have hQcore : Q ≤ pCore 2 K := le_sSup ⟨hQnormal, hQtwo⟩
  intro k hk
  apply hQcore
  change (k : G) ∈ pCore 2 G
  apply hchar
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqK : (⟨q, hcore hq⟩ : K) ∈ pCore 2 K := hQcore hq
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp hk (⟨q, hcore hq⟩ : K) hqK)

private theorem characteristicTwo_transport
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hchar : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    Subgroup.centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have hcore := pCore_map_iso 2 e
  intro h hh
  obtain ⟨g, rfl⟩ := e.surjective h
  rw [← hcore]
  apply Subgroup.mem_map_of_mem
  apply hchar
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply e.injective
  have hyH : e y ∈ pCore 2 H := by
    rw [← hcore]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp hh (e y) hyH

public theorem characteristicTwo_of_contains_core_in
    {G : Type*} [Group G] (L K : Subgroup G)
    (hchar : IsCharacteristicTwoType L) (hKL : K ≤ L)
    (hcore : (pCore 2 L).map L.subtype ≤ K) : IsCharacteristicTwoType K := by
  have hcoreI : pCore 2 L ≤ K.subgroupOf L := by
    intro l hl
    exact hcore (Subgroup.mem_map_of_mem L.subtype hl)
  have hcharI : IsCharacteristicTwoType (K.subgroupOf L) :=
    characteristicTwo_of_contains_core hchar (K.subgroupOf L) hcoreI
  exact characteristicTwo_transport (Subgroup.subgroupOfEquivOfLe hKL) hcharI

end Stellmacher
