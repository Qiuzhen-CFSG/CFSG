module

public import Theory.PPrimeCore
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Centralizers of normal Sylow subgroups modulo the prime-complement core

For a normal Sylow p-subgroup S, the p'-core centralizes S, and
S C_G(S) = S O_{p'}(G). The intersection of S with its normal centralizer
is a central Sylow subgroup of that centralizer. Burnside transfer splits
off a normal p-complement there. Its elements lie in the characteristic
p'-core of the centralizer, which maps into the ambient p'-core.

This is the elementary centralizer reduction used in Lyons, *A
Characterization of the Group U₃(4)* (1972), Lemma 1(c), pp. 372–373.
-/

namespace Sylow
open Subgroup

public theorem pPrimeCore_le_centralizer_of_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) [(S : Subgroup G).Normal] :
    pPrimeCore p G ≤ centralizer (S : Set G) := by
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  have hc : (Nat.card (pPrimeCore p G)).Coprime (Nat.card S) := by
    rw [hn]
    exact (pPrimeCore_coprime_card (p := p)).symm.pow_right n
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_disjoint (disjoint_of_coprime_natCard hc))

public theorem centralizer_le_sup_pPrimeCore_of_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) [(S : Subgroup G).Normal] :
    centralizer (S : Set G) ≤ (S : Subgroup G) ⊔ pPrimeCore p G := by
  let C := centralizer (S : Set G)
  let : C.Normal := normal_centralizer
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal C
  have hTC : normalizer (T : Set C) ≤ centralizer (T : Set C) := by
    intro c _
    rw [mem_centralizer_iff]
    intro t ht
    apply Subtype.ext
    have htS : (t : G) ∈ (S : Subgroup G) := by
      change t ∈ (S : Subgroup G).subgroupOf C
      rwa [← hT]
    exact mem_centralizer_iff.mp c.property t htS
  let f := MonoidHom.transferSylow T hTC
  have hk : f.ker ≤ pPrimeCore p C := le_sSup ⟨inferInstance,
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (MonoidHom.not_dvd_card_ker_transferSylow T hTC)⟩
  have hcore : (pPrimeCore p C).map C.subtype ≤ pPrimeCore p G :=
    le_sSup ⟨inferInstance, Nat.Coprime.of_dvd_right
      (card_map_dvd _ C.subtype) pPrimeCore_coprime_card⟩
  intro c hc
  have hgen := (MonoidHom.ker_transferSylow_isComplement' T hTC).sup_eq_top
  have hmem : (⟨c, hc⟩ : C) ∈ f.ker ⊔ (T : Subgroup C) := by rw [hgen]; trivial
  obtain ⟨k, hk', t, ht, hkt⟩ := mem_sup_of_normal_left.mp hmem
  have hkG : (k : G) ∈ pPrimeCore p G :=
    hcore (mem_map_of_mem C.subtype (hk hk'))
  have htG : (t : G) ∈ (S : Subgroup G) := by
    change t ∈ (S : Subgroup G).subgroupOf C
    rwa [← hT]
  have hv := congrArg Subtype.val hkt
  change (k : G) * (t : G) = c at hv
  rw [← hv]
  exact ((S : Subgroup G) ⊔ pPrimeCore p G).mul_mem
    ((le_sup_right : pPrimeCore p G ≤ (S : Subgroup G) ⊔ pPrimeCore p G) hkG)
    ((le_sup_left : (S : Subgroup G) ≤ (S : Subgroup G) ⊔ pPrimeCore p G) htG)

public theorem sup_centralizer_eq_sup_pPrimeCore_of_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) [(S : Subgroup G).Normal] :
    (S : Subgroup G) ⊔ centralizer (S : Set G) =
      (S : Subgroup G) ⊔ pPrimeCore p G := by
  exact le_antisymm (sup_le le_sup_left S.centralizer_le_sup_pPrimeCore_of_normal)
    (sup_le_sup_left S.pPrimeCore_le_centralizer_of_normal _)

end Sylow
