module
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Odd quotients of commutators in a cubic local group

If H/O₂(H) is S₃, every subgroup of H' has two-core quotient of order
dividing three. Its image in S₃ lies in A₃ and its map kernel is a normal
two-group. The same conclusion applies to the literal commutator of two
ambient subgroups contained in H.

This supplies the odd-prime quotient in the local cubic specialization of
Stellmacher (9.3), Journal of Algebra 190 (1997), p.49, without the ambient
P-star or subnormality premises used by his general (5.2) argument.
-/

public section
namespace SymmetricThreeTwoCore
open Subgroup

/-- A subgroup of the derived group has a two-core quotient of order one or three. -/
theorem subgroup_core_quotient_card_dvd_three
    {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (K : Subgroup H) (hK : K ≤ commutator H) :
    Nat.card (K ⧸ pCore 2 K) ∣ 3 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let g := f.comp K.subtype
  have hkf : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkg : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.comp K.subtype).ker
    rw [← MonoidHom.comap_ker, hkf]
    exact pCore_isPGroup.comap_subtype
  have hcore : g.ker ≤ pCore 2 K := le_sSup ⟨inferInstance, hkg⟩
  have himage : g.range ≤ alternatingGroup (Fin 3) := by
    change (f.comp K.subtype).range ≤ _
    rw [MonoidHom.range_comp, range_subtype]
    apply (Subgroup.map_mono hK).trans
    rw [map_commutator_eq]
    exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  change (pCore 2 K).index ∣ 3
  have hd := index_dvd_of_le hcore
  rw [index_ker] at hd
  rw [← hc]
  exact hd.trans (card_dvd_of_le himage)

/-- The actual ambient commutator has a three-group quotient by its own two-core. -/
theorem ambient_commutator_core_quotient_three
    {G : Type*} [Group G] [Finite G] (P R B : Subgroup G)
    (e : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (hRP : R ≤ P) (hBP : B ≤ P) :
    IsPGroup 3 ((⁅R,B⁆ : Subgroup G) ⧸ pCore 2 (⁅R,B⁆ : Subgroup G)) := by
  let F := ⁅R,B⁆
  have hFP : F ≤ P := (commutator_le_sup R B).trans (sup_le hRP hBP)
  let K := F.subgroupOf P
  have hK : K ≤ commutator P := by
    apply (map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_subtype_commutator, show K.map P.subtype = F from
      map_subgroupOf_eq_of_le hFP]
    exact commutator_mono hRP hBP
  have hthree : IsPGroup 3 (K ⧸ pCore 2 K) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [pow_one] using subgroup_core_quotient_card_dvd_three e K hK)
  let eqv : K ≃* F := subgroupOfEquivOfLe hFP
  exact hthree.of_equiv (QuotientGroup.congr _ _ eqv (pCore_map_iso 2 eqv))

end SymmetricThreeTwoCore
