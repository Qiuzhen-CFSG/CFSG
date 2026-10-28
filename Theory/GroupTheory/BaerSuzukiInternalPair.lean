module
public import Theory.GroupTheory.Involution.OddRotation
public import Theory.GroupTheory.BaerSuzukiLocal

/-!
# Baer–Suzuki with an internal conjugator

An involution outside the two-core inverts an element of odd prime order.
If `r` is this element and the involution lies in `V`, then `r²` belongs to
`V∨Vʳ`. Coprimality puts `r` itself in this join, which therefore is not a
two-group. Restriction to the original overgroup preserves the actual join.

This gives the internal conjugator needed in Aschbacher–Smith, Lemma
13.3.18, printed p.895, without assuming an extra dihedral quotient marking.
The Baer–Suzuki theorem is imported through the proved odd-rotation theorem.
-/

public section
namespace Subgroup
open BenderSuzuki.PFAppendixIII
variable {G : Type*} [Group G] [Finite G]

/-- For an elementary two-subgroup outside the two-core, Baer–Suzuki
supplies a non-two conjugate join containing its own conjugator. -/
theorem exists_internal_conjugate_sup_not_isPGroup
    (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hV : ¬ V ≤ pCore 2 G) :
    ∃ g : G, g ∈ V ⊔ V.map (MulAut.conj g).toMonoidHom ∧
      ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  classical
  obtain ⟨v,hv,hvc⟩ := Set.not_subset.mp hV
  have hv1 : v ≠ 1 := fun he => hvc (he ▸ (pCore 2 G).one_mem)
  have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
  have hvi : IsInvolution v := ⟨hv1,hv2⟩
  obtain ⟨q,hq,hq2,r,hr,hi⟩ :=
    BenderSuzuki.involution_outside_twoCore_inverts_odd_prime v hvi hvc
  let J := V ⊔ V.map (MulAut.conj r).toMonoidHom
  have hir : v * r⁻¹ * v = r := by
    have hh := congrArg Inv.inv hi
    simpa only [rightConjugateElem, mul_inv_rev, inv_inv, hvi.inv_eq_self, mul_assoc] using hh
  have hr2 : r ^ 2 ∈ J := by
    have he : r ^ 2 = (r * v * r⁻¹) * v := by
      calc
        r ^ 2 = r * (v * r⁻¹ * v) := by rw [hir, pow_two]
        _ = _ := by group
    rw [he]
    exact J.mul_mem (mem_sup_right (mem_map_of_mem (MulAut.conj r).toMonoidHom hv))
      (mem_sup_left hv)
  have hcop : Nat.Coprime 2 (orderOf r) := by
    rw [hr]
    exact Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun hd => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp hd).symm)
  obtain ⟨n,hn⟩ := exists_pow_eq_self_of_coprime hcop
  have hrJ : r ∈ J := hn ▸ J.pow_mem hr2 n
  refine ⟨r,hrJ,?_⟩
  intro hp
  obtain ⟨m,hm⟩ := hp.exists_pow_pow_eq_one ⟨r,hrJ⟩
  have hpow : r ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hd : q ∣ 2 ^ m := hr ▸ orderOf_dvd_of_pow_eq_one hpow
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hd))

/-- The internal-conjugator form inside the literal original overgroup. -/
theorem exists_internal_conjugate_sup_not_isPGroup_in
    (H V : Subgroup G) [IsElementaryAbelian 2 V]
    (hVH : V ≤ H) (hcore : ¬ V ≤ H.pCoreIn 2) :
    ∃ g ∈ H, g ∈ V ⊔ V.map (MulAut.conj g).toMonoidHom ∧
      ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let W := V.subgroupOf H
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  have hW : W.map H.subtype = V := map_subgroupOf_eq_of_le hVH
  have hn : ¬ W ≤ pCore 2 H := by
    intro h
    exact hcore (hW ▸ map_mono (f := H.subtype) h)
  obtain ⟨g,hg,hp⟩ := exists_internal_conjugate_sup_not_isPGroup W hn
  have hconj : (W.map (MulAut.conj g).toMonoidHom).map H.subtype =
      V.map (MulAut.conj (g : G)).toMonoidHom := by
    have hf : H.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp H.subtype := by ext x; rfl
    rw [map_map, hf, ← map_map, hW]
  have hmap : (W ⊔ W.map (MulAut.conj g).toMonoidHom).map H.subtype =
      V ⊔ V.map (MulAut.conj (g : G)).toMonoidHom := by rw [map_sup,hW,hconj]
  refine ⟨g,g.property, hmap ▸ mem_map_of_mem H.subtype hg, ?_⟩
  intro hpair
  have hi := (hmap.symm ▸ hpair).comap_of_injective H.subtype H.subtype_injective
  rw [comap_map_eq_self_of_injective H.subtype_injective] at hi
  exact hp hi

end Subgroup
