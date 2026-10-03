module

public import Theory.GroupTheory.PGroup.CriticalSubgroup

/-!
# Critical subgroups over a prescribed maximal characteristic abelian subgroup

Thompson's construction can start with any maximal characteristic abelian
subgroup, rather than choosing a new one. Intersect its centralizer with the
inverse image of the central omega subgroup of the quotient. The resulting
critical subgroup has precisely the prescribed subgroup as its center.

This retains the center identification in the proof of `exists_criticalPSubgroup`.
Source: Gorenstein, *Finite Groups*, Theorem 5.3.11, pp.185–186.
-/

open Subgroup
open scoped commutatorElement

namespace IsPGroup

/-- A prescribed maximal characteristic abelian subgroup is the center of
some characteristic critical subgroup. -/
public theorem exists_criticalPSubgroup_with_center
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (D : Subgroup P) [D.Characteristic] [IsMulCommutative D]
    (hmax : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A →
      D ≤ A → A = D) :
    ∃ C : Subgroup P, IsCriticalPSubgroup p C ∧ (center C).map C.subtype = D := by
  classical
  let q : P →* (P ⧸ D) := QuotientGroup.mk' D
  let W : Subgroup (center (P ⧸ D)) := omega₁ (center (P ⧸ D)) (p := p)
  let : W.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian p W := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let V : Subgroup (P ⧸ D) := W.map (center (P ⧸ D)).subtype
  let : V.Characteristic := inferInstance
  let : IsElementaryAbelian p V := IsElementaryAbelian.map_subtype
  let K : Subgroup P := V.comap q
  let : K.Characteristic := Characteristic.comap_quotient_mk inferInstance
  let C : Subgroup P := centralizer (D : Set P) ⊓ K
  let : C.Characteristic := inferInstance
  have hDC : D ≤ C := by
    intro d hd
    refine ⟨le_centralizer D hd, ?_⟩
    change q d ∈ V
    have hqd : q d = 1 := (QuotientGroup.eq_one_iff (N := D) d).mpr hd
    rw [hqd]
    exact V.one_mem
  have hDZ : D ≤ (center C).map C.subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    exact le_inf hDC (le_centralizer_iff.mp inf_le_left)
  have hZD : (center C).map C.subtype = D :=
    le_antisymm ((hmax _ inferInstance inferInstance hDZ).le) hDZ
  have hcomm : ⁅(⊤ : Subgroup P), C⁆ ≤ D := by
    apply commutator_le.mpr
    intro g _ c hc
    apply (QuotientGroup.eq_one_iff (N := D) _).mp
    change q ⁅g, c⁆ = 1
    rw [map_commutatorElement]
    have hqc : q c ∈ center (P ⧸ D) := map_subtype_le W hc.2
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hqc (q g))
  have hpow (c : C) : (c : P) ^ p ∈ D := by
    apply (QuotientGroup.eq_one_iff (N := D) _).mp
    change q ((c : P) ^ p) = 1
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (A := V) (q c) c.property.2
  have hcentralizer : centralizer (C : Set P) = D := by
    apply le_antisymm ?_ (le_centralizer_iff.mp inf_le_left)
    let Q : Subgroup P := centralizer (C : Set P)
    let Qbar : Subgroup (P ⧸ D) := Q.map q
    let : Qbar.Normal := QuotientGroup.map_normal D Q
    let : Fact (IsPGroup p (P ⧸ D)) := ⟨hP.to_quotient D⟩
    by_contra hnot
    have hnontrivial : Nontrivial Qbar := by
      obtain ⟨x, hxQ, hxD⟩ := SetLike.not_le_iff_exists.mp hnot
      have hxbar : q x ∈ Qbar := mem_map_of_mem q hxQ
      have hxne : q x ≠ 1 := fun h => hxD ((QuotientGroup.eq_one_iff (N := D) x).mp h)
      exact ⟨⟨⟨q x, hxbar⟩, 1, fun h => hxne (congrArg Subtype.val h)⟩⟩
    obtain ⟨T, _, hTQ, hTcard, hTcenter⟩ :=
      exists_central_subgroup_card_eq_prime_in_normal (p := p) Qbar hnontrivial
    have hTnontrivial : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp
      (hTcard ▸ (Fact.out : p.Prime).one_lt)
    obtain ⟨t, ht⟩ : ∃ t : T, t ≠ 1 := exists_ne 1
    obtain ⟨x, hxQ, hxt⟩ := hTQ t.property
    have hxV : q x ∈ V := by
      have hz : q x ∈ center (P ⧸ D) := hxt.symm ▸ hTcenter t.property
      refine ⟨⟨q x, hz⟩, ?_, rfl⟩
      apply subset_closure
      change (⟨q x, hz⟩ : center (P ⧸ D)) ^ (p ^ 1) = 1
      apply Subtype.ext
      have hp := congrArg Subtype.val (pow_card_eq_one' (x := t))
      change (q x) ^ (p ^ 1) = 1
      change (t : P ⧸ D) ^ Nat.card T = 1 at hp
      simpa only [pow_one, hTcard, hxt] using hp
    have hxC : x ∈ C := ⟨centralizer_le hDC hxQ, hxV⟩
    have hxD : x ∈ D := by
      rw [← hZD, map_center_subtype_eq_inf_centralizer]
      exact ⟨hxC, hxQ⟩
    apply ht
    apply Subtype.ext
    exact hxt.symm.trans ((QuotientGroup.eq_one_iff (N := D) x).mpr hxD)
  refine ⟨C, ?_, hZD⟩
  refine ⟨inferInstance, ?_, hZD.symm ▸ hcomm, hcentralizer.trans hZD.symm⟩
  have hquotpow : ∀ x : C ⧸ center C, x ^ p = 1 := by
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (center C) x
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (N := center C) (c ^ p)).mpr
    have hh : ((c ^ p : C) : P) ∈ (center C).map C.subtype := hZD.symm ▸ hpow c
    obtain ⟨z, hz, heq⟩ := hh
    exact (Subtype.ext heq : z = c ^ p) ▸ hz
  refine { toIsMulCommutative := ?_, exponent_dvd_p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hquotpow }
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (center C) x
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (center C) y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff (N := center C) ⁅c, d⁆).mpr
  have hh : ((⁅c, d⁆ : C) : P) ∈ (center C).map C.subtype :=
    hZD.symm ▸ hcomm (commutator_mem_commutator (mem_top (c : P)) d.property)
  obtain ⟨z, hz, heq⟩ := hh
  exact (Subtype.ext heq : z = ⁅c, d⁆) ▸ hz


end IsPGroup
