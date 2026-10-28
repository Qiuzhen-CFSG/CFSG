module
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Sylow overgroups when a normal factor exhausts the core quotient

If N is normal in a finite group H and N/O_p(N) has the same order as
H/O_p(H), the image of N exhausts that quotient. A Sylow subgroup therefore
factors through O_p(H) and its intersection with N. The core normalizes every
intermediate subgroup between that intersection and N: its commutators lie
in O_p(H) intersect N. This proves invariance without a splitting hypothesis.

The normalized-join form is used to distinguish the product and wreath
endpoint extensions in Aschbacher--Smith 15.1.22(3), printed pp.1099--1100.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Equal orders of the core quotients force the Sylow subgroup to normalize
every intermediate overgroup of its intersection with the normal subgroup. -/
theorem sylow_normalizes_overgroup_of_core_quotient_card
    (N : Subgroup G) [N.Normal] (S : Sylow p G)
    (hcard : Nat.card (N ⧸ pCore p N) = Nat.card (G ⧸ pCore p G))
    (P : Subgroup G) (hSP : (S : Subgroup G) ⊓ N ≤ P) (hPN : P ≤ N) :
    (S : Subgroup G) ≤ normalizer (P : Set G) := by
  let q := QuotientGroup.mk' (pCore p G)
  have himage : N.map q = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top _).mp
    exact (Nat.card_congr ((Normal.isSubnormal (inferInstance : N.Normal)).quotientCoreImageEquiv p).toEquiv).symm.trans hcard
  have hcoreS : pCore p G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have hcoreP : pCore p G ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    exact (commutator_mono le_rfl hPN).trans
      ((commutator_le_inf _ _).trans ((inf_le_inf_right _ hcoreS).trans hSP))
  intro s hs
  obtain ⟨n,hn,he⟩ := show q s ∈ N.map q by rw [himage]; exact mem_top _
  have hc : s * n⁻¹ ∈ pCore p G := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (s * n⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hnS : n ∈ (S : Subgroup G) := by
    have hh := (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hcoreS hc)) hs
    simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
  have hh := (normalizer (P : Set G)).mul_mem (hcoreP hc) (P.le_normalizer (hSP ⟨hnS,hn⟩))
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The literal normalized-join form, retaining both intrinsic cores and
the specified Sylow subgroup of the normal factor. -/
theorem normalizes_overgroup_of_join_core_quotient_card
    (N R : Subgroup G) (hn : R ≤ normalizer (N : Set G))
    (hR : IsPGroup p R) (Q : Sylow p N)
    (hQ : (Q : Subgroup N).map N.subtype ≤ R)
    (hcard : Nat.card (N ⧸ pCore p N) =
      Nat.card ((N ⊔ R : Subgroup G) ⧸ pCore p (N ⊔ R : Subgroup G)))
    (P : Subgroup G) (hRP : R ⊓ N ≤ P) (hPN : P ≤ N) :
    R ≤ normalizer (P : Set G) := by
  let H := N ⊔ R
  let I := N.subgroupOf H
  let : I.Normal := normal_subgroupOf_of_le_normalizer (sup_le N.le_normalizer hn)
  obtain ⟨S,hS⟩ := IsPGroup.exists_sylow_sup_of_coprime_index N R hR hn
    (Q : Subgroup N) Q.not_dvd_index hQ
  let e : I ≃* N := subgroupOfEquivOfLe (show N ≤ H from le_sup_left)
  have hc : Nat.card (I ⧸ pCore p I) = Nat.card (H ⧸ pCore p H) :=
    (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso p e)).toEquiv).trans hcard
  have hS' : (S : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right)]
    exact hS
  have ht := sylow_normalizes_overgroup_of_core_quotient_card I S hc (P.subgroupOf H)
    (by rw [hS']; exact fun _ hx => hRP hx) (fun _ hx => hPN hx)
  have hm := (map_mono (f := H.subtype) ht).trans ((P.subgroupOf H).le_normalizer_map H.subtype)
  rw [hS,map_subgroupOf_eq_of_le (hPN.trans (show N ≤ H from le_sup_left))] at hm
  exact hm
end Subgroup
