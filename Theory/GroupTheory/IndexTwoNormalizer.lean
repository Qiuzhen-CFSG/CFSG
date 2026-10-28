module
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Normalizers controlled by an index-two overgroup

An index-two subgroup normalizing A leaves at most two conjugates of A.
A smaller acting group which moves A consequently has normalizer of index
two. Every element outside that normalizer gives the same conjugate.
The proofs use the two cosets, preserving right conjugation by t⁻¹.

Application: Aschbacher--Smith 14.6.12--16, printed pp.1031--1035.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A subgroup normalized by an index-two overgroup and moved by T has
relative normalizer of index two in T. -/
theorem normalizer_relIndex_eq_two_of_index_two_overgroup
    (T H H0 H1 : Subgroup G) (hTH : T ≤ H)
    (hi : H0.relIndex H = 2) (h0N : H0 ≤ normalizer (H1 : Set G))
    (hmoved : ∃ t ∈ T, t ∉ normalizer (H1 : Set G)) :
    (T ⊓ normalizer (H1 : Set G)).relIndex T = 2 := by
  let : (H0.subgroupOf H).Normal := normal_of_index_eq_two hi
  have hd0 : H0.relIndex T ∣ 2 := by
    have hd := relIndex_dvd_index_of_normal (H0.subgroupOf H) (T.subgroupOf H)
    rw [relIndex_subgroupOf hTH] at hd
    exact hi ▸ hd
  have hd : (T ⊓ normalizer (H1 : Set G)).relIndex T ∣ 2 := by
    rw [inf_relIndex_left]
    exact (relIndex_dvd_of_le_left T h0N).trans hd0
  apply (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
  intro hone
  obtain ⟨t,ht,htN⟩ := hmoved
  exact htN ((relIndex_eq_one.mp hone ht).2)
/-- All elements in the nontrivial coset have the same effect on a subgroup
normalized by the subgroup of index two. -/
theorem map_conj_eq_of_index_two (D A : Subgroup G) (hi : D.index = 2)
    (hn : D ≤ normalizer (A : Set G)) (x y : G) (hx : x ∉ D) (hy : y ∉ D) :
    A.map (MulAut.conj x).toMonoidHom = A.map (MulAut.conj y).toMonoidHom := by
  have hm : y⁻¹ * x ∈ D := (D.mul_mem_iff_of_index_two hi).mpr
    (by simp only [inv_mem_iff, hx, hy])
  have he := mem_normalizer_iff_map_conj_eq.mp (hn hm)
  have hh := congrArg (fun B : Subgroup G => B.map (MulAut.conj y).toMonoidHom) he
  rw [map_map] at hh
  convert hh using 1
  congr 1
  ext z
  simp [MulAut.conj_apply,mul_assoc]

/-- Outside elements give the same right conjugate when an index-two
overgroup normalizes the original subgroup. -/
theorem map_conj_eq_of_outside_normalizer
    (T H H0 H1 H2 : Subgroup G) (hTH : T ≤ H) (h1H : H1 ≤ H)
    (hi : H0.relIndex H = 2) (h0N : H0 ≤ normalizer (H1 : Set G))
    (x : G) (hx : x ∈ T) (hxN : x ∉ normalizer (H1 : Set G))
    (hex : H1.map (MulAut.conj x⁻¹).toMonoidHom = H2)
    (t : G) (ht : t ∈ T) (htN : t ∉ T ⊓ normalizer (H1 : Set G)) :
    H1.map (MulAut.conj t⁻¹).toMonoidHom = H2 := by
  have htN' : t ∉ normalizer (H1 : Set G) := fun hn => htN ⟨ht,hn⟩
  have hn : H0.subgroupOf H ≤ normalizer (H1.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq h1H]
    exact fun _ hb => h0N hb
  have ht0 : (⟨t⁻¹,H.inv_mem (hTH ht)⟩ : H) ∉ H0.subgroupOf H := by
    intro hh
    have hmem : t⁻¹ ∈ normalizer (H1 : Set G) := h0N hh
    exact htN' (inv_mem_iff.mp hmem)
  have hx0 : (⟨x⁻¹,H.inv_mem (hTH hx)⟩ : H) ∉ H0.subgroupOf H := by
    intro hh
    have hmem : x⁻¹ ∈ normalizer (H1 : Set G) := h0N hh
    exact hxN (inv_mem_iff.mp hmem)
  have he := map_conj_eq_of_index_two (H0.subgroupOf H) (H1.subgroupOf H)
    hi hn ⟨t⁻¹,H.inv_mem (hTH ht)⟩ ⟨x⁻¹,H.inv_mem (hTH hx)⟩ ht0 hx0
  have hmap := congrArg (fun B : Subgroup H => B.map H.subtype) he
  have hc (b : H) :
      (MulAut.conj (b : G)).toMonoidHom.comp H.subtype =
        H.subtype.comp (MulAut.conj b).toMonoidHom := rfl
  have hmap' : H1.map (MulAut.conj t⁻¹).toMonoidHom =
      H1.map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [← map_subgroupOf_eq_of_le h1H, map_map, map_map,
      hc ⟨t⁻¹,H.inv_mem (hTH ht)⟩, hc ⟨x⁻¹,H.inv_mem (hTH hx)⟩]
    simpa only [map_map] using hmap
  exact hmap'.trans hex


end Subgroup
