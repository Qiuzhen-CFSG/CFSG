module
public import Theory.GroupTheory.SylowNormalizerConjugate
public import Theory.GroupTheory.ConjugationOrbitSize
/-!
# Sylow selection and the prime part of a point orbit

Select a conjugate of a point inside a prescribed Sylow overgroup so that
its centralizer has Sylow intersection with the fixed Sylow subgroup.
The index of that intersection in the Sylow is exactly the prime part
of the centralizer index. Orbit control by a subgroup computes this
index without changing the point or the conjugation convention.

Source application: Aschbacher--Smith, the selection before 12.6.3,
printed pp.823--824. An orbit of length 28 gives index four at p=2.
-/

public section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem relIndex_eq_pow_factorization (P : Sylow p G) (C : Subgroup G)
    (hPC : ¬ p ∣ (P : Subgroup G).relIndex C) :
    C.relIndex (P : Subgroup G) = p ^ C.index.factorization p := by
  have he : C.relIndex (P : Subgroup G) * (P : Subgroup G).index =
      (P : Subgroup G).relIndex C * C.index := by
    rw [← inf_relIndex_left, relIndex_mul_index inf_le_left,
      ← inf_relIndex_right, relIndex_mul_index inf_le_right]
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have hd : C.relIndex (P : Subgroup G) ∣ p ^ n := by
    rw [← hn]
    exact (C.subgroupOf (P : Subgroup G)).index_dvd_card
  obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  have hf := congrArg (fun a : ℕ => a.factorization p) he
  rw [Nat.factorization_mul (show C.relIndex (P : Subgroup G) ≠ 0 from
      index_ne_zero_of_finite) index_ne_zero_of_finite,
    Nat.factorization_mul (show (P : Subgroup G).relIndex C ≠ 0 from
      index_ne_zero_of_finite) index_ne_zero_of_finite,
    Finsupp.add_apply,Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd P.not_dvd_index,
    Nat.factorization_eq_zero_of_not_dvd hPC,hk] at hf
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.Prime.factorization_self (Fact.out : p.Prime), mul_one, add_zero, zero_add] at hf
  rw [hk,hf]
end Sylow

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] in
/-- An automorphism carries the full point centralizer to that of its image. -/
theorem map_pointCentralizer (e : G ≃* G) (v : G) :
    (centralizer ({v} : Set G)).map e.toMonoidHom = centralizer ({e v} : Set G) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change y ∈ centralizer ({v} : Set G) at hy
    rw [mem_centralizer_singleton_iff] at hy ⊢
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg e hy
  · intro hx
    refine ⟨e.symm x, ?_,e.apply_symm_apply x⟩
    change e.symm x ∈ centralizer ({v} : Set G)
    rw [mem_centralizer_singleton_iff] at hx ⊢
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx

theorem exists_local_point_sylow (T : Sylow p G) (J : Subgroup G)
    (hTJ : (T : Subgroup G) ≤ J) (v : G) :
    ∃ n : J, ¬ p ∣ (T : Subgroup G).relIndex (J ⊓ centralizer ({(n : G)*v*(n : G)⁻¹} : Set G)) := by
  let C := (centralizer ({v} : Set G)).subgroupOf J
  obtain ⟨n,hn⟩ := (T.subtype hTJ).exists_conjugate_not_dvd_relIndex C
  have hJ : J.map (MulAut.conj (n : G)).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (J.le_normalizer n.property)
  have hmap : (C.map (MulAut.conj n).toMonoidHom).map J.subtype =
      J ⊓ centralizer ({(n : G)*v*(n : G)⁻¹} : Set G) := by
    have he : J.subtype.comp (MulAut.conj n).toMonoidHom =
        (MulAut.conj (n : G)).toMonoidHom.comp J.subtype := by ext x; rfl
    rw [map_map,he,← map_map]
    change ((centralizer ({v} : Set G)).subgroupOf J |>.map J.subtype).map _ = _
    rw [subgroupOf_map_subtype,map_inf _ _ _ (MulAut.conj (n : G)).injective,
      map_pointCentralizer,hJ,inf_comm]
    rfl
  refine ⟨n,?_⟩
  rw [← hmap, ← map_subgroupOf_eq_of_le hTJ,
    relIndex_map_map_of_injective _ _ J.subtype_injective]
  exact hn

omit [Finite G] in
theorem conjugacyOrbit_ncard_eq_relIndex (J : Subgroup G) (v : G) :
    (conjugacyOrbit J v).ncard = (centralizer ({v} : Set G)).relIndex J := by
  let : MulAction J G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp J.subtype)
  have hs : MulAction.stabilizer J v = (centralizer ({v} : Set G)).subgroupOf J := by
    ext n
    change (n : G) * v * (n : G)⁻¹ = v ↔ (n : G) ∈ centralizer ({v} : Set G)
    rw [mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]
  have ho : MulAction.orbit J v = conjugacyOrbit J v := rfl
  have he := Nat.card_congr (MulAction.orbitEquivQuotientStabilizer J v)
  rw [ho,hs] at he
  exact he

omit [Finite G] in
theorem point_centralizer_index_of_orbit_control
    (L J : Subgroup G) (hLJ : L ≤ J) (v : G)
    (ho : ∀ n : J, ∃ l : L, (n : G)*v*(n : G)⁻¹ = (l : G)*v*(l : G)⁻¹) :
    (centralizer ({v} : Set G)).relIndex J = (centralizer ({v} : Set G)).relIndex L := by
  rw [← conjugacyOrbit_ncard_eq_relIndex,← conjugacyOrbit_ncard_eq_relIndex]
  congr 1
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    obtain ⟨l,hl⟩ := ho n
    exact ⟨l,hl.symm⟩
  · rintro ⟨l,rfl⟩
    exact ⟨⟨l,hLJ l.property⟩,rfl⟩
end Subgroup
