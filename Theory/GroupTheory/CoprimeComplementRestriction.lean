module
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Sylow

/-!
# Restricting coprime complements to normal subgroups

For a factorization by subgroups of coprime orders, the two factors of an
element in a normal subgroup both belong to that normal subgroup. In the
quotient, their images are mutual inverses in subgroups of coprime orders,
hence both images are trivial. The original unique factorization
therefore restricts to the normal subgroup.

This is used to restrict the full-edge complement in DGS 12.3(a), printed
p.179, to the relatively normal starred endpoint, without identifying
that endpoint with the full vertex stabilizer.
-/

public section
namespace Subgroup
variable {D : Type*} [Group D]

/-- Coprime complementary factors restrict to complementary factors in a normal subgroup. -/
theorem IsComplement'.subgroupOf_normal_of_coprime (P K N : Subgroup D) [N.Normal]
    (h : P.IsComplement' K) (hc : Nat.Coprime (Nat.card P) (Nat.card K)) :
    (P.subgroupOf N).IsComplement' (K.subgroupOf N) := by
  let q := QuotientGroup.mk' N
  have hd : Disjoint (P.map q) (K.map q) := disjoint_of_coprime_natCard
    ((hc.coprime_dvd_left (P.card_map_dvd q)).coprime_dvd_right (K.card_map_dvd q))
  refine ⟨mul_injective_of_disjoint (by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro n hn
    apply Subtype.ext
    exact (disjoint_iff.mp h.disjoint).le hn), ?_⟩
  intro n
  obtain ⟨⟨p, k⟩, he⟩ := h.2 (n : D)
  change (p : D) * (k : D) = (n : D) at he
  have hq : q p * q k = 1 := by
    rw [← map_mul, he]
    exact (QuotientGroup.eq_one_iff _).mpr n.property
  have hp1 : q p = 1 := (disjoint_iff.mp hd).le
    ⟨mem_map_of_mem q p.property, by
      rw [eq_inv_of_mul_eq_one_left hq]
      exact (K.map q).inv_mem (mem_map_of_mem q k.property)⟩
  have hk1 : q k = 1 := by simpa only [hp1, one_mul] using hq
  exact ⟨(⟨⟨p, (QuotientGroup.eq_one_iff _).mp hp1⟩, p.property⟩,
    ⟨⟨k, (QuotientGroup.eq_one_iff _).mp hk1⟩, k.property⟩), Subtype.ext he⟩

/-- Restricting a coprime complement supplies the entire Sylow normalizer
in a relatively normal subgroup. -/
theorem sylow_normalizer_sup_restricted_complement
    {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
    (A E : Subgroup G) (hEA : E ≤ normalizer (A : Set G))
    (T : Sylow p A) (hT : E.subgroupOf A = normalizer (T : Set A))
    (P K : Subgroup E) (hp : IsPGroup p P) (h : P.IsComplement' K)
    (hc : Nat.Coprime (Nat.card P) (Nat.card K)) :
    (T : Subgroup A) ⊔ (K.map E.subtype).subgroupOf A = normalizer (T : Set A) := by
  let N := A.subgroupOf E
  let : N.Normal := normal_subgroupOf_of_le_normalizer hEA
  have hr := IsComplement'.subgroupOf_normal_of_coprime P K N h hc
  let R := (P.map E.subtype).subgroupOf A
  have hRN : R ≤ normalizer (T : Set A) := by
    rw [← hT]
    rintro a ⟨e, he, hea⟩
    change (e : G) = (a : G) at hea
    change (a : G) ∈ E
    rw [← hea]
    exact e.property
  have hRT : R ≤ T := by
    have hpR : IsPGroup p R := (hp.map E.subtype).comap_subtype
    rw [← inf_eq_left.mpr hRN, hpR.inf_normalizer_sylow T]
    exact inf_le_right
  apply le_antisymm
  · apply sup_le (T : Subgroup A).le_normalizer
    change (K.map E.subtype).subgroupOf A ≤ normalizer (T : Set A)
    rw [← hT]
    rintro a ⟨e, he, hea⟩
    change (e : G) = (a : G) at hea
    change (a : G) ∈ E
    rw [← hea]
    exact e.property
  · intro a ha
    have haE : (a : G) ∈ E := (show a ∈ E.subgroupOf A from hT.symm ▸ ha)
    obtain ⟨⟨u, v⟩, huv⟩ := hr.2 (⟨⟨a, haE⟩, a.property⟩ : N)
    let uA : A := ⟨u.val.val, u.val.property⟩
    let vA : A := ⟨v.val.val, v.val.property⟩
    have hu : uA ∈ R := ⟨u.val.val, u.property, rfl⟩
    have hv : vA ∈ (K.map E.subtype).subgroupOf A := ⟨v.val.val, v.property, rfl⟩
    have he : uA * vA = a := by
      apply Subtype.ext
      exact congrArg (fun n : N => ((n : E) : G)) huv
    rw [← he]
    exact Subgroup.mul_mem_sup (hRT hu) hv
end Subgroup
