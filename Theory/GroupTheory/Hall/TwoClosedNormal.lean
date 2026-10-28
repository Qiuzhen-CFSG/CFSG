module

public import Theory.PGroupCore
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.Hall.Conjugacy

/-!
# Odd Hall control over a normal two-closed subgroup

Suppose a normal subgroup B has a normal Sylow two-subgroup and abelian
odd quotient. Odd subgroups of B embed in that quotient. If G/B is a
two-group, every odd subgroup of G lies in B and G is solvable.

Conjugacy of Hall subgroups inside B and its normal Sylow complement
factorization give G = O₂(B) N_G(Y). Intersecting with the supplied Sylow
two-subgroup gives S = O₂(B) N_S(Y), with the core embedded in G.
This is the Frattini step of Aschbacher--Smith, 4.4.13(2), printed p.624.
The concrete central-cover Borel calculation is a separate hypothesis.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- An odd subgroup has trivial image in a two-group quotient. -/
theorem odd_subgroup_le (B Y : Subgroup G) [B.Normal]
    (hq : IsPGroup 2 (G ⧸ B)) (ho : Odd (Nat.card Y)) : Y ≤ B := by
  let q := QuotientGroup.mk' B
  have hp := hq.to_subgroup (Y.map q)
  have hcop : Nat.Coprime 2 (Nat.card (Y.map q)) :=
    (Nat.coprime_two_left.mpr ho).of_dvd_right (card_map_dvd Y q)
  have hz : Y.map q = ⊥ := by
    rcases hp.card_eq_or_dvd with h | h
    · exact eq_bot_of_card_eq _ h
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp hcop) h)
  simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff Y).mp hz

/-- A normal Sylow two-subgroup with abelian odd quotient. -/
structure TwoClosedAbelianQuotient (B : Subgroup G) : Prop where
  odd_index : Odd (pCore 2 B).index
  abelian : IsMulCommutative (B ⧸ pCore 2 B)

/-- Such a subgroup is an extension of two solvable groups. -/
theorem TwoClosedAbelianQuotient.solvable {B : Subgroup G}
    (h : TwoClosedAbelianQuotient B) : Group.IsSolvable B := by
  let := h.abelian
  let : Group.IsSolvable (B ⧸ pCore 2 B) :=
    Group.isSolvable_of_comm (mul_comm' (M := B ⧸ pCore 2 B))
  let := (pCore_isPGroup (p := 2) (G := B)).isNilpotent
  exact Group.isSolvable_of_ker_le_range (pCore 2 B).subtype
    (QuotientGroup.mk' (pCore 2 B)) (by rw [range_subtype, QuotientGroup.ker_mk'])

/-- A two-group extension preserves this solvability. -/
theorem TwoClosedAbelianQuotient.solvable_extension {B : Subgroup G} [B.Normal]
    (hq : IsPGroup 2 (G ⧸ B)) (h : TwoClosedAbelianQuotient B) : Group.IsSolvable G := by
  let := h.solvable
  let := hq.isNilpotent
  exact Group.isSolvable_of_ker_le_range B.subtype (QuotientGroup.mk' B)
    (by rw [range_subtype, QuotientGroup.ker_mk'])

omit [Finite G] in
/-- The Hall prime-set convention gives literal odd cardinality. -/
theorem odd_hall_odd {Y : Subgroup G} (hY : IsHallSubgroup oddPrimes Y) :
    Odd (Nat.card Y) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact fun hh => hY.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ hh rfl

omit [Finite G] in
/-- Every odd subgroup embeds in the abelian quotient by the two-core. -/
theorem TwoClosedAbelianQuotient.odd_subgroup_abelian {B Y : Subgroup G}
    (h : TwoClosedAbelianQuotient B)
    (hYB : Y ≤ B) (ho : Odd (Nat.card Y)) : IsMulCommutative Y := by
  let q := QuotientGroup.mk' (pCore 2 B)
  let f := q.comp (inclusion hYB)
  have hpker : IsPGroup 2 f.ker :=
    (pCore_isPGroup (p := 2) (G := B)).of_injective
      ((inclusion hYB).comp f.ker.subtype |>.codRestrict (pCore 2 B) (by
        intro y
        exact (QuotientGroup.eq_one_iff _).mp y.property))
      (by intro x y hxy; apply Subtype.ext; exact inclusion_injective hYB (Subtype.ext_iff.mp hxy))
  have hcop : Nat.Coprime 2 (Nat.card f.ker) :=
    (Nat.coprime_two_left.mpr ho).of_dvd_right (card_subgroup_dvd_card f.ker)
  have hk : f.ker = ⊥ := by
    rcases hpker.card_eq_or_dvd with hc | hd
    · exact eq_bot_of_card_eq _ hc
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp hcop) hd)
  have hi := (MonoidHom.ker_eq_bot_iff f).mp hk
  let := h.abelian
  exact IsMulCommutative.of_comm fun a b => hi (by simp only [map_mul]; exact mul_comm' _ _)

/-- Hall conjugacy inside the normal subgroup gives the exact Sylow
factorization. The witness is the ambient image of its two-core. -/
theorem normal_twoClosed_frattini (B : Subgroup G) [B.Normal]
    (h : TwoClosedAbelianQuotient B)
    (S : Sylow 2 G) (Y : Subgroup G) (hYB : Y ≤ B)
    (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf B)) :
    ∃ Q : Subgroup G, Y ≤ normalizer (Q : Set G) ∧
      (S : Set G) = (Q : Set G) *
        ((S : Subgroup G) ⊓ normalizer (Y : Set G) : Set G) := by
  let Q := (pCore 2 B).map B.subtype
  have hNQ : normalizer (Q : Set G) = ⊤ := by
    apply top_unique
    rw [← normalizer_eq_top B]
    exact normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  let : Q.Normal := normalizer_eq_top_iff.mp hNQ
  have hQS : Q ≤ (S : Subgroup G) :=
    (pCore_isPGroup.map B.subtype).le_sylow_of_normal S
  refine ⟨Q, by rw [hNQ]; exact le_top, ?_⟩
  apply Set.Subset.antisymm
  · intro s hs
    let a : MulAut B := MulAut.conjNormal s
    have hh : IsHallSubgroup OddHall.oddPrimes (Y.subgroupOf B) := hHall
    have hcomp := OddHall.sylow_complement_of_hall
      ((pCore_isPGroup (p := 2) (G := B)).toSylow
        (Nat.not_even_iff_odd.mpr h.odd_index ∘ even_iff_two_dvd.mpr)) hh
    obtain ⟨b, hb⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable h.solvable
      hHall (hHall.map_mulAut a)
    obtain ⟨⟨q, y⟩, hqy⟩ := hcomp.2 b
    have hmap : Y.map (MulAut.conj s).toMonoidHom =
        Y.map (MulAut.conj b.val).toMonoidHom := by
      have he := congrArg (Subgroup.map B.subtype) hb
      rw [map_map, map_map] at he
      have hleft : B.subtype.comp a.toMonoidHom =
          (MulAut.conj s).toMonoidHom.comp B.subtype := rfl
      have hright : B.subtype.comp (MulAut.conj b).toMonoidHom =
          (MulAut.conj b.val).toMonoidHom.comp B.subtype := rfl
      rw [hleft, hright, ← map_map, ← map_map,
        map_subgroupOf_eq_of_le hYB] at he
      exact he
    have hn : b.val⁻¹ * s ∈ normalizer (Y : Set G) := by
      rw [mem_normalizer_iff_map_conj_eq]
      change Y.map (MulAut.conj (b.val⁻¹ * s)).toMonoidHom = Y
      have he := congrArg (Subgroup.map (MulAut.conj b.val⁻¹).toMonoidHom) hmap
      simp only [map_map] at he
      have hleft : (MulAut.conj b.val⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
          (MulAut.conj (b.val⁻¹ * s)).toMonoidHom := by ext; simp [mul_assoc]
      have hright : (MulAut.conj b.val⁻¹).toMonoidHom.comp (MulAut.conj b.val).toMonoidHom =
          MonoidHom.id G := by ext; simp [mul_assoc]
      simpa only [hleft, hright, map_id] using he
    have hqn : q.val.val⁻¹ * s ∈ normalizer (Y : Set G) := by
      have he : b.val = q.val.val * y.val.val := congrArg Subtype.val hqy.symm
      have hn' := (normalizer (Y : Set G)).mul_mem (Y.le_normalizer y.property) hn
      change y.val.val * (b.val⁻¹ * s) ∈ normalizer (Y : Set G) at hn'
      have he' : y.val.val * (b.val⁻¹ * s) = q.val.val⁻¹ * s := by rw [he]; group
      rwa [he'] at hn'
    exact ⟨q.val.val, ⟨q.val, q.property, rfl⟩, q.val.val⁻¹ * s,
      ⟨S.mul_mem (S.inv_mem (hQS ⟨q.val, q.property, rfl⟩)) hs, hqn⟩,
      mul_inv_cancel_left _ _⟩
  · rintro _ ⟨q, hq, t, ht, rfl⟩
    exact S.mul_mem (hQS hq) ht.1

end Subgroup.OddHall
