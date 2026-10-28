module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.AbelianConsequences

/-!
# Comparing abelian odd centralizer complements

An abelian odd complement contains every odd-order element commuting with
its marked generator. Thus two abelian complements coincide whenever the
marked generator of the second belongs to the first. Involution fusion
also permits the original centralizer data to be marked at any involution.
Together these facts allow us to use the same complement at each nontrivial
prime fixed subgroup of its four-group action.

A noncyclic abelian complement is self-centralizing: an involution in its
centralizer would embed the complement in an involution centralizer, where
every odd subgroup has order one, three or five.

These are ambient-group inputs to the noncyclic-order step cited in
Bender, *Finite groups with large subgroups* (1974), proof of (4.1),
printed p.225, referring to Janko (1966), proof of Lemma 3.1. They do not
assume the order or the exceptional normalizer of the complement.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

/-- The actual local hypotheses can be marked at every ambient involution. -/
public theorem exists_data_at_involution [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (t : G) (ht : orderOf t = 2) :
    ∃ k : Janko1CentralizerData G, k.z = t := by
  obtain ⟨g, hg⟩ := h.involutions_conjugate t ht
  let f := MulAut.conj g
  have hf : f t = h.z := hg
  have he : (centralizer ({t} : Set G)).map f.toMonoidHom =
      centralizer ({h.z} : Set G) := by
    ext y
    rw [mem_map_equiv, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    rw [← f.injective.eq_iff, map_mul, map_mul, f.apply_symm_apply, hf]
  let e := (f.subgroupMap (centralizer ({t} : Set G))).trans
    (MulEquiv.subgroupCongr he)
  obtain ⟨S, htS, hcent⟩ := h.involution_is_two_central t ht
  exact ⟨⟨t, ht, S, htS, hcent, ⟨e.trans h.centralizer_equiv.some⟩⟩, rfl⟩

/-- Intersecting abelian complements at a marked generator identifies them. -/
public theorem OddCentralizerComplement.eq_of_mark_mem_of_commutative
    {h k : Janko1CentralizerData G} {x y : G} {A B : Subgroup G}
    (a : OddCentralizerComplement h x A) (b : OddCentralizerComplement k y B)
    (ha : IsMulCommutative A) (hb : IsMulCommutative B) (hy : y ∈ A) : A = B := by
  let := ha
  let := hb
  have hAB : A ≤ B := by
    intro u hu
    apply (b.mem_iff_odd_orderOf ?_).mpr (a.odd_orderOf hu)
    exact mem_centralizer_singleton_iff.mpr ((Subgroup.le_centralizer A hu) y hy).symm
  apply le_antisymm hAB
  intro u hu
  apply (a.mem_iff_odd_orderOf ?_).mpr (b.odd_orderOf hu)
  exact mem_centralizer_singleton_iff.mpr ((Subgroup.le_centralizer B hu) x (hAB a.x_mem)).symm

/-- A fixed prime element gives the same complement with a new marked involution.
The universal commutativity premise is exactly the independent source input. -/
public theorem OddCentralizerComplement.remark_at_fixed_prime [IsSimpleGroup G]
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (ha : IsMulCommutative A)
    (allComm : ∀ (k : Janko1CentralizerData G) (q : ℕ), (q = 3 ∨ q = 5) →
      ∀ y : G, y ∈ centralizer ({k.z} : Set G) → orderOf y = q →
        ∀ B : Subgroup G, OddCentralizerComplement k y B → IsMulCommutative B)
    (t : G) (ht : orderOf t = 2) (q : ℕ) (hq : q = 3 ∨ q = 5)
    (y : G) (hyA : y ∈ A) (hyt : y ∈ centralizer ({t} : Set G))
    (hy : orderOf y = q) :
    ∃ k : Janko1CentralizerData G, k.z = t ∧ OddCentralizerComplement k y A := by
  obtain ⟨k, hk⟩ := h.exists_data_at_involution t ht
  have hyk : y ∈ centralizer ({k.z} : Set G) := hk.symm ▸ hyt
  obtain ⟨B, b⟩ := k.exists_oddCentralizerComplement q hq y hyk hy
  have he := a.eq_of_mark_mem_of_commutative b ha (allComm k q hq y hyk hy B b) hyA
  exact ⟨k, hk, he.symm ▸ b⟩

omit [Finite G] in
private theorem cyclic_of_small_card (A : Subgroup G)
    (hc : Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 5) : IsCyclic A := by
  rcases hc with hc | hc | hc
  · exact isCyclic_of_card_dvd_prime (p := 3) (by rw [hc]; decide)
  · exact isCyclic_of_prime_card (p := 3) hc
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact isCyclic_of_prime_card (p := 5) hc

/-- A noncyclic odd complement has no involution in its full centralizer. -/
public theorem OddCentralizerComplement.centralizer_odd_of_noncyclic [IsSimpleGroup G]
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (hncyc : ¬ IsCyclic A) :
    Odd (Nat.card (centralizer (A : Set G))) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer (A : Set G)) 2 (even_iff_two_dvd.mp heven)
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_mk _ _).symm.trans ht
  have hAt : A ≤ centralizer ({(t : G)} : Set G) := by
    intro u hu
    exact mem_centralizer_singleton_iff.mpr (t.property u hu)
  exact hncyc (cyclic_of_small_card A
    (h.odd_subgroup_centralizing_involution_card A a.odd_card t htG hAt))

/-- A noncyclic abelian odd complement is its full ambient centralizer. -/
public theorem OddCentralizerComplement.centralizer_eq_of_noncyclic [IsSimpleGroup G]
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (ha : IsMulCommutative A)
    (hncyc : ¬ IsCyclic A) : centralizer (A : Set G) = A := by
  let := ha
  apply le_antisymm ?_ (Subgroup.le_centralizer A)
  intro y hy
  apply (a.mem_iff_odd_orderOf ?_).mpr
    ((a.centralizer_odd_of_noncyclic hncyc).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hy))
  exact mem_centralizer_singleton_iff.mpr (hy x a.x_mem).symm

end CFSG.Quasithin.Janko1CentralizerData
