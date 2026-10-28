module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.NoncyclicOrder.FixedFusion

/-!
# Prime support determines the odd complement order

The odd complement is the set of odd-order elements in its centralizer.
Consequently conjugating the marked prime subgroup conjugates the entire
complement. All complements marked at the same prime have the same order.

The four-fixed-subgroup formula detects each prime divisor of a complement
in an actual involution fixed subgroup. Under universal commutativity,
remarking at that subgroup preserves the complement. This relates the
orders of complements marked at different primes, without assuming that
either complement is Sylow or that an exceptional normalizer exists.

Source: the noncyclic-order step in Bender (1974), proof of (4.1), p.225,
citing Janko (1966), proof of Lemma 3.1.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

/-- Conjugating the marked subgroup conjugates its unique odd complement. -/
public theorem OddCentralizerComplement.map_eq_of_map_zpowers
    {h k : Janko1CentralizerData G} {x y : G} {A B : Subgroup G}
    (a : OddCentralizerComplement h x A) (b : OddCentralizerComplement k y B)
    (f : G ≃* G) (hf : (zpowers x).map f.toMonoidHom = zpowers y) :
    A.map f.toMonoidHom = B := by
  ext u
  rw [mem_map_equiv]
  have aC {v : G} (hv : v ∈ A) : v ∈ centralizer (zpowers x : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact a.le_centralizer h hv
  have bC {v : G} (hv : v ∈ B) : v ∈ centralizer (zpowers y : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact b.le_centralizer k hv
  constructor
  · intro hu
    apply (b.mem_iff_odd_orderOf ?_).mpr
    · have ho := a.odd_orderOf hu
      rwa [f.symm.orderOf_eq] at ho
    · have hy : f.symm y ∈ zpowers x :=
        mem_map_equiv.mp (hf.symm ▸ mem_zpowers y)
      apply mem_centralizer_singleton_iff.mpr
      apply f.symm.injective
      simpa only [map_mul] using ((aC hu) (f.symm y) hy).symm
  · intro hu
    apply (a.mem_iff_odd_orderOf ?_).mpr
    · rw [f.symm.orderOf_eq]
      exact b.odd_orderOf hu
    · have hx : f x ∈ zpowers y := hf ▸ mem_map.mpr ⟨x, mem_zpowers x, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      simpa only [map_mul, f.apply_symm_apply] using ((bC hu) (f x) hx).symm

/-- The order of an odd complement depends only on its marked prime. -/
public theorem OddCentralizerComplement.card_eq_of_same_prime [IsSimpleGroup G]
    {h k : Janko1CentralizerData G} {x y : G} {A B : Subgroup G}
    (a : OddCentralizerComplement h x A) (b : OddCentralizerComplement k y B)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hyC : y ∈ centralizer ({k.z} : Set G)) (hy : orderOf y = p) :
    Nat.card A = Nat.card B := by
  obtain ⟨g, _, hg⟩ := h.prime_fixed_pair_conjugate p hp x hxC hx k.z k.involution
    (zpowers y) (by rw [Nat.card_zpowers, hy]) (zpowers_le.mpr hyC)
  have he := b.map_eq_of_map_zpowers a (MulAut.conj g) hg
  rw [← he, card_map_of_injective (MulAut.conj g).injective]

private theorem second_involution {h : Janko1CentralizerData G}
    (t : G) (htC : t ∈ centralizer ({h.z} : Set G))
    (ht : orderOf t = 2) (htz : t ∉ zpowers h.z) : orderOf (h.z * t) = 2 := by
  have hc : Commute h.z t := (mem_centralizer_singleton_iff.mp htC).symm
  apply orderOf_eq_prime_iff.mpr
  constructor
  · rw [hc.mul_pow, show h.z ^ 2 = 1 from h.involution ▸ pow_orderOf_eq_one h.z,
      show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t, mul_one]
  · intro he
    apply htz
    have he' : t = h.z⁻¹ := by simpa using congrArg (h.z⁻¹ * ·) he
    rw [he']
    exact (zpowers h.z).inv_mem (mem_zpowers h.z)

/-- Every prime divisor is realized by remarking the same complement at a fixed element. -/
public theorem OddCentralizerComplement.remark_at_prime_divisor [IsSimpleGroup G]
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (ha : IsMulCommutative A)
    (allComm : ∀ (k : Janko1CentralizerData G) (q : ℕ), (q = 3 ∨ q = 5) →
      ∀ y : G, y ∈ centralizer ({k.z} : Set G) → orderOf y = q →
        ∀ B : Subgroup G, OddCentralizerComplement k y B → IsMulCommutative B)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (q : ℕ) (hq : q = 3 ∨ q = 5) (hqd : q ∣ Nat.card A) :
    ∃ (k : Janko1CentralizerData G) (y : G),
      y ∈ centralizer ({k.z} : Set G) ∧ orderOf y = q ∧
        OddCentralizerComplement k y A := by
  by_cases hqp : q = p
  · exact ⟨h, x, hxC, hqp.symm ▸ hx, a⟩
  have hqprime : q.Prime := by rcases hq with rfl | rfl <;> decide
  let : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨t, htC, ht, htz, hti⟩ := h.exists_local_inverter p hp x hxC hx
  have hm := a.four_fixed_card p hp hxC hx t htC ht htz hti
  have hqp' : ¬ q ∣ p := by
    intro hd
    have hpprime : p.Prime := by rcases hp with rfl | rfl <;> decide
    exact hqp ((Nat.dvd_prime hpprime).mp hd |>.resolve_left hqprime.ne_one)
  have fixed (s : G) (hs : orderOf s = 2)
      (hd : q ∣ Nat.card (A ⊓ centralizer ({s} : Set G) : Subgroup G)) :
      ∃ (k : Janko1CentralizerData G) (y : G),
        y ∈ centralizer ({k.z} : Set G) ∧ orderOf y = q ∧
          OddCentralizerComplement k y A := by
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(A ⊓ centralizer ({s} : Set G))) q hd
    have hyG : orderOf (y : G) = q := (Subgroup.orderOf_mk _ _).symm.trans hy
    obtain ⟨k, hk, b⟩ := a.remark_at_fixed_prime ha allComm s hs q hq y
      y.property.1 y.property.2 hyG
    exact ⟨k, y, hk.symm ▸ y.property.2, hyG, b⟩
  rw [hm] at hqd
  rcases hqprime.dvd_mul.mp hqd with hleft | hright
  · exact fixed t ht ((hqprime.dvd_mul.mp hleft).resolve_left hqp')
  · exact fixed (h.z * t) (second_involution t htC ht htz) hright

/-- Sharing a prime divisor identifies the orders of the actual complements. -/
public theorem OddCentralizerComplement.card_eq_of_prime_dvd [IsSimpleGroup G]
    {h k : Janko1CentralizerData G} {x y : G} {A B : Subgroup G}
    (a : OddCentralizerComplement h x A) (b : OddCentralizerComplement k y B)
    (ha : IsMulCommutative A)
    (allComm : ∀ (k : Janko1CentralizerData G) (q : ℕ), (q = 3 ∨ q = 5) →
      ∀ y : G, y ∈ centralizer ({k.z} : Set G) → orderOf y = q →
        ∀ B : Subgroup G, OddCentralizerComplement k y B → IsMulCommutative B)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (q : ℕ) (hq : q = 3 ∨ q = 5)
    (hyC : y ∈ centralizer ({k.z} : Set G)) (hy : orderOf y = q)
    (hqd : q ∣ Nat.card A) : Nat.card A = Nat.card B := by
  obtain ⟨l, u, huC, hu, c⟩ := a.remark_at_prime_divisor ha allComm p hp hxC hx q hq hqd
  exact c.card_eq_of_same_prime b q hq huC hu hyC hy

end CFSG.Quasithin.Janko1CentralizerData
