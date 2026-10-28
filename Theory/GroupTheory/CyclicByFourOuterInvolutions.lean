module

public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Linarith

/-!
# Outer involutions in a cyclic-by-four presentation

A cyclic generator of order `2^(n+3)` admits the two unitary actions with
exponents `2^(n+2)-1` and `2^(n+2)+1`. Four normal forms cover the group.
An involution in the latter action's coset has cyclic part of order at most
two, because the relevant exponent gcd is two. The mixed coset inverts the
cyclic subgroup. This yields exactly one exceptional pair of involutions.

The four normal forms also give the relative-index bound by an explicit
surjection. The marked half-power is central, and faithful pullback retains
the actual inner and Sylow subgroup images. No matrix realization or Sylow
maximality is assumed to follow from the presentation; those must be proved
by a concrete-model caller.

Source application: the odd unitary case of Aschbacher--Smith E.1.14(7),
printed p.214, citing Aschbacher (1982), Lemma 4.11. The underlying inner
semidihedral torus is Alperin--Brauer--Gorenstein II.2 Lemma 1, article p.17.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Four cosets of a cyclic subgroup, with the two unitary reflection actions.
The definition contains generator relations and coverage, not an involution dichotomy. -/
structure CyclicByFourCoordinates {G : Type*} [Group G]
    (L T : Subgroup G) (z : G) where
  a : G
  b : G
  c : G
  n : ℕ
  a_order : orderOf a = 2 ^ (n + 3)
  a_inner : a ∈ L
  a_mem : a ∈ T
  b_inner : b ∈ L
  b_mem : b ∈ T
  c_mem : c ∈ T
  c_outer : c ∉ L
  c_sq : c ^ 2 = 1
  b_action : b * a * b⁻¹ = a ^ (2 ^ (n + 2) - 1)
  c_action : c * a * c⁻¹ = a ^ (2 ^ (n + 2) + 1)
  marked : z = a ^ (2 ^ (n + 2))
  cover : ∀ t ∈ T, ∃ i : ℤ,
    t = a ^ i ∨ t = a ^ i * b ∨ t = a ^ i * c ∨ t = a ^ i * b * c

namespace CyclicByFourCoordinates
variable {G : Type*} [Group G] {L T : Subgroup G} {z : G}
variable (d : CyclicByFourCoordinates L T z)

private theorem action_zpow (u a : G) (k : ℕ) (h : u * a * u⁻¹ = a ^ k) (i : ℤ) :
    u * a ^ i * u⁻¹ = (a ^ i) ^ k := by
  calc
    u * a ^ i * u⁻¹ = (u * a * u⁻¹) ^ i := (map_zpow (MulAut.conj u) a i)
    _ = (a ^ k) ^ i := by rw [h]
    _ = (a ^ i) ^ k := by rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, Int.mul_comm]

private theorem action_gcd (n : ℕ) :
    Nat.gcd (2 ^ (n + 3)) (2 ^ (n + 2) + 2) = 2 := by
  have he : 2 ^ (n + 2) + 2 = 2 * (2 ^ (n + 1) + 1) := by ring
  have ho : Odd (2 ^ (n + 1) + 1) := by
    exact (show Even (2 ^ (n + 1)) from ⟨2 ^ n, by ring⟩).add_odd odd_one
  rw [show 2 ^ (n + 3) = 2 * 2 ^ (n + 2) by ring, he, Nat.gcd_mul_left]
  rw [(ho.coprime_two_left.pow_left (n + 2)).gcd_eq_one, mul_one]

/-- In the Frobenius coset, a square-one element differs from the representative
by a square-one element of the cyclic subgroup. -/
theorem exceptional_coset_square (i : ℤ) (hi : (d.a ^ i * d.c) ^ 2 = 1) :
    (d.a ^ i) ^ 2 = 1 := by
  have hp : (d.a ^ i) ^ (2 ^ (d.n + 2) + 2) = 1 := by
    calc
      (d.a ^ i) ^ (2 ^ (d.n + 2) + 2) =
          d.a ^ i * (d.a ^ i) ^ (2 ^ (d.n + 2) + 1) := by
            rw [← pow_succ']
      _ = d.a ^ i * (d.c * d.a ^ i * d.c⁻¹) := by
        rw [action_zpow d.c d.a _ d.c_action]
      _ = (d.a ^ i * d.c) ^ 2 := by
        have hc : d.c⁻¹ = d.c := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using d.c_sq)
        rw [hc, pow_two]; group
      _ = 1 := hi
  apply orderOf_dvd_iff_pow_eq_one.mp
  have hd := Nat.dvd_gcd (orderOf_dvd_of_mem_zpowers (zpow_mem (mem_zpowers _) i))
    (orderOf_dvd_of_pow_eq_one hp)
  rwa [d.a_order, action_gcd] at hd

/-- The mixed reflection inverts the cyclic generator. -/
theorem mixed_inverts_generator : (d.b * d.c) * d.a * (d.b * d.c)⁻¹ = d.a⁻¹ := by
  let m := 2 ^ (d.n + 2)
  have hm : 1 ≤ m := by dsimp [m]; exact Nat.one_le_pow _ _ (by decide)
  have hpow : d.a ^ ((m - 1) * (m + 1) + 1) = 1 := by
    have he : (m - 1) * (m + 1) + 1 = 2 ^ (d.n + 3) * 2 ^ (d.n + 1) := by
      have hsub := Nat.sub_add_cancel hm
      dsimp [m] at hsub ⊢
      have htwo : 2 ^ (d.n + 3) * 2 ^ (d.n + 1) = 2 ^ (d.n + 2) * 2 ^ (d.n + 2) := by ring
      rw [htwo]
      nlinarith
    rw [he, pow_mul, ← d.a_order, pow_orderOf_eq_one, one_pow]
  apply eq_inv_of_mul_eq_one_left
  calc
    (d.b * d.c * d.a * (d.b * d.c)⁻¹) * d.a =
        (d.b * (d.c * d.a * d.c⁻¹) * d.b⁻¹) * d.a := by group
    _ = (d.b * d.a ^ (m + 1) * d.b⁻¹) * d.a := by rw [d.c_action]
    _ = (d.b * d.a * d.b⁻¹) ^ (m + 1) * d.a := congrArg (fun x : G => x * d.a) (map_pow (MulAut.conj d.b) d.a (m + 1))
    _ = (d.a ^ (m - 1)) ^ (m + 1) * d.a := by rw [d.b_action]
    _ = 1 := by rw [← pow_mul, ← pow_succ]; exact hpow

/-- Every element in the mixed coset inverts the cyclic subgroup. -/
theorem mixed_inverts (i : ℤ) (x : G) (hx : x ∈ zpowers d.a) :
    (d.a ^ i * d.b * d.c) * x * (d.a ^ i * d.b * d.c)⁻¹ = x⁻¹ := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
  have he : (d.b * d.c) * d.a ^ j * (d.b * d.c)⁻¹ = (d.a ^ j)⁻¹ := by
    calc
      _ = ((d.b * d.c) * d.a * (d.b * d.c)⁻¹) ^ j := map_zpow (MulAut.conj (d.b * d.c)) d.a j
      _ = (d.a⁻¹) ^ j := by rw [d.mixed_inverts_generator]
      _ = _ := inv_zpow d.a j
  calc
    _ = d.a ^ i * ((d.b * d.c) * d.a ^ j * (d.b * d.c)⁻¹) * (d.a ^ i)⁻¹ := by group
    _ = d.a ^ i * (d.a ^ j)⁻¹ * (d.a ^ i)⁻¹ := by rw [he]
    _ = _ := by rw [← zpow_neg, ← zpow_neg, ← zpow_add, ← zpow_add]; congr 1; omega

include d in
/-- The marked element is the unique involution of the cyclic subgroup. -/
theorem marked_order : orderOf z = 2 := by
  rw [d.marked]
  have hd : 2 ^ (d.n + 2) ∣ orderOf d.a := by rw [d.a_order, pow_succ]; exact ⟨2, rfl⟩
  rw [orderOf_pow_of_dvd (by positivity) hd, d.a_order, pow_succ,
    Nat.mul_div_cancel_left _ (by positivity)]

/-- Exact outer-involution dichotomy derived from the four normal forms. -/
theorem outer_dichotomy [Finite G] (t : G) (ht : t ∈ T) (hout : t ∉ L) (h2 : t ^ 2 = 1) :
    t = d.c ∨ t = z * d.c ∨ ∀ x ∈ zpowers d.a, t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨i, hi | hi | hi | hi⟩ := d.cover t ht
  · exact (hout (hi ▸ L.zpow_mem d.a_inner i)).elim
  · exact (hout (hi ▸ L.mul_mem (L.zpow_mem d.a_inner i) d.b_inner)).elim
  · have hs := d.exceptional_coset_square i (hi ▸ h2)
    by_cases h1 : d.a ^ i = 1
    · exact Or.inl (by simpa [h1] using hi)
    · have hz : z ∈ zpowers d.a := by simpa only [d.marked] using (zpowers d.a).pow_mem (mem_zpowers d.a) (2 ^ (d.n + 2))
      have he := IsCyclic.eq_of_orderOf_eq_two
        (x := (⟨d.a ^ i, zpow_mem (mem_zpowers _) i⟩ : zpowers d.a))
        (y := (⟨z, hz⟩ : zpowers d.a))
        (by simpa only [orderOf_mk] using orderOf_eq_prime hs h1)
        (by simpa only [orderOf_mk] using d.marked_order)
      exact Or.inr (Or.inl (hi.trans (congrArg (fun x : G => x * d.c) (congrArg Subtype.val he))))
  · exact Or.inr (Or.inr (by rw [hi]; exact d.mixed_inverts i))

/-- The four displayed normal forms bound the literal relative index. -/
theorem core_relIndex [Finite G] : (zpowers d.a).relIndex T ≤ 4 := by
  let C := zpowers d.a
  have hCT : C ≤ T := zpowers_le.mpr d.a_mem
  let rep : Fin 4 → T := ![1, ⟨d.b, d.b_mem⟩, ⟨d.c, d.c_mem⟩,
    ⟨d.b * d.c, T.mul_mem d.b_mem d.c_mem⟩]
  let f : C × Fin 4 → T := fun v => ⟨v.1.val, hCT v.1.property⟩ * rep v.2
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨i, hi | hi | hi | hi⟩ := d.cover t t.property
    · refine ⟨(⟨d.a ^ i, zpow_mem (mem_zpowers _) i⟩, 0), ?_⟩
      apply Subtype.ext
      simpa [f, rep] using hi.symm
    · refine ⟨(⟨d.a ^ i, zpow_mem (mem_zpowers _) i⟩, 1), ?_⟩
      apply Subtype.ext
      simpa [f, rep] using hi.symm
    · refine ⟨(⟨d.a ^ i, zpow_mem (mem_zpowers _) i⟩, 2), ?_⟩
      apply Subtype.ext
      simpa [f, rep] using hi.symm
    · refine ⟨(⟨d.a ^ i, zpow_mem (mem_zpowers _) i⟩, 3), ?_⟩
      apply Subtype.ext
      simpa [f, rep, mul_assoc] using hi.symm
  have hcard : Nat.card T ≤ Nat.card C * 4 := by
    simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_surjective f hf
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) C T bot_le hCT
  simp only [relIndex_bot_left] at hm
  have hp : 0 < Nat.card C := Nat.card_pos
  change C.relIndex T ≤ 4
  nlinarith

/-- The inner elements use precisely the first two normal forms. -/
theorem inner_cover (t : G) (ht : t ∈ T) (hL : t ∈ L) :
    ∃ i : ℤ, t = d.a ^ i ∨ t = d.a ^ i * d.b := by
  obtain ⟨i, hi | hi | hi | hi⟩ := d.cover t ht
  · exact ⟨i, Or.inl hi⟩
  · exact ⟨i, Or.inr hi⟩
  · have h := L.mul_mem (L.inv_mem (L.zpow_mem d.a_inner i)) hL
    rw [hi, inv_mul_cancel_left] at h
    exact (d.c_outer h).elim
  · have h := L.mul_mem (L.inv_mem (L.mul_mem (L.zpow_mem d.a_inner i) d.b_inner)) hL
    rw [hi, inv_mul_cancel_left] at h
    exact (d.c_outer h).elim

private theorem fixes_marked [Finite G] (u : G) (k : ℕ)
    (hu : u * d.a * u⁻¹ = d.a ^ k) : Commute u z := by
  have hzC : z ∈ zpowers d.a := by
    simpa only [d.marked] using (zpowers d.a).pow_mem (mem_zpowers d.a) (2 ^ (d.n + 2))
  have hconj : u * z * u⁻¹ = (d.a ^ k) ^ (2 ^ (d.n + 2)) := by
    calc
      u * z * u⁻¹ = u * d.a ^ (2 ^ (d.n + 2)) * u⁻¹ := congrArg (fun x : G => u * x * u⁻¹) d.marked
      _ = (u * d.a * u⁻¹) ^ (2 ^ (d.n + 2)) := map_pow (MulAut.conj u) d.a _
      _ = _ := by rw [hu]
  have huC : u * z * u⁻¹ ∈ zpowers d.a := by
    rw [hconj]
    exact pow_mem (pow_mem (mem_zpowers _) _) _
  have horder : orderOf (u * z * u⁻¹) = 2 :=
    ((MulAut.conj u).orderOf_eq z).trans d.marked_order
  have he := IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨u * z * u⁻¹, huC⟩ : zpowers d.a)) (y := (⟨z, hzC⟩ : zpowers d.a))
    (by simpa only [orderOf_mk] using horder)
    (by simpa only [orderOf_mk] using d.marked_order)
  exact (mul_inv_eq_iff_eq_mul).mp (congrArg Subtype.val he)

include d in
/-- The normal forms and odd actions centralize the marked involution. -/
theorem marked_centralized [Finite G] : T ≤ centralizer ({z} : Set G) := by
  have ha : Commute d.a z := by
    simpa only [d.marked] using Commute.self_pow d.a (2 ^ (d.n + 2))
  have hb : Commute d.b z := d.fixes_marked d.b _ d.b_action
  have hc : Commute d.c z := d.fixes_marked d.c _ d.c_action
  intro t ht
  apply mem_centralizer_singleton_iff.mpr
  obtain ⟨i, hi | hi | hi | hi⟩ := d.cover t ht
  · rw [hi]; exact ha.zpow_left i
  · rw [hi]; exact (ha.zpow_left i).mul_left hb
  · rw [hi]; exact (ha.zpow_left i).mul_left hc
  · rw [hi]; exact ((ha.zpow_left i).mul_left hb).mul_left hc

/-- Pull the literal coordinates back through a faithful homomorphism. The
marked inner and Sylow subgroups are the actual images, not abstract copies. -/
theorem of_map {H : Type*} [Group H] (f : G →* H) (hf : Function.Injective f)
    (d' : CyclicByFourCoordinates (L.map f) (T.map f) (f z)) :
    Nonempty (CyclicByFourCoordinates L T z) := by
  obtain ⟨a, haT, ha⟩ := mem_map.mp d'.a_mem
  obtain ⟨b, hbT, hb⟩ := mem_map.mp d'.b_mem
  obtain ⟨c, hcT, hc⟩ := mem_map.mp d'.c_mem
  have hin (x y : G) (hxy : f x = f y) : x = y := hf hxy
  have haL : a ∈ L := by
    obtain ⟨a', haL, hae⟩ := mem_map.mp d'.a_inner
    exact hin a' a (hae.trans ha.symm) ▸ haL
  have hbL : b ∈ L := by
    obtain ⟨b', hbL, hbe⟩ := mem_map.mp d'.b_inner
    exact hin b' b (hbe.trans hb.symm) ▸ hbL
  refine ⟨{
    a := a
    b := b
    c := c
    n := d'.n
    a_order := ?_
    a_inner := haL
    a_mem := haT
    b_inner := hbL
    b_mem := hbT
    c_mem := hcT
    c_outer := ?_
    c_sq := ?_
    b_action := ?_
    c_action := ?_
    marked := ?_
    cover := ?_ }⟩
  · rw [← orderOf_injective f hf a, ha]
    exact d'.a_order
  · intro h
    exact d'.c_outer (hc ▸ mem_map_of_mem f h)
  · apply hf
    simpa only [map_pow, map_one, hc] using d'.c_sq
  · apply hf
    simpa only [map_mul, map_inv, map_pow, ha, hb] using d'.b_action
  · apply hf
    simpa only [map_mul, map_inv, map_pow, ha, hc] using d'.c_action
  · apply hf
    simpa only [map_pow, ha] using d'.marked
  · intro t ht
    obtain ⟨i, hi | hi | hi | hi⟩ := d'.cover (f t) (mem_map_of_mem f ht)
    · exact ⟨i, Or.inl (hf (by simpa only [map_zpow, ha] using hi))⟩
    · exact ⟨i, Or.inr (Or.inl (hf (by simpa only [map_mul, map_zpow, ha, hb] using hi)))⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inl (hf (by simpa only [map_mul, map_zpow, ha, hc] using hi))))⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inr (hf (by simpa only [map_mul, map_zpow, ha, hb, hc] using hi))))⟩

end CyclicByFourCoordinates
end Theory.GroupTheory
