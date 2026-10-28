module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.NormNum

/-!
# Compatible normalizer generators in Janko's recognition argument

For a group of order 443520 with element orders among 1, 2, 3, 4, 5, 6,
7, 8 and 11, the cyclic subgroups of orders 5 and 11 are self-centralizing.
A commuting element of coprime order would otherwise give a forbidden
product order. Their normalizer actions have kernels of orders 5 and 11;
Sylow congruences force image orders 4 and 5, hence normalizer orders 20
and 55.

The order-five normalizer realizes squaring. In the order-eleven case,
the action image has index two in the automorphism group, so it contains
the square of the squaring automorphism, which is fourth powering. The
spectrum then determines the orders of the lifts. We construct the 11:5
pair first and apply the order-five result to that same element `m`.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, Lemma 15, p.16, and Section 9, p.17,
DOI 10.1016/0021-8693(68)90002-1. Relations use left conjugation, as in
`M22Identification.PermutationData`; the source uses right actions.
The argument is independent of character theory and of recognition results.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction
variable {G : Type*} [Group G] [Finite G]

private theorem centralizer_eq_zpowers
    (hcard : Nat.card G = 443520)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    {p : ℕ} (hp : p = 5 ∨ p = 11) (x : G) (hx : orderOf x = p) :
    centralizer (zpowers x : Set G) = zpowers x := by
  let : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  let C := centralizer (zpowers x : Set G)
  have hC : IsPGroup p C := by
    apply IsPGroup.iff_orderOf.mpr
    intro y
    have hy : orderOf y = orderOf (y : G) := (orderOf_injective C.subtype C.subtype_injective y).symm
    by_cases he : orderOf (y : G) = p
    · exact ⟨1, by simpa only [pow_one, hy] using he⟩
    have hs := horders (y : G)
    have hcop : (orderOf x).Coprime (orderOf (y : G)) := by
      rw [hx]
      rcases hp with rfl | rfl <;>
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs <;>
        rcases hs with h | h | h | h | h | h | h | h | h <;>
        simp_all <;> decide
    have hc : Commute x (y : G) := y.property x (mem_zpowers x)
    have hm := horders (x * (y : G))
    rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hx] at hm
    have ho : orderOf (y : G) = 1 := by
      rcases hp with rfl | rfl <;>
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs hm <;> omega
    exact ⟨0, by simpa only [pow_zero, hy] using ho⟩
  obtain ⟨k, hk⟩ := hC.exists_card_eq
  have hCdvd : Nat.card C ∣ p := by
    have hd : Nat.card C ∣ 443520 := hcard ▸ C.card_subgroup_dvd_card
    rcases hp with rfl | rfl
    · have hc : (Nat.card C).Coprime 88704 := by
        rw [hk]
        exact (by decide : Nat.Coprime 5 88704).pow_left k
      exact hc.dvd_of_dvd_mul_right (show Nat.card C ∣ 5 * 88704 from hd)
    · have hc : (Nat.card C).Coprime 40320 := by
        rw [hk]
        exact (by decide : Nat.Coprime 11 40320).pow_left k
      exact hc.dvd_of_dvd_mul_right (show Nat.card C ∣ 11 * 40320 from hd)
  apply (eq_of_le_of_card_ge (le_centralizer (zpowers x)) ?_).symm
  rw [Nat.card_zpowers, hx]
  exact Nat.le_of_dvd (by rcases hp with rfl | rfl <;> decide) hCdvd

private theorem normalizer_image_card
    (hcard : Nat.card G = 443520)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    {p : ℕ} (hp : p = 5 ∨ p = 11) (x : G) (hx : orderOf x = p) :
    Nat.card (zpowers x).normalizerMonoidHom.range = if p = 5 then 4 else 5 := by
  let : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  let P := zpowers x
  let N := normalizer (P : Set G)
  let f := P.normalizerMonoidHom
  have hP : Nat.card P = p := (Nat.card_zpowers x).trans hx
  have hker : Nat.card f.ker = p := by
    rw [normalizerMonoidHom_ker, centralizer_eq_zpowers hcard horders hp x hx,
      Nat.card_congr (subgroupOfEquivOfLe P.le_normalizer).toEquiv, hP]
  have hrange : Nat.card f.range ∣ p - 1 := by
    have hh := f.range.card_subgroup_dvd_card
    rwa [IsCyclic.card_mulAut, hP, Nat.totient_prime Fact.out] at hh
  have hN : p * Nat.card f.range = Nat.card N := by
    simpa only [index_ker, hker] using f.ker.card_mul_index
  have hi := N.card_mul_index
  rw [← hN, hcard] at hi
  have hpi : ¬ p ∣ P.index := by
    have hh := P.card_mul_index
    rw [hP, hcard] at hh
    rcases hp with rfl | rfl <;> omega
  let S : Sylow p G := (IsPGroup.of_card (hP.trans (pow_one p).symm)).toSylow hpi
  have hm := card_sylow_modEq_one p G
  rw [S.card_eq_index_normalizer] at hm
  change N.index % p = 1 % p at hm
  change Nat.card f.range = if p = 5 then 4 else 5
  rcases hp with rfl | rfl
  · have hd := Nat.mem_divisors.mpr ⟨hrange, by decide⟩
    rw [show (5 - 1 : ℕ).divisors = {1, 2, 4} by decide] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hd | hd | hd <;> rw [hd] at hi ⊢ <;> norm_num at hi hm ⊢ <;> omega
  · have hd := Nat.mem_divisors.mpr ⟨hrange, by decide⟩
    rw [show (11 - 1 : ℕ).divisors = {1, 2, 5, 10} by decide] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hd | hd | hd | hd <;> rw [hd] at hi ⊢ <;> norm_num at hi hm ⊢ <;> omega

private noncomputable def squareAut (x : G) (hc : (orderOf x).Coprime 2) :
    MulAut (zpowers x) :=
  let _ := IsCyclic.commGroup (α := zpowers x)
  MulEquiv.mk' (powCoprime (by simpa only [Nat.card_zpowers] using hc))
    (fun a b => mul_pow a b 2)

omit [Finite G] in
private theorem squareAut_apply (x : G) (hc : (orderOf x).Coprime 2) (a : zpowers x) :
    squareAut x hc a = a ^ 2 := rfl

private theorem exists_power_conjugator
    (hcard : Nat.card G = 443520)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    {p : ℕ} (hp : p = 5 ∨ p = 11) (x : G) (hx : orderOf x = p) :
    ∃ y : normalizer (zpowers x : Set G),
      (y : G) * x * (y : G)⁻¹ = x ^ (if p = 5 then 2 else 4) := by
  let P := zpowers x
  let f := P.normalizerMonoidHom
  let e := squareAut x (by rw [hx]; rcases hp with rfl | rfl <;> decide)
  have hR := normalizer_image_card hcard horders hp x hx
  change Nat.card f.range = _ at hR
  have hA : Nat.card (MulAut P) = p - 1 := by
    rw [IsCyclic.card_mulAut, Nat.card_zpowers, hx]
    exact Nat.totient_prime (by rcases hp with rfl | rfl <;> decide)
  rcases hp with rfl | rfl
  · have htop : f.range = ⊤ := f.range.eq_top_of_card_eq (by simpa [hA] using hR)
    obtain ⟨y, hy⟩ := (MonoidHom.range_eq_top.mp htop) e
    refine ⟨y, ?_⟩
    have hh := congrArg (fun a : MulAut P => (a ⟨x, mem_zpowers x⟩ : G)) hy
    exact hh
  · have hi := f.range.card_mul_index
    rw [hR, hA] at hi
    have hindex : f.range.index = 2 := by norm_num at hi; omega
    obtain ⟨y, hy⟩ := f.range.sq_mem_of_index_two hindex e
    refine ⟨y, ?_⟩
    have hh := congrArg (fun a : MulAut P => (a ⟨x, mem_zpowers x⟩ : G)) hy
    change (y : G) * x * (y : G)⁻¹ = ((e ^ 2) ⟨x, mem_zpowers x⟩ : G) at hh
    rw [pow_two, MulAut.mul_apply] at hh
    simpa only [e, squareAut_apply, Subgroup.coe_pow,
      ← pow_mul, Nat.reduceMul, show ¬(11 : ℕ) = 5 by decide, if_false] using hh

omit [Finite G] in
private theorem power_conjugation_mod {x y : G} {k : ℕ}
    (h : y * x * y⁻¹ = x ^ k) : k ^ orderOf y ≡ 1 [MOD orderOf x] := by
  have hi (r : ℕ) : (MulAut.conj y ^ r) x = x ^ (k ^ r) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_pow]
      change (y * x * y⁻¹) ^ (k ^ r) = _
      rw [h, ← pow_mul, pow_succ']
  have hh := hi (orderOf y)
  rw [← map_pow, pow_orderOf_eq_one, map_one, MulAut.one_apply] at hh
  exact pow_eq_pow_iff_modEq.mp (hh.symm.trans (pow_one x).symm)

/-- Every element of order five has an order-four conjugator acting by squaring.
The universal choice of `m` is what makes the final two relations compatible. -/
public theorem exists_four_conjugating_five
    (hcard : Nat.card G = 443520)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    (m : G) (hm : orderOf m = 5) :
    ∃ n : G, orderOf n = 4 ∧ n * m * n⁻¹ = m ^ 2 := by
  obtain ⟨n, hn⟩ := exists_power_conjugator hcard horders (Or.inl rfl) m hm
  change (n : G) * m * (n : G)⁻¹ = m ^ 2 at hn
  refine ⟨n, ?_, hn⟩
  have hmod := power_conjugation_mod hn
  rw [hm] at hmod
  have hker : Nat.card (zpowers m).normalizerMonoidHom.ker = 5 := by
    rw [normalizerMonoidHom_ker, centralizer_eq_zpowers hcard horders (Or.inl rfl) m hm,
      Nat.card_congr (subgroupOfEquivOfLe (zpowers m).le_normalizer).toEquiv,
      Nat.card_zpowers, hm]
  have hN := (zpowers m).normalizerMonoidHom.ker.card_mul_index
  rw [index_ker, hker, normalizer_image_card hcard horders (Or.inl rfl) m hm] at hN
  have hd : orderOf (n : G) ∣ 20 := by
    have he : orderOf (n : G) = orderOf n :=
      orderOf_injective (normalizer (zpowers m : Set G)).subtype Subtype.val_injective n
    rw [he]
    simpa [← hN] using orderOf_dvd_natCard n
  have hs := horders (n : G)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h | h | h | h | h | h | h | h | h
  all_goals solve
    | exact h
    | norm_num [h, Nat.ModEq] at hmod
    | norm_num [h] at hd

/-- Every element of order eleven has an order-five conjugator acting by
fourth powering. -/
public theorem exists_five_conjugating_eleven
    (hcard : Nat.card G = 443520)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    (ell : G) (hell : orderOf ell = 11) :
    ∃ m : G, orderOf m = 5 ∧ m * ell * m⁻¹ = ell ^ 4 := by
  obtain ⟨m, hm⟩ := exists_power_conjugator hcard horders (Or.inr rfl) ell hell
  change (m : G) * ell * (m : G)⁻¹ = ell ^ 4 at hm
  refine ⟨m, ?_, hm⟩
  have hmod := power_conjugation_mod hm
  rw [hell] at hmod
  have hs := horders (m : G)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h | h | h | h | h | h | h | h | h
  all_goals solve
    | exact h
    | norm_num [h, Nat.ModEq] at hmod

/-- The compatible 11:5 and 5:4 generators required by Janko's final action
argument. Only the stated order and spectrum inputs are needed from that proof. -/
public theorem exists_normalizer_generators [IsSimpleGroup G]
    (hcard : Nat.card G = 443520)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ)) :
    ∃ ell m n : G, orderOf ell = 11 ∧ orderOf m = 5 ∧ orderOf n = 4 ∧
      m * ell * m⁻¹ = ell ^ 4 ∧ n * m * n⁻¹ = m ^ 2 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨ell, hell⟩ := exists_prime_orderOf_dvd_card' (G := G) 11 (by rw [hcard]; decide)
  obtain ⟨m, hm, hmell⟩ := exists_five_conjugating_eleven hcard horders ell hell
  obtain ⟨n, hn, hnm⟩ := exists_four_conjugating_five hcard horders m hm
  exact ⟨ell, m, n, hell, hm, hn, hmell, hnm⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction
