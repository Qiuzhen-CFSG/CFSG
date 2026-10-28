module
public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.Quasithin.LocalRank
public import Theory.PPrimeCore

/-!
# Large odd-prime subgroups and the actual Frattini action

The local p-rank bound passes to involution centralizers in every subgroup.
If a subgroup Q has p-rank greater than two, its centralizer has odd order.
For normal Q, the action on a supercritical Frattini quotient also has odd
kernel: an involution in the kernel would centralize Q by supercritical
automorphism detection, contradicting the local rank bound.

Source: Aschbacher–Smith, Lemma A.1.28, printed p.26.
-/

open Subgroup
namespace Theory.Quasithin
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- The ambient local-rank bound controls every subgroup involution centralizer. -/
public theorem subgroup_involution_centralizer_primeRank_le
    (hlocal : twoLocalPrimeRank p G ≤ 2) (H : Subgroup G)
    (a : H) (ha : orderOf a = 2) :
    primeRank p (centralizer ({a} : Set H)) ≤ 2 := by
  have hao : orderOf (a : G) = 2 := (orderOf_coe a).trans ha
  let f : centralizer ({a} : Set H) →* centralizer ({(a : G)} : Set G) :=
    H.subtype.restrict (fun x hx => by
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : centralizer ({(a : G)} : Set G) => (z : G)) h))
  exact (Theory.GroupTheory.primeRank_le_of_injective p f hf).trans
    (((Theory.GroupTheory.isTwoLocal_involution_centralizer hao).primeRank_le p).trans hlocal)

omit [Fact p.Prime] in
/-- A subgroup of large p-rank has odd centralizer when involution centralizers
have p-rank at most two. -/
public theorem odd_card_centralizer_of_large_primeRank
    (hlocal : ∀ a : G, orderOf a = 2 → primeRank p (centralizer ({a} : Set G)) ≤ 2)
    (Q : Subgroup G) (hQrank : 2 < primeRank p Q) :
    Odd (Nat.card (centralizer (Q : Set G))) := by
  apply Nat.coprime_two_left.mp
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro hdvd
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (Q : Set G)) 2 hdvd
  have hao : orderOf (a : G) = 2 := (orderOf_coe a).trans ha
  have hle : Q ≤ centralizer ({(a : G)} : Set G) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact mem_centralizer_iff.mp a.property x hx
  exact (not_le_of_gt hQrank) ((Theory.GroupTheory.primeRank_le_of_injective p (inclusion hle) (inclusion_injective hle)).trans (hlocal a hao))

/-- The actual action of a normal large-rank p-subgroup on a supercritical
Frattini quotient has odd kernel. -/
public theorem odd_card_supercritical_frattini_kernel
    (hp : Odd p)
    (hlocal : ∀ a : G, orderOf a = 2 → primeRank p (centralizer ({a} : Set G)) ≤ 2)
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup p Q) (hQrank : 2 < primeRank p Q)
    (X : Subgroup Q) (hX : IsSupercriticalPSubgroup p X) :
    letI : X.Characteristic := hX.characteristic
    Odd (Nat.card ((((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp
      (MulAut.conjNormal : G →* MulAut Q)).ker)) := by
  let : X.Characteristic := hX.characteristic
  let action : G →* MulAut Q := MulAut.conjNormal
  let f := ((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp action
  apply Nat.coprime_two_left.mp
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro hdvd
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 hdvd
  have hao : orderOf (a : G) = 2 := (orderOf_coe a).trans ha
  have hcop : p.Coprime (orderOf (action a)) :=
    hp.coprime_two_right.of_dvd_right (hao ▸ orderOf_map_dvd action a)
  have he := hX.orderOf_frattini_action_eq_of_coprime hQ hp (action a) hcop
  have hfa : quotientAut (frattini X) (MulAut.characteristic X (action a)) = 1 := a.property
  rw [hfa, orderOf_one] at he
  have hact : action a = 1 := orderOf_eq_one_iff.mp he.symm
  have hle : Q ≤ centralizer ({(a : G)} : Set G) := by
    intro x hx
    have hxfix := congrArg (fun b : MulAut Q => (b ⟨x, hx⟩ : G)) hact
    change (a : G) * x * (a : G)⁻¹ = x at hxfix
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun z : G => z * (a : G)) hxfix
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm
  exact (not_le_of_gt hQrank) ((Theory.GroupTheory.primeRank_le_of_injective p (inclusion hle) (inclusion_injective hle)).trans (hlocal a hao))
end Theory.Quasithin
