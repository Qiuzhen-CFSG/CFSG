module

public import Theory.GroupTheory.PerfectCentralCoverTorusNormalizer

/-!
# Odd Sylow geometry controlling perfect central kernels

For two commuting generators, conjugation by an ambient element acts on
their lifted commutator by the product of its two power exponents. The
commutator is central and hence also fixed. Coprimality with the order
of the first generator forces that commutator to vanish. This gives an
abelian full torus preimage in every central extension.

Central Sylow transfer then excludes the corresponding kernel prime,
either directly or through an abelian-by-cyclic Sylow normalizer. All
geometric witnesses refer to elements of the base group; they assume
nothing about a cover or its multiplier. Concrete triality witnesses
remain separate obligations.

Source: the nondefining-characteristic multiplier calculation summarized
in GLS3 §6.1, and central transfer as in Aschbacher--Smith I.1.1--2.
-/

public section

open Subgroup
open scoped commutatorElement

namespace PerfectCentralCovering.OddSylow

private theorem commutator_pow_left {E : Type*} [Group E] (a b : E)
    (hc : ⁅a, b⁆ ∈ center E) (k : ℕ) : ⁅a ^ k, b⁆ = ⁅a, b⁆ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, commutatorElement_mul_left_eq_conj_mul,
      mem_center_iff.mp hc (a ^ k), mul_inv_cancel_right, ih, pow_succ']

private theorem commutator_pow_right {E : Type*} [Group E] (a b : E)
    (hc : ⁅a, b⁆ ∈ center E) (k : ℕ) : ⁅a, b ^ k⁆ = ⁅a, b⁆ ^ k := by
  have hc' : ⁅b, a⁆ ∈ center E := by
    rw [← commutatorElement_inv]
    exact (center E).inv_mem hc
  calc
    ⁅a, b ^ k⁆ = ⁅b ^ k, a⁆⁻¹ := (commutatorElement_inv (b ^ k) a).symm
    _ = (⁅b, a⁆ ^ k)⁻¹ := congrArg Inv.inv (commutator_pow_left b a hc' k)
    _ = ⁅a, b⁆ ^ k := by rw [← inv_pow, commutatorElement_inv]

/-- Diagonal power conjugation annihilates the lifted alternating pairing
when its determinant minus one is coprime to an exponent of the first generator. -/
theorem commute_lifts_of_power_conjugation {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (x y s : G) (m i j : ℕ) (hpos : 0 < i * j)
    (hcop : m.Coprime (i * j - 1)) (hx : x ^ m = 1) (hxy : Commute x y)
    (hsx : s * x * s⁻¹ = x ^ i) (hsy : s * y * s⁻¹ = y ^ j)
    (a b : E) (ha : f a = x) (hb : f b = y) : Commute a b := by
  have hc : ⁅a, b⁆ ∈ center E := hk (by
    rw [MonoidHom.mem_ker, map_commutatorElement, ha, hb]
    exact hxy.commutator_eq)
  obtain ⟨t, ht⟩ := hf s
  have he : ⁅a, b⁆ = ⁅a ^ i, b ^ j⁆ := by
    calc
      ⁅a, b⁆ = t * ⁅a, b⁆ * t⁻¹ := by
        rw [mem_center_iff.mp hc t, mul_inv_cancel_right]
      _ = ⁅t * a * t⁻¹, t * b * t⁻¹⁆ := conjugate_commutatorElement _ _ _
      _ = ⁅a ^ i, b ^ j⁆ := CentralExtension.commutator_eq_of_image_eq f hk
        (by simp only [map_mul, map_inv, map_pow, ht, ha, hsx])
        (by simp only [map_mul, map_inv, map_pow, ht, hb, hsy])
  have hci : ⁅a ^ i, b⁆ ∈ center E := by
    rw [commutator_pow_left a b hc i]
    exact (center E).pow_mem hc i
  rw [commutator_pow_right (a ^ i) b hci j,
    commutator_pow_left a b hc i, ← pow_mul] at he
  have hdet : ⁅a, b⁆ ^ (i * j - 1) = 1 := by
    rw [pow_sub _ hpos, pow_one, ← he, mul_inv_cancel]
  have hm : ⁅a, b⁆ ^ m = 1 := by
    rw [← commutator_pow_left a b hc m]
    apply Commute.commutator_eq
    exact (mem_center_iff.mp (hk (by
      rw [MonoidHom.mem_ker, map_pow, ha, hx])) b).symm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hdet))

/-- Actual commuting generators with diagonal conjugation detecting their
alternating pairing. The exponents need not be equal and may encode a reflection. -/
structure TorusPair {G : Type*} [Group G] (T : Subgroup G) where
  left : G
  right : G
  actor : G
  generates : closure ({left, right} : Set G) = T
  commute : Commute left right
  exponent : ℕ
  leftPower : ℕ
  rightPower : ℕ
  positive : 0 < leftPower * rightPower
  coprime : exponent.Coprime (leftPower * rightPower - 1)
  pow_eq_one : left ^ exponent = 1
  conjugate_left : actor * left * actor⁻¹ = left ^ leftPower
  conjugate_right : actor * right * actor⁻¹ = right ^ rightPower

/-- These base-group equations make the literal full torus preimage abelian. -/
theorem TorusPair.abelian_preimage {E G : Type*} [Group E] [Group G]
    {T : Subgroup G} (d : TorusPair T) (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    IsMulCommutative (T.comap f) := by
  obtain ⟨a, ha⟩ := hf d.left
  obtain ⟨b, hb⟩ := hf d.right
  have hab := commute_lifts_of_power_conjugation f hf hk d.left d.right d.actor
    d.exponent d.leftPower d.rightPower d.positive d.coprime d.pow_eq_one
    d.commute d.conjugate_left d.conjugate_right a b ha hb
  exact CentralExtension.isMulCommutative_comap_of_pair_lifts f hk T a b hab
    (by simpa only [ha, hb] using d.generates)

/-- Local geometry sufficient for odd-primary central transfer. In the
last alternative normality is relative to the displayed Sylow subgroup. -/
inductive Geometry (p : ℕ) (G : Type*) [Group G] : Prop
  | cyclic (h : ∀ Q : Sylow p G, IsCyclic Q) : Geometry p G
  | torus (Q : Sylow p G) (d : TorusPair (Q : Subgroup G)) : Geometry p G
  | normalizer (Q : Sylow p G) (T : Subgroup G) (d : TorusPair T) (c r : G)
      (generates : T ⊔ zpowers c = (Q : Subgroup G))
      (normalizes : c ∈ normalizer (T : Set G))
      (inverts : ∀ t ∈ T, r * t * r⁻¹ = t⁻¹)
      (fixes : Commute r c) : Geometry p G

/-- Every finite perfect central cover satisfies the prime exclusion
deduced from the specified base-group Sylow geometry. -/
theorem Geometry.not_dvd_card_kernel {E G : Type*} [Group E] [Finite E]
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h : Geometry p G) (f : Cover E G) : ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Group.IsPerfect E := f.isPerfect
  cases h with
  | cyclic h => exact f.not_dvd_card_multiplier_of_isCyclic_sylow h
  | torus Q d =>
    exact not_dvd_card_kernel_of_abelian_sylow_preimage f.toMonoidHom f.surjective
      f.ker_le_center Q (d.abelian_preimage f.toMonoidHom f.surjective f.ker_le_center)
  | normalizer Q T d c r hQ hc hr hrc =>
    exact not_dvd_card_kernel_of_torus_normalizer f.toMonoidHom f.surjective
      f.ker_le_center hp Q T c r hQ hc
      (d.abelian_preimage f.toMonoidHom f.surjective f.ker_le_center) hr hrc

/-- Primes outside the actual group order require no torus calculation. -/
theorem geometry_of_not_dvd_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ Nat.card G) : Geometry p G := by
  apply Geometry.cyclic
  intro Q
  have hcard : Nat.card Q = 1 := Q.isPGroup'.card_eq_or_dvd.resolve_right
    (fun h => hp (h.trans (card_subgroup_dvd_card (Q : Subgroup G))))
  let : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact isCyclic_of_subsingleton

/-- A prime occurring at most once in the group order has cyclic Sylow
subgroups, so needs no additional normalizer calculation. -/
theorem geometry_of_not_square_dvd_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : ¬ p ^ 2 ∣ Nat.card G) : Geometry p G := by
  apply Geometry.cyclic
  intro Q
  obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
  have hle : k ≤ 1 := by
    by_contra h
    apply hp
    apply dvd_trans _ (card_subgroup_dvd_card (Q : Subgroup G))
    rw [hk]
    exact pow_dvd_pow p (by omega)
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hk]
  simpa only [pow_one] using pow_dvd_pow p hle

/-- It is enough to construct the local geometry at odd prime divisors
of the base group. No universal cover, simplicity or kernel bound is an input. -/
theorem kernel_isTwoGroup {E G : Type*} [Group E] [Finite E]
    [Group G] [Finite G] (f : Cover E G)
    (hlocal : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ∣ Nat.card G → Geometry p G) :
    IsPGroup 2 f.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpprime, hpdiv, _⟩ := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra hp2
    let : Fact p.Prime := ⟨hpprime⟩
    have h : Geometry p G := by
      by_cases hcard : p ∣ Nat.card G
      · exact hlocal p hp2 hcard
      · exact geometry_of_not_dvd_card hcard
    exact h.not_dvd_card_kernel hp2 f hpdiv
  subst p
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩

end PerfectCentralCovering.OddSylow
