module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.Basic
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.PGroup.NormalChain


/-!
# Three-subgroup control of the odd-core commutator

For an order-two subgroup A of a finite solvable group G, write Q = O₂′(G).
Assume that every noncentral conjugate pair has odd intersection of order
three. Then [Q,A] is a three-group normal in Q, and every such intersection
is subnormal in Q. All subgroups use the literal left-conjugate pair from
`BlockConstruction.Basic`; normality and subnormality are relative to Q.

A nonidentity commutator [x,a] generates the cubic pair intersection.
Consequently that intersection lies in [Q,A], and it lies in every
A-normalized subgroup containing x. In particular a noncentral invariant
r-subgroup forces r = 3. For the global step, solvability permits the
invariant Hall version of the source's invariant-Sylow argument: an
A-invariant Hall 3′-subgroup of Q centralizes A. Coprime Hall action puts
[Q,A] in the three-core of Q. Finally every subgroup of a finite three-group
is subnormal, and its normal inclusion in Q completes the chain.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, 9.3.4,
printed p.242 / PDF p.255 of `refs/original/kurzweil.pdf`, specialized to
p = 2. The order-three pair input remains explicit; its producer is 9.3.3.
`OddCommutators.Support` applies this result to the actual support assembly.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
variable {G : Type*} [Group G]

private theorem pair_odd_le_of_commutators_le (A H : Subgroup G)
    {x : G} (hx : x ∈ pPrimeCore 2 G)
    (hxc : x ∉ centralizer (A : Set G))
    (hcard : Nat.card ↥(conjugatePair A x ⊓ pPrimeCore 2 G) = 3)
    (hcomm : ∀ a ∈ A, ⁅x, a⁆ ∈ H) :
    conjugatePair A x ⊓ pPrimeCore 2 G ≤ H := by
  classical
  obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, ⁅x, a⁆ ≠ 1 := by
    by_contra! hall
    apply hxc
    intro a ha
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hall a ha)).symm
  let L := conjugatePair A x ⊓ pPrimeCore 2 G
  have hcL : ⁅x, a⁆ ∈ L := by
    refine ⟨?_, commutator_le_left _ _ (commutator_mem_commutator hx ha)⟩
    have hc : x * a * x⁻¹ ∈ conjugatePair A x :=
      (le_sup_right : A.map (MulAut.conj x).toMonoidHom ≤ conjugatePair A x)
        (mem_map_of_mem _ ha)
    exact (conjugatePair A x).mul_mem hc
      ((conjugatePair A x).inv_mem ((le_sup_left : A ≤ conjugatePair A x) ha))
  let : Fact (Nat.card L).Prime := ⟨by rw [show Nat.card L = 3 from hcard]; decide⟩
  have htop : H.subgroupOf L = ⊤ := by
    apply (H.subgroupOf L).eq_bot_or_eq_top_of_prime_card.resolve_left
    intro he
    have hc : (⟨⁅x, a⁆, hcL⟩ : L) ∈ H.subgroupOf L := hcomm a ha
    rw [he, mem_bot] at hc
    exact hne (congrArg Subtype.val hc)
  exact subgroupOf_eq_top.mp htop

/-- The odd part of a noncentral pair lies in the actual odd-core commutator. -/
theorem pair_odd_le_commutator (A : Subgroup G)
    {x : G} (hx : x ∈ pPrimeCore 2 G)
    (hxc : x ∉ centralizer (A : Set G))
    (hcard : Nat.card ↥(conjugatePair A x ⊓ pPrimeCore 2 G) = 3) :
    conjugatePair A x ⊓ pPrimeCore 2 G ≤ ⁅pPrimeCore 2 G, A⁆ :=
  pair_odd_le_of_commutators_le A _ hx hxc hcard
    (fun _ ha => commutator_mem_commutator hx ha)

/-- Normalized overgroups of the conjugator contain the cubic odd subgroup. -/
theorem pair_odd_le_normalized (A R : Subgroup G)
    (hAR : A ≤ normalizer (R : Set G))
    {x : G} (hx : x ∈ pPrimeCore 2 G) (hxR : x ∈ R)
    (hxc : x ∉ centralizer (A : Set G))
    (hcard : Nat.card ↥(conjugatePair A x ⊓ pPrimeCore 2 G) = 3) :
    conjugatePair A x ⊓ pPrimeCore 2 G ≤ R :=
  pair_odd_le_of_commutators_le A R hx hxc hcard
    (fun _ ha => (le_normalizer_iff_commutator_le_left.mp hAR)
      (commutator_mem_commutator hxR ha))

/-- Normality here is relative to the odd core, with no ambient normality claim. -/
theorem odd_commutator_normal (A : Subgroup G) :
    ((⁅pPrimeCore 2 G, A⁆).subgroupOf (pPrimeCore 2 G)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (commutator_le_left _ _)).mpr
    (normalizer_commutator_ge_left _ _)

private theorem normalized_threePrime_le_centralizer (A R : Subgroup G)
    (hRQ : R ≤ pPrimeCore 2 G) (hAR : A ≤ normalizer (R : Set G))
    (hR : ¬ 3 ∣ Nat.card R)
    (hpairCard : ∀ x ∈ pPrimeCore 2 G, x ∉ centralizer (A : Set G) →
      Nat.card ↥(conjugatePair A x ⊓ pPrimeCore 2 G) = 3) :
    R ≤ centralizer (A : Set G) := by
  intro x hx
  by_contra hxc
  have hle := pair_odd_le_normalized A R hAR (hRQ hx) hx hxc
    (hpairCard x (hRQ hx) hxc)
  have hd := card_dvd_of_le hle
  rw [hpairCard x (hRQ hx) hxc] at hd
  exact hR hd

variable [Finite G]

/-- A noncentral normalized prime subgroup of the odd core has prime three. -/
theorem prime_eq_three_of_normalized_noncentral (A R : Subgroup G)
    {r : ℕ} [Fact r.Prime] (hR : IsPGroup r R)
    (hRQ : R ≤ pPrimeCore 2 G) (hAR : A ≤ normalizer (R : Set G))
    (hnc : ¬ R ≤ centralizer (A : Set G))
    (hpairCard : ∀ x ∈ pPrimeCore 2 G, x ∉ centralizer (A : Set G) →
      Nat.card ↥(conjugatePair A x ⊓ pPrimeCore 2 G) = 3) : r = 3 := by
  have hd : 3 ∣ Nat.card R := by
    by_contra hn
    exact hnc (normalized_threePrime_le_centralizer A R hRQ hAR hn hpairCard)
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [hn] at hd
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
    (Nat.prime_three.dvd_of_dvd_pow hd)).symm

/-- The pair-cardinality input forces the odd-core commutator to be a three-group. -/
theorem odd_commutator_isPGroup (hsolv : Group.IsSolvable G)
    (A : Subgroup G) (hA : Nat.card A = 2)
    (hpairCard : ∀ x ∈ pPrimeCore 2 G, x ∉ centralizer (A : Set G) →
      Nat.card ↥(conjugatePair A x ⊓ pPrimeCore 2 G) = 3) :
    IsPGroup 3 ↥⁅pPrimeCore 2 G, A⁆ := by
  let Q := pPrimeCore 2 G
  let : Group.IsSolvable G := hsolv
  have hsolvQ : Group.IsSolvable Q := inferInstance
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Q) := by
    rw [hA]
    exact pPrimeCore_coprime_card
  let π : Set Nat.Primes := {p | p.val = 3}
  obtain ⟨H, hH, hHI⟩ := exists_isHallSubgroup_isInvariant
    (G := Q) (A := A) hsolvQ hcop {p | p ∉ π}
  have hfixed : H ≤ fixedPointSubgroup A Q := by
    let R := H.map Q.subtype
    have hRQ : R ≤ Q := map_subtype_le H
    have hAR : A ≤ normalizer (R : Set G) := by
      intro a ha
      apply mem_normalizer_iff.mpr
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(⟨a, ha⟩ : A) • y, (hHI.invariant ⟨a, ha⟩ y).mp hy, rfl⟩
      · rintro ⟨y, hy, he⟩
        refine ⟨(⟨a⁻¹, A.inv_mem ha⟩ : A) • y,
          (hHI.invariant ⟨a⁻¹, A.inv_mem ha⟩ y).mp hy, ?_⟩
        change a⁻¹ * (y : G) * (a⁻¹)⁻¹ = x
        change (y : G) = a * x * a⁻¹ at he
        rw [he]
        group
    have hR : ¬ 3 ∣ Nat.card R := by
      rw [show Nat.card R = Nat.card H from card_map_of_injective Q.subtype_injective]
      intro hd
      exact hH.p_in_pi_of_p_dvd_card ⟨3, Nat.prime_three⟩ hd rfl
    have hRC := normalized_threePrime_le_centralizer A R hRQ hAR hR hpairCard
    intro x hx a
    apply Subtype.ext
    change (a : G) * (x : G) * (a : G)⁻¹ = x
    have hc := hRC (mem_map_of_mem Q.subtype hx) (a : G) a.property
    change (a : G) * (x : G) = (x : G) * (a : G) at hc
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hle := commutatorAction_le_piCore_of_hall_complement_le_fixedPointSubgroup
    (G := Q) (A := A) hsolvQ hcop π H hH hfixed
  have hthree : IsPGroup 3 (commutatorAction A Q) := by
    apply IsPGroup.of_card
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro r hr hd
    exact piCore_isPiSubgroup π ⟨r, hr⟩ (hd.trans (card_dvd_of_le hle))
  have hm := hthree.map Q.subtype
  rwa [commutatorAction_subgroup_conj_map_eq_commutator Q A
    (le_normalizer_of_normal (H := Q))] at hm

/-- The relative-subnormality premise used by the pair-support assembly. -/
theorem pair_odd_isSubnormal (hsolv : Group.IsSolvable G)
    (A : Subgroup G) (hA : Nat.card A = 2)
    (hpairCard : ∀ x ∈ pPrimeCore 2 G, x ∉ centralizer (A : Set G) →
      Nat.card ↥(conjugatePair A x ⊓ pPrimeCore 2 G) = 3)
    {x : G} (hx : x ∈ pPrimeCore 2 G)
    (hxc : x ∉ centralizer (A : Set G)) :
    ((conjugatePair A x ⊓ pPrimeCore 2 G).subgroupOf (pPrimeCore 2 G)).IsSubnormal := by
  let Q := pPrimeCore 2 G
  let N := (⁅Q, A⁆).subgroupOf Q
  let L := (conjugatePair A x ⊓ Q).subgroupOf Q
  have hLN : L ≤ N := fun _ hy =>
    pair_odd_le_commutator A hx hxc (hpairCard x hx hxc) hy
  have hN : IsPGroup 3 N :=
    (odd_commutator_isPGroup hsolv A hA hpairCard).of_equiv
      (subgroupOfEquivOfLe (commutator_le_left Q A)).symm
  exact Subgroup.IsSubnormal.trans hLN (hN.subgroup_isSubnormal (L.subgroupOf N))
    (odd_commutator_normal A).isSubnormal

end CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
