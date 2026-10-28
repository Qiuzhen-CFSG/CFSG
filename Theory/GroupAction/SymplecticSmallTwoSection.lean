module
public import Theory.GroupAction.ComponentSmallTwoSection
public import Theory.Representation.SymplecticFour.BinaryDegree

/-!
# Symplectic components centralize small two-sections

A prime of binary multiplicative order 4n divides the order of Sp₄(2ⁿ).
Fixed-point counting shows that it cannot divide the automorphism group of
a two-group of order at most 2^(2n). Thus a two-perfect group with this
simple quotient acts trivially on any normalized section of that size.
The section may be nonabelian and need not split off its central kernel.

The graph application is the escaping fixed-Sylow seed in MS93 (3.4),
printed p.868. The primitive-prime input is the proved binary specialization
of GLS2, Chapter A, Theorem 1.1.
-/

public section
open Subgroup

/-- A two-group smaller than the binary degree of a prime has no automorphism
of that prime order. No elementary abelian hypothesis is required. -/
theorem MulAut.not_prime_dvd_card_of_twoGroup_card_bound
    {V : Type*} [Group V] [Finite V] {p m : ℕ}
    (hp : p.Prime) (hV : IsPGroup 2 V) (hcard : Nat.card V ≤ 2 ^ m)
    (horder : m < orderOf (2 : ZMod p)) :
    ¬ p ∣ Nat.card (MulAut V) := by
  let : Fact p.Prime := ⟨hp⟩
  intro hdiv
  obtain ⟨n,hn⟩ := hV.exists_card_eq
  have hnle : n ≤ m := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hcard
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p hdiv
  let P := zpowers a
  have hP : Nat.card P = p := by rw [Nat.card_zpowers,ha]
  have hgroup : IsPGroup p P := IsPGroup.of_card (n := 1) (by simpa using hP)
  let D := FixedPoints.subgroup P V
  have hmod := hgroup.card_modEq_card_fixedPoints V
  change Nat.card V % p = Nat.card D % p at hmod
  have hDdiv : Nat.card D ∣ 2^n := hn ▸ D.card_subgroup_dvd_card
  obtain ⟨k,hk,hDcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hDdiv
  have hnk : n = k := by
    apply pow_injOn_Iio_orderOf (x := (2 : ZMod p))
      (show n < orderOf (2 : ZMod p) from lt_of_le_of_lt hnle horder)
      (show k < orderOf (2 : ZMod p) from lt_of_le_of_lt (hk.trans hnle) horder)
    rw [hn,hDcard] at hmod
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ p).mpr hmod
  have heq : Nat.card D = Nat.card V := by rw [hn,hDcard,hnk]
  have htop := D.eq_top_of_card_eq heq
  have haone : a = 1 := by
    apply MulEquiv.ext
    intro x
    exact (show x ∈ D from htop ▸ mem_top x) ⟨a,mem_zpowers a⟩
  rw [haone,orderOf_one] at ha
  exact hp.ne_one ha.symm

open scoped commutatorElement
namespace Subgroup
variable {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]
theorem commutator_component_le_of_primitive_small_section
    (L D Z : Subgroup G) [Finite L] [Finite D] [(Z.subgroupOf D).Normal]
    (hL : IsPPerfect 2 L) (q : L →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) {p m : ℕ} (hp : p.Prime) (hS : p ∣ Nat.card S)
    (hD : IsPGroup 2 D) (hcard : Z.relIndex D ≤ 2 ^ m)
    (horder : m < orderOf (2 : ZMod p))
    (hLD : L ≤ normalizer (D : Set G)) (hLZ : L ≤ normalizer (Z : Set G)) :
    ⁅D,L⁆ ≤ Z := by
  let V := D ⧸ Z.subgroupOf D
  have hV : IsPGroup 2 V := hD.to_quotient _
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action L D Z hLD hLZ inferInstance
  have him : IsPGroup 2 a.range := MonoidHom.isPGroup_range_of_simple_quotient q hq hker
    a p hS (MulAut.not_prime_dvd_card_of_twoGroup_card_bound hp hV hcard horder)
  have hk := pResidual_le_ker_of_isPGroup 2 a.rangeRestrict him
  rw [MonoidHom.ker_rangeRestrict,(pResidual_eq_top_iff 2 L).mpr hL] at hk
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl d hd
  have htriv : a ⟨l,hl⟩ = 1 := hk (mem_top _)
  have hfix := ha ⟨l,hl⟩ ⟨d,hd⟩
  rw [htriv] at hfix
  have hmember := QuotientGroup.eq_iff_div_mem.mp hfix.symm
  change l*d*l⁻¹/d ∈ Z at hmember
  simpa only [div_eq_mul_inv,commutatorElement_def] using hmember

/-- A two-perfect actor with simple symplectic quotient centralizes every
normalized two-section of order at most q². -/
theorem commutator_component_le_of_symplectic_small_section
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hS : Nat.card S = Nat.card
      (Theory.SpecificGroups.SymplecticFour.Sp F))
    (L D Z : Subgroup G) [Finite L] [Finite D] [(Z.subgroupOf D).Normal]
    (hL : IsPPerfect 2 L) (q : L →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker)
    (hD : IsPGroup 2 D) (hcard : Z.relIndex D ≤ Nat.card F ^ 2)
    (hLD : L ≤ normalizer (D : Set G)) (hLZ : L ≤ normalizer (Z : Set G)) :
    ⁅D,L⁆ ≤ Z := by
  obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul hn
  have hdiv : p ∣ Nat.card S := by
    rw [hS]
    exact Representation.SymplecticFour.prime_dvd_card_of_orderOf_two hn hF hp ho
  have hbound : Z.relIndex D ≤ 2 ^ (2 * n) := by
    simpa only [hF,←pow_mul,Nat.mul_comm n 2] using hcard
  exact commutator_component_le_of_primitive_small_section L D Z hL q hq hker
    hp hdiv hD hbound (by rw [ho]; omega) hLD hLZ
end Subgroup
