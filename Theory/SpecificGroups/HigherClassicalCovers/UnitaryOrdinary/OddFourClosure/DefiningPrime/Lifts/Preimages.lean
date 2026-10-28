module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Lifts.Tori
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Group

/-!
# Abelian preimages of unitary roots

Central commutators fixed by simultaneous doubling are killed by three.
The actual diagonal torus therefore makes both short-root preimages abelian
in a central extension with kernel of prime order q > 3. The long-root
parameter groups have order q, so their central preimages commute by
cyclicity. All four conclusions concern the literal matrix root maps.

Source: GLS3 §6.1 and Aschbacher--Smith I.1.4(3), printed p.408.
-/
public section
open scoped commutatorElement
namespace CentralExtension
variable {E G A : Type*} [Group E] [Group G] [AddCommGroup A]

/-- Simultaneous doubling kills the commutator of lifts when the central
kernel has cardinality coprime to three. The parameter group may have rank
larger than one. -/
private theorem commute_lifts_of_doubling
    (f : E →* G) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (hcard : (Nat.card f.ker).Coprime 3)
    (u : Multiplicative A →* G) (d : G)
    (hd : ∀ a : A, d * u (.ofAdd a) * d⁻¹ = u (.ofAdd (a+a)))
    {x y : E} (hx : f x ∈ u.range) (hy : f y ∈ u.range) : Commute x y := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  have hc : ⁅x,y⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, ← ha, ← hb]
    exact ((Commute.all a b).map u).commutator_eq
  have hcenter := hk hc
  have hconj (z : E) : z * ⁅x,y⁆ * z⁻¹ = ⁅x,y⁆ := by
    rw [Subgroup.mem_center_iff.mp hcenter z, mul_inv_cancel_right]
  have hr : ⁅x,y^2⁆ = ⁅x,y⁆^2 := by
    rw [pow_two, commutatorElement_mul_right_eq_mul_conj,
      mul_assoc, mul_assoc, ← mul_assoc y, hconj, pow_two]
  have hrcenter : ⁅x,y^2⁆ ∈ Subgroup.center E := by
    rw [hr]
    exact (Subgroup.center E).pow_mem hcenter 2
  have hfour : ⁅x^2,y^2⁆ = ⁅x,y⁆^4 := by
    rw [pow_two x, commutatorElement_mul_left_eq_conj_mul,
      Subgroup.mem_center_iff.mp hrcenter x, mul_inv_cancel_right, ← pow_two, hr,
      ← pow_mul]
  obtain ⟨z,hz⟩ := hf d
  have he : ⁅x,y⁆ = ⁅x^2,y^2⁆ := by
    rw [← hconj z, conjugate_commutatorElement]
    apply commutator_eq_of_image_eq f hk
    · rw [map_mul, map_mul, map_inv, hz, ← ha, map_pow, ← ha]
      change d * u (.ofAdd a.toAdd) * d⁻¹ = u a ^ 2
      rw [hd a.toAdd]
      change u (a*a) = u a ^ 2
      rw [map_mul, pow_two]
    · rw [map_mul, map_mul, map_inv, hz, ← hb, map_pow, ← hb]
      change d * u (.ofAdd b.toAdd) * d⁻¹ = u b ^ 2
      rw [hd b.toAdd]
      change u (b*b) = u b ^ 2
      rw [map_mul, pow_two]
  have hthree : ⁅x,y⁆^3 = 1 := by
    have H := he.trans hfour
    rw [show 4 = 3+1 by decide, pow_succ] at H
    exact mul_right_cancel (H.symm.trans (one_mul _).symm)
  have hpow : ⁅x,y⁆ ^ Nat.card f.ker = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨⁅x,y⁆,hc⟩ : f.ker)))
  exact commutatorElement_eq_one_iff_commute.mp (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcard (orderOf_dvd_of_pow_eq_one hpow)
      (orderOf_dvd_of_pow_eq_one hthree)))

/-- Central preimages of a cyclic parameter group commute. This is used for
the trace-zero long roots, whose cardinality is q, rather than q². -/
private theorem commute_lifts_of_cyclic_parameters {B : Type*} [Group B] [IsCyclic B]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (u : B →* G) {x y : E} (hx : f x ∈ u.range) (hy : f y ∈ u.range) :
    Commute x y := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  obtain ⟨c,hc⟩ := IsCyclic.exists_generator (α := B)
  obtain ⟨m,hm⟩ := hc a
  obtain ⟨n,hn⟩ := hc b
  obtain ⟨z,hz⟩ := hf (u c)
  apply commutatorElement_eq_one_iff_commute.mp
  rw [commutator_eq_of_image_eq f hk
    (ha.symm.trans (by rw [← hm, map_zpow, ← hz, map_zpow]))
    (hb.symm.trans (by rw [← hn, map_zpow, ← hz, map_zpow]))]
  exact ((Commute.refl z).zpow_zpow m n).commutator_eq

end CentralExtension

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
open BenderSuzuki.MatrixGroups
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 4 F)
variable {E : Type*} [Group E] (f : E →* HyperbolicSU J)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
include hf hk

omit [Finite F] in
private theorem root_preimage_of_doubling {q : ℕ} (hp : q.Prime) (hq : 3 < q)
    (hdegree : Nat.card f.ker = q)
    (u : Multiplicative F →* HyperbolicSU J) (d : HyperbolicSU J)
    (hd : ∀ a : F, d * u (.ofAdd a) * d⁻¹ = u (.ofAdd (a+a)))
    {x y : E} (hx : f x ∈ u.range) (hy : f y ∈ u.range) : Commute x y := by
  apply CentralExtension.commute_lifts_of_doubling f hf hk _ u d hd hx hy
  rw [hdegree]
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq)

/-- The rank-two additive short root has abelian full preimage in every
central extension whose kernel has order q > 3. This does not assert that
its parameter group is cyclic. -/
theorem short_preimage_commute_of_prime_kernel {q : ℕ} (hp : q.Prime) (hq : 3 < q)
    (hcard : Nat.card F = q^2) (hdegree : Nat.card f.ker = q)
    {x y : E} (hx : f x ∈ (shortRoot J).range) (hy : f y ∈ (shortRoot J).range) :
    Commute x y := by
  let : Fact q.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F q := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have h2 : (2 : fixedField J) ≠ 0 := by
    have hF : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F (p := q) Nat.prime_two
      (ne_of_gt (lt_trans (by decide : 2 < 3) hq))
    intro h
    apply hF
    exact congrArg (fun z : fixedField J => (z : F)) h
  let c : (fixedField J)ˣ := Units.mk0 2 h2
  apply root_preimage_of_doubling J f hf hk hp hq hdegree
    (shortRoot J) (fixedDiagonal J c 1) _ hx hy
  intro a
  rw [fixedDiagonal_short, inv_one, mul_one]
  change shortRoot J (.ofAdd ((2 : F)*a)) = shortRoot J (.ofAdd (a+a))
  rw [two_mul]

/-- The other rank-two short-root preimage is abelian by the same doubling
torus, with its actual weight ab. -/
theorem middle_preimage_commute_of_prime_kernel {q : ℕ} (hp : q.Prime) (hq : 3 < q)
    (hcard : Nat.card F = q^2) (hdegree : Nat.card f.ker = q)
    {x y : E} (hx : f x ∈ (middleRoot J).range) (hy : f y ∈ (middleRoot J).range) :
    Commute x y := by
  let : Fact q.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F q := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have h2 : (2 : fixedField J) ≠ 0 := by
    have hF : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F (p := q) Nat.prime_two
      (ne_of_gt (lt_trans (by decide : 2 < 3) hq))
    intro h
    apply hF
    exact congrArg (fun z : fixedField J => (z : F)) h
  let c : (fixedField J)ˣ := Units.mk0 2 h2
  apply root_preimage_of_doubling J f hf hk hp hq hdegree
    (middleRoot J) (fixedDiagonal J c 1) _ hx hy
  intro a
  rw [fixedDiagonal_middle, mul_one]
  change middleRoot J (.ofAdd ((2 : F)*a)) = middleRoot J (.ofAdd (a+a))
  rw [two_mul]

/-- The highest long-root parameters have prime order q. Consequently their
full central preimage is abelian; no bound on the covering kernel is needed. -/
theorem high_preimage_commute {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q)
    {x y : E} (hx : f x ∈ (highRoot J).range) (hy : f y ∈ (highRoot J).range) :
    Commute x y := by
  let : Fact q.Prime := ⟨hp⟩
  let : IsCyclic (Multiplicative (traceZero J)) :=
    isCyclic_of_prime_card (by
      change Nat.card (traceZero J) = q
      exact card_traceZero J hp hcard hconj)
  exact CentralExtension.commute_lifts_of_cyclic_parameters f hf hk (highRoot J) hx hy

/-- The simple long root has the same cyclic trace-zero parameter group. -/
theorem long_preimage_commute {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q)
    {x y : E} (hx : f x ∈ (longRoot J).range) (hy : f y ∈ (longRoot J).range) :
    Commute x y := by
  let : Fact q.Prime := ⟨hp⟩
  let : IsCyclic (Multiplicative (traceZero J)) :=
    isCyclic_of_prime_card (by
      change Nat.card (traceZero J) = q
      exact card_traceZero J hp hcard hconj)
  exact CentralExtension.commute_lifts_of_cyclic_parameters f hf hk (longRoot J) hx hy

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
