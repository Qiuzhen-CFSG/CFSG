module

public import Theory.GroupTheory.PGroup.CriticalSubgroupAutomorphisms
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Detection on first omega for odd p-groups

A coprime automorphism of a finite odd p-group which fixes all elements
whose p-th power is one is trivial. Restrict to a critical subgroup D.
Its central quotient is elementary abelian, so commutators have exponent
p and the p-th power map is a homomorphism. Detection on the abelian center
shows that the automorphism fixes all p-th powers. Consequently each
displacement has p-th power one and is fixed, forcing the automorphism's
p-th power to be the identity. Critical-subgroup detection finishes the proof.

The restriction kernel on first omega is therefore a p-group. This supplies
the odd-prime detection step used in Aschbacher–Smith, *The Classification
of Quasithin Groups*, Lemma A.1.21(3), printed pp.24–25, with the critical
subgroup theorem cited there as Aschbacher, *Finite Group Theory*, §24.
The private power-collection identities are adapted from this repository's
`Theory.GroupTheory.OddPrimeRankOneSylow`.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

private theorem oddCriticalOmega_pow_mul_swap_of_relation
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_y : Commute c y) :
    ∀ n : ℕ, y ^ n * x = c ^ n * x * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        y ^ (n + 1) * x = y * (y ^ n * x) := by simp [pow_succ', mul_assoc]
        _ = y * (c ^ n * x * y ^ n) := by
              rw [oddCriticalOmega_pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = y * c ^ n * x * y ^ n := by simp [mul_assoc]
        _ = c ^ n * y * x * y ^ n := by
              have hycn : Commute (c ^ n) y := hc_y.pow_left n
              rw [hycn.eq]
        _ = c ^ n * (y * x) * y ^ n := by simp [mul_assoc]
        _ = c ^ n * (c * x * y) * y ^ n := by rw [hrel]
        _ = (c ^ n * c) * x * (y * y ^ n) := by simp [mul_assoc]
        _ = (c ^ n * c) * x * (y ^ n * y) := by
              have hy_pow_comm : y * y ^ n = y ^ n * y := by
                calc
                  y * y ^ n = y ^ (n + 1) := (pow_succ' y n).symm
                  _ = y ^ n * y := pow_succ y n
              rw [hy_pow_comm]
        _ = c ^ (n + 1) * x * y ^ (n + 1) := by
              simp [pow_succ, mul_assoc]

private theorem oddCriticalOmega_pow_mul_eq_cpow_mul_pow_mul_pow
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_x : Commute c x)
    (hc_y : Commute c y) :
    ∀ n : ℕ, (x * y) ^ n = c ^ (Nat.choose n 2) * x ^ n * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := by simp [pow_succ]
        _ = (c ^ (Nat.choose n 2) * x ^ n * y ^ n) * (x * y) := by
              rw [oddCriticalOmega_pow_mul_eq_cpow_mul_pow_mul_pow x y c hrel hc_x hc_y n]
        _ = c ^ (Nat.choose n 2) * x ^ n * (y ^ n * x) * y := by simp [mul_assoc]
        _ = c ^ (Nat.choose n 2) * x ^ n * (c ^ n * x * y ^ n) * y := by
              rw [oddCriticalOmega_pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = c ^ (Nat.choose n 2) * (x ^ n * c ^ n) * x * y ^ n * y := by
              simp [mul_assoc]
        _ = c ^ (Nat.choose n 2) * (c ^ n * x ^ n) * x * y ^ n * y := by
              have hcxnn : Commute (c ^ n) (x ^ n) := (hc_x.pow_left n).pow_right n
              rw [hcxnn.symm.eq]
        _ = (c ^ (Nat.choose n 2) * c ^ n) * (x ^ n * x) * (y ^ n * y) := by
              simp [mul_assoc]
        _ = c ^ (Nat.choose (n + 1) 2) * x ^ (n + 1) * y ^ (n + 1) := by
              have hchoose : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
                simpa [Nat.choose_one_right, Nat.add_comm] using
                  (Nat.choose_succ_right (n := n + 1) (k := 1) (Nat.succ_pos n))
              rw [hchoose, pow_add, pow_succ, pow_succ]

private theorem oddCriticalOmega_prime_dvd_choose_two {p : ℕ} [Fact (Nat.Prime p)]
    (hpodd : p ≠ 2) :
    p ∣ Nat.choose p 2 := by
  have hlt : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hpodd)
  exact Nat.Prime.dvd_choose_self (Fact.out : Nat.Prime p) (k := 2) (by decide) hlt

private theorem oddCriticalOmega_choose_two_pow_eq_one
    {p : ℕ} [Fact (Nat.Prime p)] {M : Type*} [Group M] {c : M}
    (hpodd : p ≠ 2) (hc : c ^ p = 1) :
    c ^ Nat.choose p 2 = 1 := by
  rcases oddCriticalOmega_prime_dvd_choose_two (p := p) hpodd with ⟨k, hk⟩
  calc
    c ^ Nat.choose p 2 = c ^ (p * k) := by simp [hk]
    _ = (c ^ p) ^ k := by rw [pow_mul]
    _ = 1 := by simp [hc]


private theorem oddCriticalOmega_pth_mul {R : Type*} [Group R] {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) [IsElementaryAbelian p (R ⧸ center R)]
    (x y : R) : (x * y) ^ p = x ^ p * y ^ p := by
  have hc : _root_.commutator R ≤ center R :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hpow (z : R) : z ^ p ∈ center R := by
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (R ⧸ center R)) _
  have hm : ⁅y, x⁆ ∈ center R :=
    hc (commutator_mem_commutator (mem_top _) (mem_top _))
  have hrel : y * x = ⁅y, x⁆ * x * y := by
    simp [commutatorElement_def, mul_assoc]
  have hcx : Commute ⁅y, x⁆ x := ((mem_center_iff.mp hm) x).symm
  have hcy : Commute ⁅y, x⁆ y := ((mem_center_iff.mp hm) y).symm
  have hcp : ⁅y, x⁆ ^ p = 1 := by
    have he := oddCriticalOmega_pow_mul_swap_of_relation x y ⁅y, x⁆ hrel hcy p
    rw [(mem_center_iff.mp (hpow y) x).symm] at he
    have he' : 1 * (x * y ^ p) = ⁅y, x⁆ ^ p * (x * y ^ p) := by
      simpa only [one_mul, mul_assoc] using he
    exact (mul_right_cancel he').symm
  rw [oddCriticalOmega_pow_mul_eq_cpow_mul_pow_mul_pow x y ⁅y, x⁆ hrel hcx hcy,
    oddCriticalOmega_choose_two_pow_eq_one hp hcp, one_mul]

private theorem oddCriticalOmega_eq_one_of_fixes_roots
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hp : p ≠ 2) [IsElementaryAbelian p (R ⧸ center R)]
    (a : MulAut R) (hcop : p.Coprime (orderOf a))
    (hfix : ∀ x : R, x ^ p = 1 → a x = x) : a = 1 := by
  let b := MulAut.characteristic (center R) a
  have hbomega : OmegaAction.omegaRestriction (center R) p 1 b = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    apply hfix
    have hx : (x : center R) ∈ (powMonoidHom (p^1) : center R →* center R).ker :=
      (OmegaAction.omega_eq_pow_ker (G := center R) p 1) ▸ x.property
    simpa using congrArg Subtype.val hx
  have hb : b = 1 := by
    apply orderOf_eq_one_iff.mp
    have he := (OmegaAction.omegaRestriction (center R) p 1).orderOf_map_eq_of_coprime_of_isPGroup_ker
        (OmegaAction.restriction_kernel_isPGroup (hR.to_subgroup (center R))) b
        (hcop.of_dvd_right (orderOf_map_dvd (MulAut.characteristic (center R)) a))
    rw [hbomega, orderOf_one] at he
    exact he.symm
  have hcenterfix (x : R) (hx : x ∈ center R) : a x = x :=
    congrArg Subtype.val (DFunLike.congr_fun hb (⟨x, hx⟩ : center R))
  have hpowcenter (x : R) : x ^ p ∈ center R := by
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (R ⧸ center R)) _
  have hdisp (x : R) : (x⁻¹ * a x) ^ p = 1 := by
    rw [oddCriticalOmega_pth_mul hp, inv_pow, ← map_pow,
      hcenterfix _ (hpowcenter x), inv_mul_cancel]
  have hiter (x : R) (n : ℕ) : (a ^ n) x = x * (x⁻¹ * a x) ^ n := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ', MulAut.mul_apply, hn, map_mul, map_pow, hfix _ (hdisp x)]
      simp only [pow_succ', ← mul_assoc, mul_inv_cancel, one_mul]
  have hap : a ^ p = 1 := by
    ext x
    rw [hiter, hdisp, mul_one]
    rfl
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hap) dvd_rfl

/-- Odd-prime coprime automorphisms are detected on elements of order dividing p. -/
public theorem MulAut.eq_one_of_coprime_of_fixes_prime_roots
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hp : p ≠ 2) (a : MulAut P)
    (hcop : p.Coprime (orderOf a))
    (hfix : ∀ x : P, x ^ p = 1 → a x = x) : a = 1 := by
  obtain ⟨D, hD⟩ := hP.exists_criticalPSubgroup
  let : D.Characteristic := hD.characteristic
  let : IsElementaryAbelian p (D ⧸ center D) := hD.quotient_elementary
  have he := hD.orderOf_restrict_eq_of_coprime hP a hcop
  have hd : MulAut.characteristic D a = 1 :=
    oddCriticalOmega_eq_one_of_fixes_roots (hP.to_subgroup D) hp _ (by rwa [he])
      (fun x hx => Subtype.ext (hfix x (congrArg Subtype.val hx)))
  apply orderOf_eq_one_iff.mp
  rw [hd, orderOf_one] at he
  exact he.symm

/-- Restriction to first omega in a finite odd p-group has p-group kernel. -/
public theorem OmegaAction.restriction_kernel_isPGroup_of_odd
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hp : p ≠ 2) :
    IsPGroup p (OmegaAction.omegaRestriction P p 1).ker := by
  let K := (OmegaAction.omegaRestriction P p 1).ker
  apply isPGroup_of_prime_order_eq_p p K
  intro a ha
  by_contra hne
  have he : (a : MulAut P) = 1 := MulAut.eq_one_of_coprime_of_fixes_prime_roots hP hp a
    (by
      rw [orderOf_coe]
      exact (Nat.coprime_primes (Fact.out : p.Prime) ha).mpr (Ne.symm hne))
    (by
      intro x hx
      have hxO : x ∈ omega P (p := p) 1 := subset_closure (by simpa using hx)
      exact congrArg (fun f : MulAut (omega P (p := p) 1) => (f ⟨x, hxO⟩ : P))
        a.property)
  have he' : a = 1 := Subtype.ext he
  exact ha.ne_one (by rw [he', orderOf_one])
