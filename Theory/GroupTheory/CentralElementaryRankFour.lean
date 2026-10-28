module

public import Theory.GroupTheory.PGroup.ExponentPrimeRankTwoOrder
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Mathlib.Data.Nat.Choose.Dvd
public import Theory.Quasithin.Rank

/-!
# Odd-prime rank in central extensions of elementary abelian groups

A finite central extension of an elementary abelian p-group of order at least
p⁴ has p-rank at least three, for odd p. No p-group hypothesis on the central
kernel is needed. Centrality makes the commutators have exponent dividing p;
collection then makes the p-th power map a homomorphism into the kernel.
Its own kernel has order at least that of the original elementary quotient,
exponent dividing p, and class at most two. The exponent-p rank-two order bound
excludes rank at most two; the cyclic case includes ranks zero and one.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, A.2.17, printed p.39. The collection argument
follows the elementary calculation also used in `SupercriticalExistence/ClassTwoOmega`.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace CentralExtension

private theorem swap_pow {P : Type*} [Group P] (x y c : P)
    (hc : ∀ z, Commute c z) (hxy : y * x = c * x * y) (n : ℕ) :
    y ^ n * x = c ^ n * x * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      y ^ (n + 1) * x = y * (y ^ n * x) := by simp [pow_succ', mul_assoc]
      _ = y * (c ^ n * x * y ^ n) := by rw [ih]
      _ = c ^ n * (y * x) * y ^ n := by
        simp only [← mul_assoc]
        rw [← (hc y).pow_left n |>.eq]
      _ = c ^ (n + 1) * x * y ^ (n + 1) := by
        rw [hxy, pow_succ c, pow_succ' y]; simp only [mul_assoc]

private theorem collect {P : Type*} [Group P] (x y c : P)
    (hc : ∀ z, Commute c z) (hxy : y * x = c * x * y) (n : ℕ) :
    (x * y) ^ n = c ^ n.choose 2 * x ^ n * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
      simpa [Nat.choose_one_right, Nat.add_comm] using
        (Nat.choose_succ_right (n := n + 1) (k := 1) (Nat.succ_pos n))
    calc
      (x * y) ^ (n + 1) = c ^ n.choose 2 * x ^ n * (y ^ n * x) * y := by
        rw [pow_succ, ih]; simp [mul_assoc]
      _ = c ^ n.choose 2 * x ^ n * (c ^ n * x * y ^ n) * y := by
        rw [swap_pow x y c hc hxy n]
      _ = c ^ (n + 1).choose 2 * x ^ (n + 1) * y ^ (n + 1) := by
        rw [hchoose, pow_add, pow_succ, pow_succ]
        have he := (hc (x ^ n)).pow_left n |>.eq
        calc
          _ = c ^ n.choose 2 * (x ^ n * c ^ n) * x * y ^ n * y := by simp [mul_assoc]
          _ = c ^ n.choose 2 * (c ^ n * x ^ n) * x * y ^ n * y := by rw [← he]
          _ = _ := by simp [mul_assoc]

variable {p : ℕ} [Fact p.Prime] {P E : Type*} [Group P] [Group E]

private theorem mul_pow_of_central_elementary_quotient [IsElementaryAbelian p E]
    (f : P →* E) (hc : f.ker ≤ center P) (hp : p ≠ 2) (x y : P) :
    (x * y) ^ p = x ^ p * y ^ p := by
  have hpow (z : P) : z ^ p ∈ center P := hc (by
    rw [MonoidHom.mem_ker, map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) _)
  have hcomm : ⁅y, x⁆ ∈ center P := hc (by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _))
  have hcc (z : P) : Commute ⁅y, x⁆ z := (mem_center_iff.mp hcomm z).symm
  have hrel : y * x = ⁅y, x⁆ * x * y := by simp [commutatorElement_def, mul_assoc]
  have hcp : ⁅y, x⁆ ^ p = 1 := by
    have hh := swap_pow x y ⁅y, x⁆ hcc hrel p
    rw [(mem_center_iff.mp (hpow y) x).symm] at hh
    exact mul_right_cancel (show ⁅y, x⁆ ^ p * (x * y ^ p) = 1 * (x * y ^ p) by
      simpa only [mul_assoc, one_mul] using hh.symm)
  have hd : p ∣ p.choose 2 := Nat.Prime.dvd_choose_self (Fact.out : p.Prime)
    (by decide) (lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp))
  obtain ⟨k, hk⟩ := hd
  rw [collect x y ⁅y, x⁆ hcc hrel p, hk, pow_mul, hcp, one_pow, one_mul]

private theorem card_le_cube_of_exponent_dvd [Finite P]
    (hp : p ≠ 2) (hpow : Monoid.exponent P ∣ p)
    (hc : commutator P ≤ center P) (hr : primeRank p P ≤ 2) :
    Nat.card P ≤ p ^ 3 := by
  have hP : IsPGroup p P := IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hpow)
  by_cases hr2 : primeRank p P = 2
  · have he : Monoid.exponent P = p := by
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hpow with he | he
      · have h1 : Subsingleton P := ⟨fun x y => by
          have hx := Monoid.pow_exponent_eq_one x
          have hy := Monoid.pow_exponent_eq_one y
          rw [he, pow_one] at hx hy
          exact hx.trans hy.symm⟩
        let := h1
        have hp1 : Nat.card P = 1 := Nat.card_unique
        have hle : primeRank p P ≤ 1 := primeRank_le_nat_card p |>.trans_eq hp1
        omega
      · exact he
    exact hP.card_le_prime_cube_of_exponent_prime_rank_two hp he hr2 hc
  · have hr1 : primeRank p P ≤ 1 := by omega
    let : IsCyclic P := hP.isCyclic_of_odd_of_elementary_card_le
      ((Fact.out : p.Prime).odd_of_ne_two hp) (fun A hA => by
        let := hA
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr1 A)
    rw [IsCyclic.exponent_eq_card] at hpow
    exact (Nat.le_of_dvd (Fact.out : p.Prime).pos hpow).trans
      (by simpa using pow_le_pow_right' (Fact.out : p.Prime).one_lt.le (by decide : 1 ≤ 3))

/-- An elementary quotient of order at least p⁴ forces rank at least three
in any finite central extension, for odd p. -/
public theorem three_le_primeRank_of_elementary_quotient [Finite P] [Finite E] [IsElementaryAbelian p E]
    (f : P →* E) (hf : Function.Surjective f) (hc : f.ker ≤ center P)
    (hp : p ≠ 2) (hcard : p ^ 4 ≤ Nat.card E) : 3 ≤ primeRank p P := by
  let power : P →* f.ker := {
    toFun := fun x => ⟨x ^ p, by
      rw [MonoidHom.mem_ker, map_pow]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E) _⟩
    map_one' := Subtype.ext (one_pow p)
    map_mul' := fun x y => Subtype.ext (mul_pow_of_central_elementary_quotient f hc hp x y) }
  have hclass : commutator P ≤ center P := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    exact hc (by rw [MonoidHom.mem_ker, map_commutatorElement]
                 exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _))
  have hclassK : commutator power.ker ≤ center power.ker := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    apply mem_center_iff.mpr
    intro z
    exact Subtype.ext (mem_center_iff.mp
      (hclass (commutator_mem_commutator (mem_top (x : P)) (mem_top (y : P)))) z)
  have hKexp : Monoid.exponent power.ker ∣ p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    change (x.val : P) ^ p = 1
    exact congrArg (fun z : f.ker => (z : P)) (show power x.val = 1 from x.property)
  have hPcard : Nat.card P = Nat.card E * Nat.card f.ker := by
    rw [← f.ker.index_mul_card, index_eq_card]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hpowercard : Nat.card P = Nat.card power.range * Nat.card power.ker := by
    rw [← power.ker.index_mul_card, index_eq_card]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange power).toEquiv]
  have hKcard : Nat.card E ≤ Nat.card power.ker := by
    apply Nat.le_of_mul_le_mul_right (c := Nat.card f.ker) _ Nat.card_pos
    calc
      Nat.card E * Nat.card f.ker = Nat.card P := hPcard.symm
      _ = Nat.card power.range * Nat.card power.ker := hpowercard
      _ ≤ Nat.card f.ker * Nat.card power.ker :=
        Nat.mul_le_mul_right _ power.range.card_le_card_group
      _ = Nat.card power.ker * Nat.card f.ker := Nat.mul_comm _ _
  by_contra hr
  have hr2 : primeRank p power.ker ≤ 2 :=
    (primeRank_subgroup_le p power.ker).trans (by omega)
  have hh := card_le_cube_of_exponent_dvd hp hKexp hclassK hr2
  have hlt : p ^ 3 < p ^ 4 := (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mpr (by decide)
  exact (not_le_of_gt hlt) (hcard.trans (hKcard.trans hh))

end CentralExtension
