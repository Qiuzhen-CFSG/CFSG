module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.FixedPoints
public import CFSG.Quasithin.Chapter8.Section02.Offenders.LinearTorus.Setup
public import Theory.NumberTheory.BinaryMersenneDivisibility
public import Theory.NumberTheory.BinaryParabolicRank

/-!
# The oversized-torus step in §8.2.3

The divisibility displayed in the book is not by itself enough to exclude
`n < k < 2*n`: for example `(n,k) = (3,4)` satisfies the displayed numerical
condition. The desired restriction `2^k - 1 ∣ 2^(2*n) - 1` requires more
than preservation of a maximal parabolic: its Levi factor also has nonsplit
tori. The original arithmetic reduction retains this restriction explicitly.

With that restriction, the standard binary-torus divisibility calculation
forces `k ∣ 2*n`.  The source bounds then leave only `k ≤ n` or `k = 2*n`.
The latter is discharged by H.4.4(4), whose hypothesis is retained as an
explicit fixed-space contradiction.  Consequently `k = w = n`.

The new model reduction below derives the stronger restriction from two
explicit geometry inputs and the preceding E.2.14/H.4.4 facts. If `n < k < 2n`,
the fixed space has rank greater than `3n`, excluding nontrivial coefficient
action. Its dimension is then divisible by n. The linear parabolic exponent
gives `k ∣ 4n`, hence `3k = 4n`; the actor degree and fixed-codimension bounds
exclude this intermediate case. Neither geometry contract is discharged in
this file yet. They concern the actual normalizer and parabolic images.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition 8.2.3, printed pp.715–716 (PDF pp.732–733), using E.2.14(9)
and H.4.4(4).
-/

public section

namespace CFSG.Quasithin.Chapter8.Section02.Offenders

/-- The target numerical restriction. It requires the actual model's
fixed-space and actor-degree constraints as well as parabolic preservation;
the displayed divisibility in the book alone does not imply it. -/
def HasLinearThreeParabolicTorus (n k : ℕ) : Prop :=
  2 ^ k - 1 ∣ 2 ^ (2 * n) - 1

/- The converse direction of the binary torus divisibility criterion, proved
   from the remainder formula rather than assumed as a field-theory tag. -/
theorem pow_sub_one_dvd_pow_sub_one_iff_dvd
    {m k : ℕ} (_hm : 0 < m) :
    2 ^ m - 1 ∣ 2 ^ k - 1 ↔ m ∣ k := by
  constructor
  · intro h
    have hz : (2 ^ k - 1) % (2 ^ m - 1) = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.pow_sub_one_mod_pow_sub_one] at hz
    have hle : 2 ^ (k % m) ≤ 1 := Nat.sub_eq_zero_iff_le.mp hz
    have hone : 1 ≤ 2 ^ (k % m) := Nat.one_le_pow (k % m) 2 (by decide)
    have he : 2 ^ (k % m) = 1 := le_antisymm hle hone
    have hzero : k % m = 0 :=
      (Nat.pow_eq_one.mp he).resolve_left (by decide)
    exact Nat.dvd_of_mod_eq_zero hzero
  · exact Nat.pow_sub_one_dvd_pow_sub_one 2

/-!
The source bounds are packaged in their literal order. `hparabolic` is the
target torus restriction for `X̄`; it is stronger than the
book's displayed divisibility by `n * (2^(4*n)-1)` and is the point at which
the descended tensor action enters this reduction.  `hH44` is precisely the
H.4.4(4) fixed-space exclusion for the rank-saturated `k = 2*n` case.
-/
theorem linear_three_k_eq_w_eq_n
    {n w k : ℕ} (hn : 0 < n)
    (hbounds : n ≤ w ∧ w ≤ k ∧ k ≤ 2 * n)
    (hparabolic : HasLinearThreeParabolicTorus n k)
    (hH44 : k = 2 * n → False) :
    k = n ∧ w = n := by
  have hnk : n ≤ k := hbounds.1.trans hbounds.2.1
  have hkpos : 0 < k := lt_of_lt_of_le hn hnk
  have hkdiv : k ∣ 2 * n :=
    (pow_sub_one_dvd_pow_sub_one_iff_dvd (m := k) hkpos).mp hparabolic
  have hkn : k ≤ n ∨ k = 2 * n := by
    rcases hkdiv with ⟨d, hd⟩
    have hdpos : 0 < d := by
      by_contra hzero
      have : d = 0 := Nat.eq_zero_of_not_pos hzero
      simp [this] at hd
      omega
    have hdle2 : d ≤ 2 := by
      by_contra hnot
      have hd3 : 3 ≤ d := by omega
      have hmul : k * 3 ≤ k * d := Nat.mul_le_mul_left k hd3
      omega
    have hd_cases : d = 1 ∨ d = 2 := by omega
    rcases hd_cases with rfl | rfl
    · right
      omega
    · left
      omega
  have hkle : k ≤ n := hkn.resolve_right hH44
  have hwk : w = k := by omega
  have hkn' : k = n := by omega
  exact ⟨hkn', hwk.trans hkn'⟩

end CFSG.Quasithin.Chapter8.Section02.Offenders

namespace CFSG.Quasithin.Chapter8.Section02.Offenders.LinearThreeTorus
open Representation.HermitianTensorThree
open Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open Representation.BinaryOffender

variable {n k : ℕ} [NeZero n]

/-- The actual fixed-space and actor-degree constraints exclude the nonsplit
intermediate case. The two independent geometry calculations remain explicit. -/
theorem Setup.not_intermediate_of_geometry (s : Setup n k)
    (hfield : LargeOddFixedSpaceLinearity n)
    (hparabolic : OddLinearParabolicExponent n)
    (hnk : n < k) (hkn : k < 2 * n) : False := by
  have hkpos : 0 < k := by omega
  have hodd : Odd (orderOf s.x) := by
    rw [s.order]
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    refine ⟨2 ^ l - 1, ?_⟩
    rw [pow_succ]
    have := Nat.one_le_pow l 2 (by decide)
    omega
  have hnormal := sourceOvergroup_le_normalizer n s.M s.source s.x.property
  obtain ⟨hlinear, hdegree⟩ := hfield s.M s.x hnormal hodd (by
    rw [← s.fixed_eq]
    exact s.fixed_rank_gt_three_mul hkn)
  rw [← s.fixed_eq] at hdegree
  have hodd' : Odd (orderOf s.x.val) := by rwa [Subgroup.orderOf_coe]
  have hdiv := hparabolic s.x.val hnormal hodd' hlinear s.parabolic
  rw [Subgroup.orderOf_coe, s.order] at hdiv
  have hkdiv : k ∣ 4 * n :=
    (pow_sub_one_dvd_pow_sub_one_iff_dvd (m := k) hkpos).mp hdiv
  have hsum : n ∣ Module.finrank (ZMod 2) s.Z + (k + rank s.A) := by
    rw [← Nat.add_assoc, s.rank_identity]
    exact dvd_mul_left n 9
  have hfixed : n ∣ k + rank s.A := (Nat.dvd_add_iff_right hdegree).mpr hsum
  exact Nat.BinaryParabolicRank.false_of_intermediate_parameters
    hnk hkn hkdiv s.actor_rank_le s.five_mul_le_rank_sum s.module_degree hfixed

/-- Discharge the original torus restriction from the marked model, conditional
only on the two explicit geometry calculations and preceding source inputs. -/
theorem Setup.hasLinearThreeParabolicTorus_of_geometry (s : Setup n k)
    (hfield : LargeOddFixedSpaceLinearity n)
    (hparabolic : OddLinearParabolicExponent n)
    (hlower : n ≤ k) (hupper : k ≤ 2 * n) : HasLinearThreeParabolicTorus n k := by
  by_cases he : k = n
  · subst k
    exact Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left n 2)
  by_cases he : k = 2 * n
  · subst k
    exact dvd_rfl
  exact (s.not_intermediate_of_geometry hfield hparabolic (by omega) (by omega)).elim

/-- Consumer application to the original parameter theorem. H.4.4(4) remains
the endpoint input; it is separate from the two model calculations. -/
theorem Setup.parameters_of_geometry (s : Setup n k) {w : ℕ}
    (hfield : LargeOddFixedSpaceLinearity n)
    (hparabolic : OddLinearParabolicExponent n)
    (hbounds : n ≤ w ∧ w ≤ k ∧ k ≤ 2 * n)
    (hH44 : k = 2 * n → False) : k = n ∧ w = n :=
  linear_three_k_eq_w_eq_n (NeZero.pos n) hbounds
    (s.hasLinearThreeParabolicTorus_of_geometry hfield hparabolic
      (hbounds.1.trans hbounds.2.1) hbounds.2.2) hH44

end CFSG.Quasithin.Chapter8.Section02.Offenders.LinearThreeTorus
