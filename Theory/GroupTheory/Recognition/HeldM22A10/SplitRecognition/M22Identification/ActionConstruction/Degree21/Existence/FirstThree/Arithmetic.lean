module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
/-!
# Finite signed-row certificates at order 443520

Complementary factors up to the square root exhaust every signed divisor.
For each first-three-column pattern, the Sylow congruence leaves the explicit
small row list below. Kernel-checked certificates impose the degree, involution
and Suzuki equations. The first decomposition is impossible; in the second,
the final two entries of every row have zero product.

These numerical results are applied to actual irreducible characters in the
sibling CaseOne and CaseTwo modules. The lists are certificates, not assumed
character rows. Source: Z. Janko, *A characterization of the Mathieu simple
groups, I*, J. Algebra 9 (1968), Sections 6–7, pp.12–16.
-/
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.FirstThree.Arithmetic
public structure Row where
  d : ℤ
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

@[expose] public def Row.value (r : Row) (v : ℤ) : ℤ := v + 8*r.a + 3*r.b

private def smallDivisors (g : ℕ) : List ℕ :=
  ((List.range (g.sqrt + 1)).filter (fun d => 0 < d ∧ d ∣ g)).flatMap
    (fun d => [d, g / d])

private theorem mem_smallDivisors {g n : ℕ} (hg : 0 < g) (hn : n ∣ g) :
    n ∈ smallDivisors g := by
  have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn hg
  obtain ⟨m, hm⟩ := hn
  have hm0 : 0 < m := by nlinarith
  rcases Nat.le_sqrt_of_eq_mul hm with h | h
  · apply List.mem_flatMap.mpr
    refine ⟨n, ?_, by simp⟩
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, hn0, ⟨m, hm⟩⟩
  · apply List.mem_flatMap.mpr
    refine ⟨m, ?_, ?_⟩
    · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, hm0, ⟨n, hm.trans (Nat.mul_comm _ _)⟩⟩
    · simp [hm, Nat.mul_div_cancel _ hm0]

private def signedDivisors : List ℤ :=
  (smallDivisors 443520).flatMap (fun (n : ℕ) => [(n : ℤ), -(n : ℤ)])

private theorem mem_signedDivisors {d : ℤ} (hd : d ∣ 443520) : d ∈ signedDivisors := by
  have hn : d.natAbs ∣ 443520 := Int.natAbs_dvd_natAbs.mpr hd
  apply List.mem_flatMap.mpr
  refine ⟨d.natAbs, mem_smallDivisors (by norm_num) hn, ?_⟩
  have h := Int.natCast_natAbs d
  simp only [List.mem_cons]
  rcases le_total 0 d with hp | hn
  · left; simp [h, abs_of_nonneg hp]
  · right; simp [h, abs_of_nonpos hn]

public def rows (c : ℤ) : List Row :=
  (([-1, 0, 1] : List ℤ).flatMap fun a =>
    ([-1, 0, 1] : List ℤ).flatMap fun b =>
      signedDivisors.map fun d => Row.mk d a b).filter
        (fun r => (128 : ℤ) ∣ r.d + c + 280*r.a + 45*r.b)

public theorem mem_rows {c : ℤ} {r : Row} (hd : r.d ∣ 443520)
    (ha : r.a ∈ ([-1,0,1] : List ℤ)) (hb : r.b ∈ ([-1,0,1] : List ℤ))
    (hc : (128 : ℤ) ∣ r.d + c + 280*r.a + 45*r.b) : r ∈ rows c := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_flatMap.mpr ⟨r.a, ha, List.mem_flatMap.mpr ⟨r.b, hb, ?_⟩⟩, ?_⟩
  · exact List.mem_map.mpr ⟨r.d, mem_signedDivisors hd, by cases r; rfl⟩
  · simpa using hc

private def candidates280 : List Row :=
  [⟨45, -1, -1⟩,
   ⟨443520, -1, 0⟩,
   ⟨-443520, -1, 0⟩,
   ⟨147840, -1, 0⟩,
   ⟨-147840, -1, 0⟩,
   ⟨88704, -1, 0⟩,
   ⟨-88704, -1, 0⟩,
   ⟨63360, -1, 0⟩,
   ⟨-63360, -1, 0⟩,
   ⟨49280, -1, 0⟩,
   ⟨-49280, -1, 0⟩,
   ⟨40320, -1, 0⟩,
   ⟨-40320, -1, 0⟩,
   ⟨29568, -1, 0⟩,
   ⟨-29568, -1, 0⟩,
   ⟨21120, -1, 0⟩,
   ⟨-21120, -1, 0⟩,
   ⟨13440, -1, 0⟩,
   ⟨-13440, -1, 0⟩,
   ⟨12672, -1, 0⟩,
   ⟨-12672, -1, 0⟩,
   ⟨9856, -1, 0⟩,
   ⟨-9856, -1, 0⟩,
   ⟨8064, -1, 0⟩,
   ⟨-8064, -1, 0⟩,
   ⟨7040, -1, 0⟩,
   ⟨-7040, -1, 0⟩,
   ⟨5760, -1, 0⟩,
   ⟨-5760, -1, 0⟩,
   ⟨4480, -1, 0⟩,
   ⟨-4480, -1, 0⟩,
   ⟨4224, -1, 0⟩,
   ⟨-4224, -1, 0⟩,
   ⟨128, -1, 0⟩,
   ⟨-128, -1, 0⟩,
   ⟨2688, -1, 0⟩,
   ⟨-2688, -1, 0⟩,
   ⟨1920, -1, 0⟩,
   ⟨-1920, -1, 0⟩,
   ⟨1408, -1, 0⟩,
   ⟨-1408, -1, 0⟩,
   ⟨384, -1, 0⟩,
   ⟨-384, -1, 0⟩,
   ⟨1152, -1, 0⟩,
   ⟨-1152, -1, 0⟩,
   ⟨896, -1, 0⟩,
   ⟨-896, -1, 0⟩,
   ⟨640, -1, 0⟩,
   ⟨-640, -1, 0⟩,
   ⟨-45, -1, 1⟩,
   ⟨21, 0, -1⟩,
   ⟨-24, 0, 0⟩,
   ⟨-9240, 0, 0⟩,
   ⟨-280, 0, 0⟩,
   ⟨360, 0, 0⟩,
   ⟨-792, 0, 0⟩,
   ⟨616, 0, 0⟩,
   ⟨315, 0, 1⟩,
   ⟨-3, 1, -1⟩,
   ⟨-1155, 1, -1⟩,
   ⟨-18480, 1, 0⟩,
   ⟨11088, 1, 0⟩,
   ⟨-48, 1, 0⟩,
   ⟨80, 1, 0⟩,
   ⟨-5040, 1, 0⟩,
   ⟨2640, 1, 0⟩,
   ⟨-176, 1, 0⟩,
   ⟨-1584, 1, 0⟩,
   ⟨336, 1, 0⟩,
   ⟨1232, 1, 0⟩,
   ⟨-560, 1, 0⟩,
   ⟨720, 1, 0⟩,
   ⟨35, 1, 1⟩]

set_option maxRecDepth 10000 in
private theorem rows_candidates280 : rows (280) = candidates280 := by decide +kernel

private def candidates127 : List Row :=
  [⟨70, -1, -1⟩,
   ⟨198, -1, -1⟩,
   ⟨-231, -1, 0⟩,
   ⟨-20, -1, 1⟩,
   ⟨1260, -1, 1⟩,
   ⟨-660, -1, 1⟩,
   ⟨-210, 0, -1⟩,
   ⟨1, 0, 0⟩,
   ⟨385, 0, 0⟩,
   ⟨-44, 0, 1⟩,
   ⟨84, 0, 1⟩,
   ⟨2772, 0, 1⟩,
   ⟨22, 1, -1⟩,
   ⟨-1386, 1, -1⟩,
   ⟨105, 1, 0⟩,
   ⟨60, 1, 1⟩,
   ⟨1980, 1, 1⟩]

set_option maxRecDepth 10000 in
private theorem rows_candidates127 : rows (127) = candidates127 := by decide +kernel

private def candidates78 : List Row :=
  [⟨-9, -1, -1⟩,
   ⟨-3465, -1, -1⟩,
   ⟨330, -1, 0⟩,
   ⟨-99, -1, 1⟩,
   ⟨-33, 0, -1⟩,
   ⟨-462, 0, 0⟩,
   ⟨5, 0, 1⟩,
   ⟨154, 1, 0⟩]

set_option maxRecDepth 10000 in
private theorem rows_candidates78 : rows (78) = candidates78 := by decide +kernel

private def candidatesNeg329 : List Row :=
  [⟨14, -1, -1⟩,
   ⟨180, -1, 1⟩,
   ⟨308, -1, 1⟩,
   ⟨-10, 0, -1⟩,
   ⟨630, 0, -1⟩,
   ⟨-55, 0, 0⟩,
   ⟨28, 0, 1⟩,
   ⟨924, 0, 1⟩,
   ⟨990, 1, -1⟩,
   ⟨4, 1, 1⟩,
   ⟨132, 1, 1⟩,
   ⟨-252, 1, 1⟩,
   ⟨1540, 1, 1⟩]

set_option maxRecDepth 10000 in
private theorem rows_candidatesNeg329 : rows (-329) = candidatesNeg329 := by decide +kernel

private def candidates153 : List Row :=
  [⟨44, -1, -1⟩,
   ⟨-84, -1, -1⟩,
   ⟨-2772, -1, -1⟩,
   ⟨-1, -1, 0⟩,
   ⟨-385, -1, 0⟩,
   ⟨210, -1, 1⟩,
   ⟨20, 0, -1⟩,
   ⟨-1260, 0, -1⟩,
   ⟨660, 0, -1⟩,
   ⟨231, 0, 0⟩,
   ⟨-70, 0, 1⟩,
   ⟨-198, 0, 1⟩,
   ⟨-4, 1, -1⟩,
   ⟨-132, 1, -1⟩,
   ⟨252, 1, -1⟩,
   ⟨-1540, 1, -1⟩,
   ⟨-990, 1, 1⟩]

set_option maxRecDepth 10000 in
private theorem rows_candidates153 : rows (153) = candidates153 := by decide +kernel

private def candidatesNeg202 : List Row :=
  [⟨15, -1, -1⟩,
   ⟨-30, -1, 0⟩,
   ⟨693, -1, 1⟩,
   ⟨-9, 0, -1⟩,
   ⟨-3465, 0, -1⟩,
   ⟨330, 0, 0⟩,
   ⟨-99, 0, 1⟩,
   ⟨-33, 1, -1⟩,
   ⟨-462, 1, 0⟩,
   ⟨5, 1, 1⟩]

set_option maxRecDepth 10000 in
private theorem rows_candidatesNeg202 : rows (-202) = candidatesNeg202 := by decide +kernel

set_option maxRecDepth 10000 in
public theorem caseOne_certificate : ∀ x ∈ rows 280, ∀ y ∈ rows 127, ∀ z ∈ rows 127,
    1+x.d+y.d+z.d = 0 → 1+x.value 8+y.value 1+z.value 1 = 16 →
    443520*(x.d*y.d*z.d+(x.value 8)^2*y.d*z.d+(y.value 1)^2*x.d*z.d+
      (z.value 1)^2*x.d*y.d) = 1118208*x.d*y.d*z.d → False := by
  rw [rows_candidates280, rows_candidates127]
  decide +kernel

set_option maxRecDepth 10000 in
public theorem caseTwo_third_certificate : ∀ x ∈ rows 78, ∀ y ∈ rows (-329), ∀ z ∈ rows 127,
    1+x.d-y.d+z.d = 0 → 1+x.value 2-y.value (-7)+z.value 1 = 16 →
    443520*(x.d*y.d*z.d+(x.value 2)^2*y.d*z.d-(y.value (-7))^2*x.d*z.d+
      (z.value 1)^2*x.d*y.d) = 1118208*x.d*y.d*z.d →
    x = ⟨154, 1, 0⟩ ∧ y = ⟨-55, 0, 0⟩ ∧ z = ⟨-210, 0, -1⟩ := by
  rw [rows_candidates78, rows_candidatesNeg329, rows_candidates127]
  decide +kernel

set_option maxRecDepth 10000 in
public theorem caseTwo_first_certificate : ∀ p ∈ rows 153, ∀ q ∈ rows 153,
    154+p.d+q.d = 0 → 10+p.value 7+q.value 7 = 16 →
    (443520 : ℚ)/147456 *
      (100/154 + (p.value 7 : ℚ)^2/p.d + (q.value 7 : ℚ)^2/q.d) = 31/12 →
    p.a*p.b = 0 ∧ q.a*q.b = 0 := by
  rw [rows_candidates153]
  decide +kernel

set_option maxRecDepth 10000 in
public theorem caseTwo_second_certificate : ∀ r ∈ rows (-202),
    154-55+r.d = 0 → 10-7+r.value (-6) = 0 → r.a*r.b = 0 := by
  rw [rows_candidatesNeg202]
  decide +kernel
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.FirstThree.Arithmetic
