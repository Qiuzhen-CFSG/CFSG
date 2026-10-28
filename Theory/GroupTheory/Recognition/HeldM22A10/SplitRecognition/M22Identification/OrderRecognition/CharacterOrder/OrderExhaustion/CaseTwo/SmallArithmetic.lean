module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints


/-!
# Finite cofactor exhaustion for the second character decomposition

Every divisor of `40320h` splits into divisors of 128, 9, 5, 7 and h. This
constructs a complete finite list of possible signed degrees. Each row retains
all nine choices for its two final unit multiplicities and filters only by the
proved modulo-128 restriction congruence. The integer third Suzuki equation,
together with the degree and involution-value relations, eliminates every
cofactor except eleven from the complete list of positive h ≤ 55 prime to 6.

The finite calculation uses kernel reduction. Its lists are enumerated from
proved divisor bounds; no external search output is assumed. In particular,
cofactors one and fifty-five and both signs of every divisor are included.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15; the omitted arithmetic is supplied here.
-/

-- Efficient complete divisor enumeration by repeated splitting of products.
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion

/-- The divisor, value and restriction conditions for one signed row. -/
@[expose] public def CaseTwoRowConditions (g : ℕ) (q v : ℤ) (p : ℤ × ℤ) : Prop :=
  p.1 ∣ (g : ℤ) ∧ ∃ a ∈ ([-1,0,1] : List ℤ), ∃ b ∈ ([-1,0,1] : List ℤ),
    p.2 = v + 8*a + 3*b ∧ 128 ∣ p.1 + q + 280*a + 45*b

private def divisors40320 : List ℕ :=
  [1,2,4,8,16,32,64,128].flatMap fun a =>
    [1,3,9].flatMap fun b => [1,5].flatMap fun c => [1,7].map fun d => a*b*c*d

private theorem dvd128_mem (n : ℕ) (h : n ∣ 128) :
    n ∈ ([1,2,4,8,16,32,64,128] : List ℕ) := by
  have hb := Nat.le_of_dvd (by decide : 0 < 128) h
  interval_cases n <;> norm_num at *

private theorem dvd40320_mem (n : ℕ) (h : n ∣ 40320) : n ∈ divisors40320 := by
  change n ∣ 128 * 9 * 5 * 7 at h
  obtain ⟨abc, d, habc, hd, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
  obtain ⟨ab, c, hab, hc, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul habc
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hab
  have ham := dvd128_mem a ha
  have hbm : b ∈ ([1,3,9] : List ℕ) := by
    have hble := Nat.le_of_dvd (by decide : 0 < 9) hb
    interval_cases b <;> norm_num at *
  have hcm : c ∈ ([1,5] : List ℕ) := by
    have hcle := Nat.le_of_dvd (by decide : 0 < 5) hc
    interval_cases c <;> norm_num at *
  have hdm : d ∈ ([1,7] : List ℕ) := by
    have hdle := Nat.le_of_dvd (by decide : 0 < 7) hd
    interval_cases d <;> norm_num at *
  exact List.mem_flatMap.mpr ⟨a, ham, List.mem_flatMap.mpr ⟨b, hbm,
    List.mem_flatMap.mpr ⟨c, hcm, List.mem_map.mpr ⟨d, hdm, rfl⟩⟩⟩⟩

private def degreeDivisors (h : ℕ) : List ℕ :=
  divisors40320.flatMap fun a => ((List.range (h+1)).filter fun b => h % b == 0).map (a * ·)

private theorem degree_mem {h n : ℕ} (hh : 0 < h) (hd : n ∣ 40320*h) :
    n ∈ degreeDivisors h := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  exact List.mem_flatMap.mpr ⟨a, dvd40320_mem a ha,
    List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.le_of_dvd hh hb)), by simpa [Nat.dvd_iff_mod_eq_zero] using hb⟩, rfl⟩⟩

private def signedDivisors (h : ℕ) : List ℤ :=
  (degreeDivisors h).flatMap fun n : ℕ => [(n : ℤ), -(n : ℤ)]

private theorem signedDegree_mem {h : ℕ} {d : ℤ} (hh : 0 < h)
    (hd : d ∣ (40320*h : ℕ)) : d ∈ signedDivisors h := by
  have hm := degree_mem hh (show d.natAbs ∣ 40320*h by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd)
  apply (List.mem_flatMap (f := fun n : ℕ => [(n : ℤ), -(n : ℤ)])).mpr
  refine ⟨d.natAbs, hm, ?_⟩
  rw [Int.natCast_natAbs]
  rcases le_total 0 d with he | he
  · simp [abs_of_nonneg he]
  · simp [abs_of_nonpos he]

private def rowCandidates (h : ℕ) (q v : ℤ) : List (ℤ × ℤ) :=
  (signedDivisors h).flatMap fun d =>
    ([-1,0,1] : List ℤ).flatMap fun a =>
      (([-1,0,1] : List ℤ).filter fun b => (d + q + 280*a + 45*b) % 128 == 0).map
        fun b => (d, v + 8*a + 3*b)

private theorem row_mem {h : ℕ} {d t q v a b : ℤ} (hh : 0 < h)
    (hd : d ∣ (40320*h : ℕ)) (ha : a ∈ ([-1,0,1] : List ℤ))
    (hb : b ∈ ([-1,0,1] : List ℤ)) (ht : t = v + 8*a + 3*b)
    (hr : 128 ∣ d + q + 280*a + 45*b) : (d,t) ∈ rowCandidates h q v := by
  refine List.mem_flatMap.mpr ⟨d, signedDegree_mem hh hd,
    List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b,
      List.mem_filter.mpr ⟨hb, ?_⟩, ?_⟩⟩⟩
  · simpa using Int.emod_eq_zero_of_dvd hr
  · simp [ht]

private def thirdEquation (g : ℕ) (p q r : ℤ × ℤ) : Prop :=
  1 + p.1 - q.1 + r.1 = 0 ∧ 1 + p.2 - q.2 + r.2 = 16 ∧
    (g : ℤ) * (p.1*q.1*r.1 + p.2^2*q.1*r.1 - q.2^2*p.1*r.1 + r.2^2*p.1*q.1) =
      1118208*p.1*q.1*r.1

private instance (g : ℕ) (p q r : ℤ × ℤ) : Decidable (thirdEquation g p q r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private def smallCheck (h : ℕ) : Bool :=
  (rowCandidates h 78 2).all fun p =>
    (rowCandidates h (-329) (-7)).all fun q =>
      (rowCandidates h 127 1).all fun r =>
        decide (thirdEquation (40320*h) p q r → h = 11)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem small_checks :
    ([1,5,7,11,13,17,19,23,25,29,31,35,37,41,43,47,49,53,55] : List ℕ).all smallCheck = true := by
  decide +kernel

private theorem small_check
    (h : ℕ) (hh : h ∈ ([1,5,7,11,13,17,19,23,25,29,31,35,37,41,43,47,49,53,55] : List ℕ))
    (p : ℤ × ℤ) (hp : p ∈ rowCandidates h 78 2)
    (q : ℤ × ℤ) (hq : q ∈ rowCandidates h (-329) (-7))
    (r : ℤ × ℤ) (hr : r ∈ rowCandidates h 127 1) :
    thirdEquation (40320*h) p q r → h = 11 := by
  have hh' := List.all_eq_true.mp small_checks h hh
  have hp' := List.all_eq_true.mp hh' p hp
  have hq' := List.all_eq_true.mp hp' q hq
  exact of_decide_eq_true (List.all_eq_true.mp hq' r hr)


/-- Exhaust the complete cofactor list, retaining every sign and both free multiplicities. -/
public theorem caseTwo_small_integer_exhaustion (h : ℕ) (hp : 0 < h)
    (h2 : ¬ 2 ∣ h) (h3 : ¬ 3 ∣ h) (hb : h ≤ 55) (p q r : ℤ × ℤ)
    (hpRow : CaseTwoRowConditions (40320*h) 78 2 p)
    (hqRow : CaseTwoRowConditions (40320*h) (-329) (-7) q)
    (hrRow : CaseTwoRowConditions (40320*h) 127 1 r)
    (hdegree : 1 + p.1 - q.1 + r.1 = 0) (hvalue : 1 + p.2 - q.2 + r.2 = 16)
    (hsuzuki : (40320*h : ℕ) *
      (p.1*q.1*r.1 + p.2^2*q.1*r.1 - q.2^2*p.1*r.1 + r.2^2*p.1*q.1) =
        1118208*p.1*q.1*r.1) : h = 11 := by
  obtain ⟨hpd, a, ha, b, hb', hpt, hpr⟩ := hpRow
  obtain ⟨hqd, c, hc, d, hd, hqt, hqr⟩ := hqRow
  obtain ⟨hrd, e, he, f, hf, hrt, hrr⟩ := hrRow
  have hpMem : p ∈ rowCandidates h 78 2 := by
    simpa using row_mem hp hpd ha hb' hpt hpr
  have hqMem : q ∈ rowCandidates h (-329) (-7) := by
    simpa using row_mem hp hqd hc hd hqt hqr
  have hrMem : r ∈ rowCandidates h 127 1 := by
    simpa using row_mem hp hrd he hf hrt hrr
  exact small_check h (small_cofactor_mem h hp h2 h3 hb) p hpMem q hqMem r hrMem
    ⟨hdegree, hvalue, hsuzuki⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
