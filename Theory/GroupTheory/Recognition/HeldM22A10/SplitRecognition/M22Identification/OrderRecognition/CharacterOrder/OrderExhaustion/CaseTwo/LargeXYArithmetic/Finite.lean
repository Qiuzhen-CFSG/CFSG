module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeConstraints
public import Mathlib.Data.Int.Sqrt

/-!
# Complete finite enumerators for the two selected-degree cases

Divisors of `1118208*d*e` split into divisors of `4096*3*7*13`, `|d|` and
`|e|`. Both signs are included. Completing the square proves coverage of the
integer quadratic solver; its linear and bounded constant cases are explicit.
The row enumerator retains all nine multiplicity pairs and both degree signs.

These are the finite arithmetic tools for the omitted elimination in Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY

@[expose] public def smallDivisors (n : ℕ) : List ℕ :=
  (List.range (n+1)).filter fun d => n % d == 0

public theorem mem_smallDivisors {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) :
    d ∈ smallDivisors n := by
  exact List.mem_filter.mpr ⟨List.mem_range.mpr
    (Nat.lt_succ_of_le (Nat.le_of_dvd hn hd)), by simpa [Nat.dvd_iff_mod_eq_zero] using hd⟩

@[expose] public def kDivisors : List ℕ :=
  [1,2,4,8,16,32,64,128,256,512,1024,2048,4096].flatMap fun a =>
    [1,3].flatMap fun b => [1,7].flatMap fun c => [1,13].map fun d => a*b*c*d

public theorem mem_kDivisors {n : ℕ} (hn : n ∣ 1118208) : n ∈ kDivisors := by
  change n ∣ 4096*3*7*13 at hn
  obtain ⟨abc,d,habc,hd,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hn
  obtain ⟨ab,c,hab,hc,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul habc
  obtain ⟨a,b,ha,hb,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hab
  have ham : a ∈ ([1,2,4,8,16,32,64,128,256,512,1024,2048,4096] : List ℕ) := by
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (show a ∣ 2^12 from ha)
    interval_cases i <;> decide
  have hbm : b ∈ ([1,3] : List ℕ) := by
    have := Nat.le_of_dvd (by decide : 0 < 3) hb
    interval_cases b <;> norm_num at *
  have hcm : c ∈ ([1,7] : List ℕ) := by
    have := Nat.le_of_dvd (by decide : 0 < 7) hc
    interval_cases c <;> norm_num at *
  have hdm : d ∈ ([1,13] : List ℕ) := by
    have := Nat.le_of_dvd (by decide : 0 < 13) hd
    interval_cases d <;> norm_num at *
  exact List.mem_flatMap.mpr ⟨a,ham,List.mem_flatMap.mpr ⟨b,hbm,
    List.mem_flatMap.mpr ⟨c,hcm,List.mem_map.mpr ⟨d,hdm,rfl⟩⟩⟩⟩

@[expose] public def denominators (d e : ℤ) : List ℤ :=
  (smallDivisors d.natAbs).flatMap fun a : ℕ =>
    (smallDivisors e.natAbs).flatMap fun b : ℕ => kDivisors.flatMap fun k : ℕ =>
      let n : ℤ := (k*a*b : ℕ)
      [n, -n]

public theorem mem_denominators {d e P : ℤ} (hd : d ≠ 0) (he : e ≠ 0)
    (hP : P ∣ 1118208*d*e) : P ∈ denominators d e := by
  have hn : P.natAbs ∣ 1118208*d.natAbs*e.natAbs := by
    simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr hP
  obtain ⟨ka,b,hka,hb,habs⟩ := exists_dvd_and_dvd_of_dvd_mul hn
  obtain ⟨k,a,hk,ha,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hka
  refine List.mem_flatMap.mpr ⟨a,mem_smallDivisors (Int.natAbs_pos.mpr hd) ha,
    List.mem_flatMap.mpr ⟨b,mem_smallDivisors (Int.natAbs_pos.mpr he) hb,
      List.mem_flatMap.mpr ⟨k,mem_kDivisors hk, ?_⟩⟩⟩
  have heq : (P.natAbs : ℤ) = k*a*b := by exact_mod_cast habs
  dsimp only
  push_cast
  rw [← heq, Int.natCast_natAbs]
  rcases le_total 0 P with h | h
  · simp [abs_of_nonneg h]
  · simp [abs_of_nonpos h]

/-- All roots, including linear polynomials and bounded constant-polynomial roots. -/
@[expose] public def roots (A B C : ℤ) : List ℤ :=
  if A = 0 then
    if B = 0 then (List.range 225).map Int.ofNat else [-C / B]
  else
    let D := B^2 - 4*A*C
    let s := Int.sqrt D
    if s*s = D then [(-B+s)/(2*A), (-B-s)/(2*A)] else []

public theorem mem_roots {A B C u : ℤ} (h : A*u^2+B*u+C=0)
    (hconst : A = 0 → B = 0 → 0 ≤ u ∧ u < 225) : u ∈ roots A B C := by
  by_cases hA : A = 0
  · by_cases hB : B = 0
    · obtain ⟨hu, hv⟩ := hconst hA hB
      simp only [roots, hA, hB, ↓reduceIte]
      exact List.mem_map.mpr ⟨u.toNat,List.mem_range.mpr (by omega),
        Int.toNat_of_nonneg hu⟩
    · have he : -C = u*B := by rw [hA] at h; nlinarith
      have heq := Int.ediv_eq_of_eq_mul_left hB he
      simpa [roots, hA, hB] using heq.symm
  · have hsq : (2*A*u+B)*(2*A*u+B) = B^2-4*A*C := by
      linear_combination 4*A*h
    have hs := (Int.exists_mul_self _).mp ⟨_,hsq⟩
    have habs : Int.sqrt (B^2-4*A*C) = |2*A*u+B| := by
      rw [← hsq, Int.sqrt_eq, Int.natCast_natAbs]
    have h2 : 2*A ≠ 0 := mul_ne_zero (by norm_num) hA
    simp only [roots, hA, ↓reduceIte, hs, List.mem_cons, List.not_mem_nil, or_false]
    rcases le_total 0 (2*A*u+B) with hsign | hsign
    · have he : -B + Int.sqrt (B^2-4*A*C) = u*(2*A) := by
        rw [habs, abs_of_nonneg hsign]; ring
      exact Or.inl (Int.ediv_eq_of_eq_mul_left h2 he).symm
    · have he : -B - Int.sqrt (B^2-4*A*C) = u*(2*A) := by
        rw [habs, abs_of_nonpos hsign]; ring
      exact Or.inr (Int.ediv_eq_of_eq_mul_left h2 he).symm

/-- Each row is represented by its value and its congruence offset. -/
@[expose] public def rows (q v : ℤ) : List (ℤ × ℤ) :=
  ([-1,0,1] : List ℤ).flatMap fun u => ([-1,0,1] : List ℤ).map fun w =>
    (v+8*u+3*w,q+280*u+45*w)

public theorem row_mem {g : ℕ} {q v d t : ℤ} (h : CaseTwoRowConditions g q v (d,t)) :
    ∃ r ∈ rows q v, t = r.1 ∧ (d+r.2)%128 = 0 := by
  obtain ⟨_,u,hu,w,hw,ht,hd⟩ := h
  refine ⟨(v+8*u+3*w,q+280*u+45*w),List.mem_flatMap.mpr
    ⟨u,hu,List.mem_map.mpr ⟨w,hw,rfl⟩⟩,ht,?_⟩
  convert Int.emod_eq_zero_of_dvd hd using 1
  congr 1
  ring

@[expose] public def largeRows (q v : ℤ) : List (ℤ × (ℤ × ℤ)) :=
  (rows q v).flatMap fun r =>
    (List.range (4*r.1^2).toNat).flatMap fun n : ℕ =>
      (([(n : ℤ),-(n : ℤ)]).filter fun d => d != 0 && (d+r.2)%128 == 0).map
        fun d => (d,r)

public theorem largeRow_mem {q v d : ℤ} {r : ℤ × ℤ} (hr : r ∈ rows q v)
    (hd : d ≠ 0) (hc : (d+r.2)%128 = 0) (hb : (d.natAbs : ℤ) < 4*r.1^2) :
    (d,r) ∈ largeRows q v := by
  refine List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr
    ⟨d.natAbs,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨d,?_,rfl⟩⟩⟩
  apply List.mem_filter.mpr
  refine ⟨?_, by simp [hd,hc]⟩
  rw [Int.natCast_natAbs]
  rcases le_total 0 d with h | h
  · simp [abs_of_nonneg h]
  · simp [abs_of_nonpos h]

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY
