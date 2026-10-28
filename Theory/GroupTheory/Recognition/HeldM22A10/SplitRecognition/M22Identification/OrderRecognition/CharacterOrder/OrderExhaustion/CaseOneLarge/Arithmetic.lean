module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseOneLarge.Configurations

import Mathlib.Tactic

/-!
# Exhaustion of the first large-ratio integer system

Every unit triple of sum one occurs in the six explicit column patterns. A
large ratio bounds the selected signed degree by 1444 in absolute value; the
Sylow restriction places it in one of 25 residue positions. Kernel-checked
coverage then selects a configuration, regardless of the constituent chosen.

Divisibility of the two other degrees makes the Suzuki denominator divide
1118208 x (1+x). The quadratic bound proved for the configuration bounds the
next degree. Its residue gives a finite interval position, and the checked
exhaustion contradicts the necessary order and degree divisibilities. This
proves the full integer system impossible without assuming an ambient-order
bound or introducing a numerical premise.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15. The reduction to a bounded second
degree and the complete finite exhaustion fill in the omitted case analysis.
-/

open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.CaseOneLarge

private theorem finite_patterns : ∀ f : Fin 3 → Fin 3,
    (f 0 : ℤ) + (f 1 : ℤ) + (f 2 : ℤ) = 4 →
      ∃ i : Fin 6, ∀ j, (f j : ℤ) - 1 = patterns i j := by
  decide +kernel

private theorem pattern_complete (a : Fin 3 → ℤ)
    (ha : ∀ j, -1 ≤ a j ∧ a j ≤ 1) (hs : ∑ j, a j = 1) :
    ∃ i : Fin 6, a = patterns i := by
  let f (j : Fin 3) : Fin 3 := ⟨(a j + 1).toNat, by have := ha j; omega⟩
  have hf (j : Fin 3) : (f j : ℤ) - 1 = a j := by
    dsimp [f]
    have := ha j
    omega
  have he : (f 0 : ℤ) + (f 1 : ℤ) + (f 2 : ℤ) = 4 := by
    have hs' : a 0 + a 1 + a 2 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hs
    have h0 := hf 0
    have h1 := hf 1
    have h2 := hf 2
    omega
  obtain ⟨i, hi⟩ := finite_patterns f he
  exact ⟨i, funext fun j => (hf j).symm.trans (hi j)⟩

private theorem value_bound : ∀ p : Fin 6 × Fin 6, ∀ j : Fin 3,
    (patternValue p j).natAbs ≤ 19 := by
  decide +kernel

private theorem degree_position (p : Fin 6 × Fin 6) (j : Fin 3) (x : ℤ)
    (hr : x % 128 = patternResidue p j)
    (hb : x.natAbs < 4 * (patternValue p j).natAbs ^ 2) :
    ∃ k : Fin 25, x = patternDegree p j k := by
  have hv := value_bound p j
  have hx : x.natAbs < 1444 := by
    calc
      x.natAbs < 4 * (patternValue p j).natAbs ^ 2 := hb
      _ ≤ 4 * 19^2 := by gcongr
      _ = 1444 := by norm_num
  have hx' : (x.natAbs : ℤ) < 1444 := by exact_mod_cast hx
  rw [Int.natCast_natAbs] at hx'
  have hxx := abs_lt.mp hx'
  have he := Int.emod_add_ediv_mul x 128
  have he0 := Int.emod_nonneg x (by norm_num : (128 : ℤ) ≠ 0)
  have he1 := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 128)
  let k : Fin 25 := ⟨(x / 128 + 12).toNat, by omega⟩
  refine ⟨k, ?_⟩
  have hk : (k.val : ℤ) = x / 128 + 12 := by dsimp [k]; omega
  dsimp [patternDegree]
  rw [hk, ← hr]
  omega

private theorem cyclic_sum (d : Fin 3 → ℤ) (j : Fin 3) :
    d j + d (j+1) + d (j+2) = ∑ i, d i := by
  have he : (∑ i, d i) = d 0 + (d 1 + d 2) := by simp [Fin.sum_univ_succ]
  rw [he]
  fin_cases j <;> dsimp [Fin.add_def] <;> ring

private theorem cyclic_numerator (d t : Fin 3 → ℤ) (j : Fin 3) :
    d j * d (j+1) * d (j+2) + t j ^ 2 * d (j+1) * d (j+2) +
      t (j+1)^2 * d j * d (j+2) + t (j+2)^2 * d j * d (j+1) =
      suzukiNumerator d t := by
  fin_cases j <;> dsimp [suzukiNumerator, Fin.add_def] <;> ring

private theorem cyclic_product (d : Fin 3 → ℤ) (j : Fin 3) :
    d j * d (j+1) * d (j+2) = d 0 * d 1 * d 2 := by
  fin_cases j <;> dsimp [Fin.add_def] <;> ring

private theorem next_degree_position (c : Configuration) (y : ℤ)
    (hr0 : 0 ≤ c.r) (hr1 : c.r < 128) (hr : y % 128 = c.r)
    (hy : |y| < 128 * (c.span : ℤ)) :
    ∃ l : ℕ, l < 2*c.span ∧ y = c.r + 128 * (l - c.span : ℤ) := by
  have hab := abs_lt.mp hy
  have he := Int.emod_add_ediv_mul y 128
  let l := (y / 128 + c.span).toNat
  have hl : (l : ℤ) = y / 128 + c.span := by dsimp [l]; omega
  refine ⟨l, ?_, ?_⟩ <;> omega

private theorem configuration_impossible (g : ℤ) (c : Configuration) (hc : c ∈ configurations)
    (y z : ℤ) (hy : y ≠ 0) (hz : z ≠ 0) (hr : y % 128 = c.r)
    (hs : c.x + y + z = -1)
    (hxd : c.x ∣ g) (hyd : y ∣ g) (hzd : z ∣ g)
    (hg : 0 < g) (hgdiv : 40320 ∣ g) (h2 : ¬ 2 ∣ g / 40320) (h3 : ¬ 3 ∣ g / 40320)
    (he : g * (c.x*y*z+c.t^2*y*z+c.u^2*c.x*z+c.v^2*c.x*y) = 1118208*c.x*y*z) : False := by
  obtain ⟨hx, hx1, hr0, hr1, _, hB, hbound⟩ := configuration_bound c hc
  let P := c.x*y*z+c.t^2*y*z+c.u^2*c.x*z+c.v^2*c.x*y
  have hP : P ≠ 0 := by
    intro hh
    change g * P = _ at he
    rw [hh, mul_zero] at he
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hx) hy) hz) he.symm
  have hden : P ∣ 1118208*c.x*(1+c.x) := numerator_dvd_fixed g c.x y z c.t c.u c.v
    hy hz hyd hzd hs he
  have hM : 1118208*c.x*(1+c.x) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (by norm_num) hx)
    omega
  have hz' : z = -1-c.x-y := by omega
  have hquadratic : quadraticA c.x c.t*y^2+quadraticB c.x c.t c.u c.v*y+
      quadraticC c.x c.u = P := by
    dsimp [quadraticA, quadraticB, quadraticC, P]
    rw [hz']
    ring
  have hybound : |y| < 128*(c.span : ℤ) := abs_lt_of_quadratic_dvd
    (quadraticA c.x c.t) (quadraticB c.x c.t c.u c.v) (quadraticC c.x c.u)
    (1118208*c.x*(1+c.x)) y (128*c.span) (by positivity) hB hbound hM
    (hquadratic.symm ▸ hden)
  obtain ⟨l, hl, hyl⟩ := next_degree_position c y hr0 hr1 hr hybound
  have hge : 1118208*c.x*y*z / P = g := by
    rw [← he]
    simp [P, hP]
  have ht := configuration_excludes c hc l hl
  dsimp only at ht
  rw [← hyl, ← hz'] at ht
  change y ≠ 0 → z ≠ 0 → P ≠ 0 → P ∣ 1118208*c.x*(1+c.x) →
    P ∣ 1118208*c.x*y*z → 0 < 1118208*c.x*y*z/P → 40320 ∣ 1118208*c.x*y*z/P →
    ¬ 2 ∣ (1118208*c.x*y*z/P) / 40320 → ¬ 3 ∣ (1118208*c.x*y*z/P) / 40320 →
    c.x ∣ 1118208*c.x*y*z/P → y ∣ 1118208*c.x*y*z/P → z ∣ 1118208*c.x*y*z/P → False at ht
  rw [hge] at ht
  exact ht hy hz hP hden ⟨g, by dsimp [P]; simpa only [mul_comm] using he.symm⟩ hg hgdiv h2 h3 hxd hyd hzd

/-- The finite table exhausts all necessary integer data in the large-ratio case. -/
public theorem largeCaseData_impossible (g : ℤ) (S : LargeCaseData g)
    (hg : 0 < g) (hgdiv : 40320 ∣ g) (h2 : ¬ 2 ∣ g / 40320) (h3 : ¬ 3 ∣ g / 40320) : False := by
  obtain ⟨a, ha⟩ := pattern_complete S.fourth S.fourth_bounds S.fourth_sum
  have hb0 : ∀ j, -1 ≤ -S.fifth j ∧ -S.fifth j ≤ 1 := by
    intro j; have := S.fifth_bounds j; omega
  have hb1 : ∑ j, -S.fifth j = 1 := by rw [Finset.sum_neg_distrib, S.fifth_sum]; norm_num
  obtain ⟨b, hb⟩ := pattern_complete (fun j => -S.fifth j) hb0 hb1
  have hb' (j : Fin 3) : S.fifth j = -patterns b j := by have hh := congrFun hb j; omega
  let p : Fin 6 × Fin 6 := (a,b)
  have ht (j : Fin 3) : tripleValue S.fourth S.fifth j = patternValue p j := by
    simp only [tripleValue, patternValue, p, ha, hb']
    ring
  have hr (j : Fin 3) : S.degree j % 128 = patternResidue p j := by
    have hh := S.degree_congruence j
    rw [ha, hb'] at hh
    dsimp [patternResidue, p]
    split_ifs at hh ⊢ <;> omega
  obtain ⟨j, hj⟩ := S.large
  rw [ht] at hj
  obtain ⟨k, hk⟩ := degree_position p j (S.degree j) (hr j) hj
  have hx : patternDegree p j k ≠ 0 := hk ▸ S.degree_ne_zero j
  have hbk : (patternDegree p j k).natAbs < 4 * (patternValue p j).natAbs ^ 2 := hk ▸ hj
  obtain ⟨c, hc, hcx, hct, hcu, hcv, hcr⟩ := configurations_cover p j k hx hbk
  have hcx' : c.x = S.degree j := hcx.trans hk.symm
  apply configuration_impossible g c hc (S.degree (j+1)) (S.degree (j+2))
    (S.degree_ne_zero _) (S.degree_ne_zero _)
  · rw [hcr]; exact hr (j+1)
  · rw [hcx', cyclic_sum]; exact S.degree_sum
  · rw [hcx']; exact S.degree_dvd j
  · exact S.degree_dvd (j+1)
  · exact S.degree_dvd (j+2)
  · exact hg
  · exact hgdiv
  · exact h2
  · exact h3
  · rw [hcx', hct, hcu, hcv, ← ht, ← ht, ← ht]
    rw [cyclic_numerator]
    calc
      g * suzukiNumerator S.degree (tripleValue S.fourth S.fifth) =
        1118208*S.degree 0*S.degree 1*S.degree 2 := S.suzuki
      _ = 1118208*S.degree j*S.degree (j+1)*S.degree (j+2) := by
        have := cyclic_product S.degree j
        nlinarith only [this]

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.CaseOneLarge
