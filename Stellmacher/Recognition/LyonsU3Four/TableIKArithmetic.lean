module

public import Stellmacher.Recognition.LyonsU3Four.TableIKDegreeSeparation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

/-!
# Arithmetic elimination of Table I case K

The separated two-row orbit degrees force one degree to be -13, so Schur's
bound restricts every prime divisor of a degree to at most 14. Reciprocal bounds,
the residues modulo 64, and these prime exclusions then force the printed
`y₄ = 297` and one of `y₅, y₆ = -63`. Equations (K1) and (K2) give the remaining
sum 372 and reciprocal sum -172/9009. Clearing denominators gives a quadratic
with no root modulo 17, completing the contradiction.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 383–384.
The page images of
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`
were checked: the closing sum on p. 384 is 372, not the OCR's 312. Intermediate
signs here follow the matrix-derived (K1); the final modular contradiction is
an alternative to the source's last prime exclusions.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four.EarlyK
local macro "ratlin" : tactic => `(tactic| (simp only [div_eq_mul_inv, one_mul] at *; linarith))

private theorem recip_bounds (n : ℤ) (a b : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hn : (n : ℚ) ≤ -a ∨ b ≤ n) : -1/a ≤ 1/(n:ℚ) ∧ 1/(n:ℚ) ≤ 1/b := by
  rcases hn with hn | hn
  · have hn0 : (n:ℚ) < 0 := by linarith
    constructor
    · apply (le_div_iff_of_neg hn0).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ ha).2
      linarith
    · exact (div_nonpos_of_nonneg_of_nonpos (by norm_num) hn0.le).trans (by positivity)
  · constructor
    · exact (div_nonpos_of_nonpos_of_nonneg (by norm_num) ha.le).trans
        (div_nonneg (by norm_num) (by linarith))
    · exact div_le_div_of_nonneg_left (by norm_num) hb hn

private theorem forces_thirteen (a b z u v : ℤ)
    (hu : u ≤ -63 ∨ 65 ≤ u) (hv : v ≤ -63 ∨ 65 ≤ v)
    (ham : (a-51)%64=0) (hbm : (b-51)%64=0) (hzm : (z-41)%64=0)
    (hne : a ≠ b)
    (h1 : 1+9/(a:ℚ)+9/(b:ℚ)-81/(z:ℚ)+1/(u:ℚ)+1/(v:ℚ)=0) :
    a = -13 ∨ b = -13 := by
  by_contra hn
  have ha' : a ≤ -77 ∨ 51 ≤ a := by omega
  have hb' : b ≤ -77 ∨ 51 ≤ b := by omega
  obtain ⟨ul,uu⟩ := recip_bounds u 63 65 (by norm_num) (by norm_num) (by exact_mod_cast hu)
  obtain ⟨vl,vu⟩ := recip_bounds v 63 65 (by norm_num) (by norm_num) (by exact_mod_cast hv)
  have finish (s t : ℤ) (hs : s ≤ -141 ∨ 51 ≤ s) (ht : t ≤ -77 ∨ 51 ≤ t)
      (hh : 1+9/(s:ℚ)+9/(t:ℚ)-81/(z:ℚ)+1/(u:ℚ)+1/(v:ℚ)=0) : False := by
    obtain ⟨sl,su⟩ := recip_bounds s 141 51 (by norm_num) (by norm_num) (by exact_mod_cast hs)
    obtain ⟨tl,tu⟩ := recip_bounds t 77 51 (by norm_num) (by norm_num) (by exact_mod_cast ht)
    have zp : (0:ℚ) < z := by
      have hp : 0 < (81:ℚ)/z := by ratlin
      exact ((div_pos_iff.mp hp).resolve_right (by norm_num)).2
    have zlt : (z:ℚ) < 105 := by
      have hh' : (81:ℚ)/105 < 81/z := by ratlin
      have := (lt_div_iff₀ zp).mp hh'
      ratlin
    have ze : z = 41 := by
      have : (0:ℤ) < z := by exact_mod_cast zp
      have : z < 105 := by exact_mod_cast zlt
      omega
    rw [ze] at hh
    norm_num at hh
    ratlin
  by_cases he : a = -77
  · apply finish b a (by omega) ha'
    linear_combination h1
  · exact finish a b (by omega) hb' h1

private def SmallPrimes (n : ℤ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n.natAbs → p ≤ 14

private theorem exclude {n : ℤ} (hn : SmallPrimes n) (m : ℤ) (p : ℕ)
    (hp : p.Prime) (hlt : 14 < p) (hd : p ∣ m.natAbs) : n ≠ m := by
  intro he
  subst n
  have := hn p hp hd
  omega

private theorem y_gap (y : ℤ)
    (hym : (y-51)%64=0) (hne : y ≠ -13) (hs : SmallPrimes y) :
    y ≤ -77 ∨ 243 ≤ y := by
  have h51 := exclude hs 51 17 (by norm_num) (by norm_num) (by norm_num)
  have h115 := exclude hs 115 23 (by norm_num) (by norm_num) (by norm_num)
  have h179 := exclude hs 179 179 (by norm_num) (by norm_num) (by norm_num)
  omega

private theorem forces_297 (y z u v : ℤ)
    (hy : y ≤ -77 ∨ 243 ≤ y) (hu : u ≤ -63 ∨ 65 ≤ u) (hv : v ≤ -63 ∨ 65 ≤ v)
    (hzm : (z-41)%64=0) (hs : SmallPrimes z)
    (h1 : 4/13+9/(y:ℚ)-81/(z:ℚ)+1/(u:ℚ)+1/(v:ℚ)=0) : z = 297 := by
  obtain ⟨yl,yu⟩ := recip_bounds y 77 243 (by norm_num) (by norm_num) (by exact_mod_cast hy)
  obtain ⟨ul,uu⟩ := recip_bounds u 63 65 (by norm_num) (by norm_num) (by exact_mod_cast hu)
  obtain ⟨vl,vu⟩ := recip_bounds v 63 65 (by norm_num) (by norm_num) (by exact_mod_cast hv)
  have zp : (0:ℚ) < z := by
    have hp : 0 < (81:ℚ)/z := by ratlin
    exact ((div_pos_iff.mp hp).resolve_right (by norm_num)).2
  have zlo : (169:ℚ) < z := by
    have hh : (81:ℚ)/z < 81/169 := by ratlin
    have := (div_lt_iff₀ zp).mp hh
    ratlin
  have zhi : (z:ℚ) < 553 := by
    have hh : (81:ℚ)/553 < 81/z := by ratlin
    have := (lt_div_iff₀ zp).mp hh
    ratlin
  have h233 := exclude hs 233 233 (by norm_num) (by norm_num) (by norm_num)
  have h361 := exclude hs 361 19 (by norm_num) (by norm_num) (by norm_num)
  have h425 := exclude hs 425 17 (by norm_num) (by norm_num) (by norm_num)
  have h489 := exclude hs 489 163 (by norm_num) (by norm_num) (by norm_num)
  have : 169 < z := by exact_mod_cast zlo
  have : z < 553 := by exact_mod_cast zhi
  omega

private theorem u_gap (u : ℤ) (hu : u ≤ -63 ∨ 65 ≤ u)
    (hum : (u-1)%64=0) (hne : u ≠ -63) (hs : SmallPrimes u) :
    u ≤ -511 ∨ 65 ≤ u := by
  have h127 := exclude hs (-127) 127 (by norm_num) (by norm_num) (by norm_num)
  have h191 := exclude hs (-191) 191 (by norm_num) (by norm_num) (by norm_num)
  have h255 := exclude hs (-255) 17 (by norm_num) (by norm_num) (by norm_num)
  have h319 := exclude hs (-319) 29 (by norm_num) (by norm_num) (by norm_num)
  have h383 := exclude hs (-383) 383 (by norm_num) (by norm_num) (by norm_num)
  have h447 := exclude hs (-447) 149 (by norm_num) (by norm_num) (by norm_num)
  omega

private theorem forces_sixtythree (y u v : ℤ)
    (hy : y ≤ -77 ∨ 243 ≤ y) (hu : u ≤ -63 ∨ 65 ≤ u) (hv : v ≤ -63 ∨ 65 ≤ v)
    (hym : (y-51)%64=0) (hum : (u-1)%64=0) (hvm : (v-1)%64=0)
    (sy : SmallPrimes y) (su : SmallPrimes u) (sv : SmallPrimes v)
    (h1 : 9/(y:ℚ)+1/(u:ℚ)+1/(v:ℚ)= -5/143) : u = -63 ∨ v = -63 := by
  obtain ⟨_,uu⟩ := recip_bounds u 63 65 (by norm_num) (by norm_num) (by exact_mod_cast hu)
  obtain ⟨_,vu⟩ := recip_bounds v 63 65 (by norm_num) (by norm_num) (by exact_mod_cast hv)
  have yn : y ≠ -77 := by
    intro he
    rw [he] at h1
    norm_num at h1
    ratlin
  have h141 := exclude sy (-141) 47 (by norm_num) (by norm_num) (by norm_num)
  have h205 := exclude sy (-205) 41 (by norm_num) (by norm_num) (by norm_num)
  have h269 := exclude sy (-269) 269 (by norm_num) (by norm_num) (by norm_num)
  have hy' : y ≤ -333 ∨ 243 ≤ y := by omega
  obtain ⟨yl,_⟩ := recip_bounds y 333 243 (by norm_num) (by norm_num) (by exact_mod_cast hy')
  by_contra hn
  have hu' := u_gap u hu hum (by omega) su
  have hv' := u_gap v hv hvm (by omega) sv
  obtain ⟨ul,_⟩ := recip_bounds u 511 65 (by norm_num) (by norm_num) (by exact_mod_cast hu')
  obtain ⟨vl,_⟩ := recip_bounds v 511 65 (by norm_num) (by norm_num) (by exact_mod_cast hv')
  ratlin

private theorem closing_contradiction (y v : ℤ) (hy : y ≠ 0) (hv : v ≠ 0)
    (hsum : y+v=372) (hrec : 9/(y:ℚ)+1/(v:ℚ)= -172/9009) : False := by
  have hyq : (y:ℚ) ≠ 0 := by exact_mod_cast hy
  have hvq : (v:ℚ) ≠ 0 := by exact_mod_cast hv
  have hp : 172*y*v+9009*(9*v+y)=0 := by
    have hh : (172:ℚ)*y*v+9009*(9*v+y)=0 := by
      field_simp at hrec
      nlinarith [hrec]
    exact_mod_cast hh
  have hpoly : 43*y*y+2022*y-7540533=0 := by
    have he : v = 372-y := by omega
    rw [he] at hp
    nlinarith [hp]
  have hmod := congrArg (fun n : ℤ => n % 17) hpoly
  simp only [Int.sub_emod, Int.add_emod, Int.mul_emod, Int.emod_emod] at hmod
  have hlo := Int.emod_nonneg y (by norm_num : (17:ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos y (by norm_num : (0:ℤ) < 17)
  interval_cases he : y % 17 <;> norm_num [he] at hmod

private theorem after_thirteen (y z u v : ℤ)
    (hu : u ≤ -63 ∨ 65 ≤ u) (hv : v ≤ -63 ∨ 65 ≤ v)
    (hym : (y-51)%64=0) (hzm : (z-41)%64=0)
    (hum : (u-1)%64=0) (hvm : (v-1)%64=0) (hne : y ≠ -13)
    (sy : SmallPrimes y) (sz : SmallPrimes z) (su : SmallPrimes u) (sv : SmallPrimes v)
    (h1 : 4/13+9/(y:ℚ)-81/(z:ℚ)+1/(u:ℚ)+1/(v:ℚ)=0)
    (h2 : y-z+u+v=12) : False := by
  have hy := y_gap y hym hne sy
  have hz := forces_297 y z u v hy hu hv hzm sz h1
  subst z
  have hr : 9/(y:ℚ)+1/(u:ℚ)+1/(v:ℚ)= -5/143 := by ratlin
  have hs := forces_sixtythree y u v hy hu hv hym hum hvm sy su sv hr
  rcases hs with he | he
  · apply closing_contradiction y v (by omega) (by omega) (by omega)
    rw [he] at hr
    norm_num at hr
    ratlin
  · apply closing_contradiction y u (by omega) (by omega) (by omega)
    rw [he] at hr
    norm_num at hr
    ratlin

/-- The separated-degree case K has no normalized degree solution. -/
theorem impossible_normalized {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) : False := by
  have eqs := equations hd ho
  have hne := degrees_ne hd ho
  have hu := degree_bounds hd 6 (by decide)
  have hv := degree_bounds hd 7 (by decide)
  change x 6 ≤ -63 ∨ 65 ≤ x 6 at hu
  change x 7 ≤ -63 ∨ 65 ≤ x 7 at hv
  have hm2 := degree_mod hd 2
  have hm3 := degree_mod hd 3
  have hm5 := degree_mod hd 5
  have hm6 := degree_mod hd 6
  have hm7 := degree_mod hd 7
  change (x 2 + -51) % 64 = 0 at hm2
  change (x 3 + -51) % 64 = 0 at hm3
  change (x 5 + 87) % 64 = 0 at hm5
  change (x 6 + 63) % 64 = 0 at hm6
  change (x 7 + 63) % 64 = 0 at hm7
  have he := forces_thirteen (x 2) (x 3) (x 5) (x 6) (x 7) hu hv
    (by omega) (by omega) (by omega) hne eqs.h₁
  have bound (p : ℕ) (hpp : p.Prime) (hpg : p ∣ g) : p ≤ 14 := by
    rcases he with he | he
    · exact prime_bound_two hp hne he p hpp hpg
    · exact prime_bound_three hp hne he p hpp hpg
  have smooth (i : Fin 8) : SmallPrimes (x i) := by
    intro p hpp hpd
    exact bound p hpp (hpd.trans (degree_dvd hp i))
  have h1 := eqs.h₁
  have h2 := eqs.h₂
  rcases he with he | he
  · apply after_thirteen (x 3) (x 5) (x 6) (x 7) hu hv
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (smooth 3) (smooth 5) (smooth 6) (smooth 7)
    · rw [he] at h1
      norm_num at h1
      ratlin
    · omega
  · apply after_thirteen (x 2) (x 5) (x 6) (x 7) hu hv
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (smooth 2) (smooth 5) (smooth 6) (smooth 7)
    · rw [he] at h1
      norm_num at h1
      ratlin
    · omega

end Stellmacher.Recognition.LyonsU3Four.EarlyK
