module

public import Stellmacher.Recognition.LyonsU3Four.TableIEarlyBounds
import Mathlib.Tactic.FieldSimp

/-!
# The arithmetic alternatives in Table I case B

The signed multiplicity bounds and equations (B1)–(B4) leave only three
configurations: `(x₁,y₃)=(-141,-471)`, `(y₄,y₅)=(118,52)`, or
`(y₃,y₅)=(41,-12)`. Each is excluded by a prime divisor in the owning
elimination module. The proof follows the split `x₁ < -77` / `x₁ = -77`;
sign information and the residue classes sharpen the reciprocal bounds.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer.
Math. Soc. 164 (1972), pp. 382–383. The signs were checked in the page images
of `refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four

private theorem lower_bound (n : ℤ) (a C : ℚ) (ha : 0 < a) (hC : 0 ≤ C)
    (hn : (n : ℚ) ≤ -a ∨ (0 : ℚ) < n) : -C/a ≤ C/n := by
  rcases hn with hn | hn
  · have hn' : (n : ℚ) < 0 := by linarith
    apply (le_div_iff_of_neg hn').2
    have hh : C / (-(n : ℚ)) ≤ C / a :=
      div_le_div_of_nonneg_left hC ha (by linarith)
    have := (div_le_iff₀ (show (0 : ℚ) < -n by linarith)).1 hh
    have he : (-C/a) * (n : ℚ) = (C/a)*(-n) := by ring
    rw [he]
    exact this
  · exact (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le).trans
      (div_nonneg hC hn.le)

private theorem upper_bound (n : ℤ) (b C : ℚ) (hb : 0 < b) (hC : 0 ≤ C)
    (hn : (n : ℚ) < 0 ∨ b ≤ n) : C/n ≤ C/b := by
  rcases hn with hn | hn
  · exact (div_nonpos_of_nonneg_of_nonpos hC hn.le).trans (by positivity)
  · exact div_le_div_of_nonneg_left hC hb hn

set_option maxHeartbeats 800000 in
/-- The rational equations of case B force one of three prime obstructions. -/
theorem tableI_B_arithmetic (x a b c d e : ℤ)
    (hx : x ≤ -77) (ha : a ≤ -75 ∨ 53 ≤ a) (hb : b ≤ -75 ∨ 53 ≤ b)
    (hc : c ≤ -87 ∨ 41 ≤ c) (hd : d ≤ -138 ∨ 54 ≤ d)
    (he : e ≤ -12 ∨ 52 ≤ e)
    (hxm : (x-51)%64=0) (ham : (a-53)%64=0) (hbm : (b-53)%64=0)
    (hcm : (c-41)%64=0) (hdm : (d-54)%64=0) (hem : (e-52)%64=0)
    (h1 : 1+18/(x:ℚ)-81/(c:ℚ)+36/(d:ℚ)-16/(e:ℚ)=0)
    (h2 : 2+82/(x:ℚ)+25/(a:ℚ)+25/(b:ℚ)+108/(d:ℚ)-16/(e:ℚ)=0)
    (h3 : 1+2*x-c+d-e=0) (h4 : 1+a+b+c+2*d=0) :
    (x = -141 ∧ c = -471) ∨ (d = 118 ∧ e = 52) ∨ (c = 41 ∧ e = -12) := by
  have la : -(25:ℚ)/75 ≤ 25/a := lower_bound a 75 25 (by norm_num) (by norm_num)
    (by exact_mod_cast (show a ≤ -75 ∨ 0 < a by omega))
  have lb : -(25:ℚ)/75 ≤ 25/b := lower_bound b 75 25 (by norm_num) (by norm_num)
    (by exact_mod_cast (show b ≤ -75 ∨ 0 < b by omega))
  have ld : -(108:ℚ)/138 ≤ 108/d := lower_bound d 138 108 (by norm_num) (by norm_num)
    (by exact_mod_cast (show d ≤ -138 ∨ 0 < d by omega))
  have ue : (16:ℚ)/e ≤ 16/52 := upper_bound e 52 16 (by norm_num) (by norm_num)
    (by exact_mod_cast (show e < 0 ∨ 52 ≤ e by omega))
  have sign : 0 < a ∨ 0 < b ∨ 0 < d ∨ e < 0 := by omega
  have pa (h : 0 < a) : (0:ℚ) ≤ 25/a := by positivity
  have pb (h : 0 < b) : (0:ℚ) ≤ 25/b := by positivity
  have pd (h : 0 < d) : (0:ℚ) ≤ 108/d := by positivity
  have ne (h : e < 0) : (16:ℚ)/e ≤ 0 := div_nonpos_of_nonneg_of_nonpos
    (by norm_num) (by exact_mod_cast (show e ≤ 0 by omega))
  by_cases xsmall : x < -77
  · have x141 : x ≤ -141 := by omega
    have lx : -(82:ℚ)/141 ≤ 82/x := lower_bound x 141 82 (by norm_num) (by norm_num)
      (Or.inl (by exact_mod_cast x141))
    have dn : d ≤ -138 := by
      rcases hd with hd | hd
      · exact hd
      · have := pd (by omega)
        linarith
    have dd : d = -138 := by
      by_contra h
      have d202 : d ≤ -202 := by omega
      have ld' : -(108:ℚ)/202 ≤ 108/d := lower_bound d 202 108 (by norm_num) (by norm_num)
        (Or.inl (by exact_mod_cast d202))
      rcases sign with sa | sb | sd | se
      · have := pa sa; linarith
      · have := pb sb; linarith
      · omega
      · have := ne se; linarith
    have xx : x = -141 := by
      by_contra h
      have x205 : x ≤ -205 := by omega
      have lx' : -(82:ℚ)/205 ≤ 82/x := lower_bound x 205 82 (by norm_num) (by norm_num)
        (Or.inl (by exact_mod_cast x205))
      rcases sign with sa | sb | sd | se
      · have := pa sa; linarith
      · have := pb sb; linarith
      · omega
      · have := ne se; linarith
    have ab : a = -75 ∨ b = -75 := by
      by_contra h
      have la' : -(25:ℚ)/139 ≤ 25/a := lower_bound a 139 25 (by norm_num) (by norm_num)
        (by exact_mod_cast (show a ≤ -139 ∨ 0 < a by omega))
      have lb' : -(25:ℚ)/139 ≤ 25/b := lower_bound b 139 25 (by norm_num) (by norm_num)
        (by exact_mod_cast (show b ≤ -139 ∨ 0 < b by omega))
      rcases sign with sa | sb | sd | se
      · have := pa sa; linarith
      · have := pb sb; linarith
      · omega
      · have := ne se; linarith
    have finish (u w : ℤ) (hu : u = -75) (hw : w ≤ -75 ∨ 53 ≤ w)
        (hh2 : 2+82/(x:ℚ)+25/(u:ℚ)+25/(w:ℚ)+108/(d:ℚ)-16/(e:ℚ)=0)
        (hh4 : 1+u+w+c+2*d=0) : c = -471 := by
      have wp : 0 < w := by
        by_contra wn
        have cn : 425 ≤ c := by omega
        have cu : (81:ℚ)/c ≤ 81/425 := upper_bound c 425 81 (by norm_num) (by norm_num)
          (Or.inr (by exact_mod_cast cn))
        have wnq : (25:ℚ)/w ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num)
          (by exact_mod_cast (show w ≤ 0 by omega))
        rw [xx, dd] at h1
        rw [xx, dd, hu] at hh2
        norm_num at h1 hh2
        linarith
      have wpq : (0:ℚ) ≤ 25/w := by positivity
      have ee : e = 52 := by
        by_contra h
        have ue' : (16:ℚ)/e ≤ 16/116 := upper_bound e 116 16 (by norm_num) (by norm_num)
          (by exact_mod_cast (show e < 0 ∨ 116 ≤ e by omega))
        rw [xx, dd, hu] at hh2
        norm_num at hh2
        linarith
      omega
    left
    refine ⟨xx, ?_⟩
    rcases ab with ab | ab
    · exact finish a b ab hb h2 h4
    · apply finish b a ab ha
      · linarith [h2]
      · omega
  · have xx : x = -77 := by omega
    rw [xx] at h1 h2
    norm_num at h1 h2
    by_cases dp : 0 < d
    · have dpq := pd dp
      have aa : a = -75 := by
        by_contra h
        have la' : -(25:ℚ)/139 ≤ 25/a := lower_bound a 139 25 (by norm_num) (by norm_num)
          (by exact_mod_cast (show a ≤ -139 ∨ 0 < a by omega))
        linarith
      have bb : b = -75 := by
        by_contra h
        have lb' : -(25:ℚ)/139 ≤ 25/b := lower_bound b 139 25 (by norm_num) (by norm_num)
          (by exact_mod_cast (show b ≤ -139 ∨ 0 < b by omega))
        linarith
      have ee : e = 52 := by
        by_contra h
        have ue' : (16:ℚ)/e ≤ 16/116 := upper_bound e 116 16 (by norm_num) (by norm_num)
          (by exact_mod_cast (show e < 0 ∨ 116 ≤ e by omega))
        linarith
      exact Or.inr (Or.inl ⟨by omega, ee⟩)
    · have dn : d ≤ -138 := by omega
      have ld36 : -(36:ℚ)/138 ≤ 36/d := lower_bound d 138 36 (by norm_num) (by norm_num)
        (Or.inl (by exact_mod_cast dn))
      have cp : 0 < c := by
        by_contra h
        have cnq : (81:ℚ)/c ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num)
          (by exact_mod_cast (show c ≤ 0 by omega))
        linarith
      have en : e < 0 := by omega
      have neq := ne en
      have cc : c = 41 ∨ c = 105 := by
        have cb : c < 169 := by
          by_contra h
          have uc : (81:ℚ)/c ≤ 81/169 := upper_bound c 169 81 (by norm_num) (by norm_num)
            (Or.inr (by exact_mod_cast (show 169 ≤ c by omega)))
          linarith
        omega
      rcases cc with cc | cc
      · have ee : e = -12 := by
          by_contra h
          have el : e ≤ -76 := by omega
          have le' : -(16:ℚ)/76 ≤ 16/e := lower_bound e 76 16 (by norm_num) (by norm_num)
            (Or.inl (by exact_mod_cast el))
          have ud : (36:ℚ)/d ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num)
            (by exact_mod_cast (show d ≤ 0 by omega))
          rw [cc] at h1
          norm_num at h1
          linarith
        exact Or.inr (Or.inr ⟨cc, ee⟩)
      · have ld72 : -(72:ℚ)/138 ≤ 72/d := lower_bound d 138 72 (by norm_num) (by norm_num)
          (Or.inl (by exact_mod_cast dn))
        have abp : 0 < a ∨ 0 < b := by omega
        rw [cc] at h1
        norm_num at h1
        have hdiff : (25:ℚ)/a+25/b+72/d = -(13:ℚ)/77-81/105 := by
          linear_combination h2 - h1
        rcases abp with ap | bp
        · have := pa ap
          exfalso
          linarith only [this, la, lb, ld72, hdiff]
        · have := pb bp
          exfalso
          linarith only [this, la, lb, ld72, hdiff]
end Stellmacher.Recognition.LyonsU3Four
