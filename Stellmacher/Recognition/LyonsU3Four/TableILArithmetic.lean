module

public import Stellmacher.Recognition.LyonsU3Four.TableIJKLSystems
import Mathlib.Tactic.FieldSimp

/-!
# The arithmetic contradiction in Table I case L

The actual matrix equations force one of the two degree labels to be `-13`.
Their sum and the signed bound on the third degree prove that these labels are
unequal, so the degree-13 row is separated and Schur's prime bound applies.
The positive order equation leaves third degree 90 or 154; the prime 47
excludes 154. The prime 29 excludes degree 116. Reciprocal bounds then force
one of the final two degrees to be 52. The remaining linear and reciprocal
equations give a quadratic with negative discriminant.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 384,
case (L). The page image was checked in
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
The final quadratic argument shortens the last numerical case split there.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four.EarlyL

private theorem reciprocal_upper (n : ℤ) (a b C : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hC : 0 ≤ C) (hn : (n : ℚ) ≤ -a ∨ b ≤ n) : C / n ≤ C / b := by
  rcases hn with hn | hn
  · exact (div_nonpos_of_nonneg_of_nonpos hC (by linarith)).trans (by positivity)
  · exact div_le_div_of_nonneg_left hC hb hn

private theorem reciprocal_lower (n : ℤ) (a b C : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hC : 0 ≤ C) (hn : (n : ℚ) ≤ -a ∨ b ≤ n) : -C / a ≤ C / n := by
  rw [neg_div]
  rcases hn with hn | hn
  · have hh := div_le_div_of_nonneg_left hC ha (show a ≤ -(n : ℚ) by linarith)
    simpa only [div_neg, neg_neg] using neg_le_neg hh
  · exact (neg_nonpos.mpr (div_nonneg hC (le_of_lt ha))).trans (div_nonneg hC (by linarith))

/-- The positive order equation bounds the third degree before using any prime bound. -/
private theorem third_degree_cases (a b c : ℤ) (hb : b ≤ -13 ∨ 51 ≤ b)
    (hc : c ≤ -38 ∨ 90 ≤ c) (hm : (c - 90) % 64 = 0)
    (hs : a + b + c = 0) (ha : a = -13)
    (h4 : 0 < 36/(a : ℚ) + 36/(b : ℚ) + 400/(c : ℚ)) :
    (c = 90 ∧ b = -77) ∨ (c = 154 ∧ b = -141) := by
  subst a
  have bb : (36 : ℚ) / b ≤ 36/51 :=
    reciprocal_upper b 13 51 36 (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast hb)
  have cp : (0 : ℚ) < c := by
    by_contra hh
    have : (400 : ℚ) / c ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)
    norm_num at h4
    linarith
  have cc : (c : ℚ) < 200 := by
    have hh : (36:ℚ)/13 - 36/51 < 400/(c:ℚ) := by norm_num at h4 ⊢; linarith
    have := (lt_div_iff₀ cp).mp hh
    linarith
  have cp' : 0 < c := by exact_mod_cast cp
  have cc' : c < 200 := by exact_mod_cast cc
  omega

/-- After the prime exclusions, the last three degrees give an impossible quadratic. -/
private theorem final_contradiction (u v w : ℤ)
    (hu : u ≤ -63 ∨ 65 ≤ u) (hv : v ≤ -12 ∨ 52 ≤ v)
    (hw : w ≤ -12 ∨ 52 ≤ w)
    (hvm : (v + 12) % 64 = 0) (hwm : (w + 12) % 64 = 0)
    (hv116 : v ≠ 116) (hw116 : w ≠ 116)
    (h1 : (191 : ℚ)/1001 + 1/(u:ℚ) - 16/(v:ℚ) - 16/(w:ℚ) = 0)
    (h2 : u - v - w = 89) : False := by
  have bu : -(1:ℚ)/63 ≤ 1/(u:ℚ) :=
    reciprocal_lower u 63 65 1 (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast hu)
  have cases52 : v = 52 ∨ w = 52 := by
    by_contra hh
    have vv : v ≤ -12 ∨ 180 ≤ v := by omega
    have ww : w ≤ -12 ∨ 180 ≤ w := by omega
    have bv : (16:ℚ)/v ≤ 16/180 :=
      reciprocal_upper v 12 180 16 (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast vv)
    have bw : (16:ℚ)/w ≤ 16/180 :=
      reciprocal_upper w 12 180 16 (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast ww)
    have vp : 180 ≤ v := by
      rcases vv with vv | vv
      · have : (16:ℚ)/v ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (by exact_mod_cast (show v ≤ 0 by omega))
        linarith
      · exact vv
    have wp : 180 ≤ w := by
      rcases ww with ww | ww
      · have : (16:ℚ)/w ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (by exact_mod_cast (show w ≤ 0 by omega))
        linarith
      · exact ww
    have : (0:ℚ) ≤ 1/(u:ℚ) := div_nonneg (by norm_num) (by exact_mod_cast (show 0 ≤ u by omega))
    linarith
  have u0 : (u:ℚ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
  have v0 : (v:ℚ) ≠ 0 := by exact_mod_cast (show v ≠ 0 by omega)
  have w0 : (w:ℚ) ≠ 0 := by exact_mod_cast (show w ≠ 0 by omega)
  rcases cases52 with rfl | rfl
  · have he : 1/(u:ℚ) - 16/(w:ℚ) = 9/77 := by norm_num at h1 ⊢; linarith
    field_simp at he
    have h2q : (u:ℚ) - w = 141 := by exact_mod_cast (show u-w=141 by omega)
    rw [show (u:ℚ) = w + 141 by linarith] at he
    nlinarith [sq_nonneg (3*(w:ℚ)+404)]
  · have he : 1/(u:ℚ) - 16/(v:ℚ) = 9/77 := by norm_num at h1 ⊢; linarith
    field_simp at he
    have h2q : (u:ℚ) - v = 141 := by exact_mod_cast (show u-v=141 by omega)
    rw [show (u:ℚ) = v + 141 by linarith] at he
    nlinarith [sq_nonneg (3*(v:ℚ)+404)]

/-- The normalized degree and order constraints for Table I case L are inconsistent. -/
theorem impossible_normalized {x : Fin 10 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) : False := by
  obtain ⟨h1, h2, h3, h4⟩ := equations hd ho
  have b2 := degree_bounds hd 2 (by decide)
  have b3 := degree_bounds hd 3 (by decide)
  have b4 := degree_bounds hd 4 (by decide)
  have b7 := degree_bounds hd 7 (by decide)
  have b8 := degree_bounds hd 8 (by decide)
  have b9 := degree_bounds hd 9 (by decide)
  change x 2 ≤ -13 ∨ 51 ≤ x 2 at b2
  change x 3 ≤ -13 ∨ 51 ≤ x 3 at b3
  change x 4 ≤ -38 ∨ 90 ≤ x 4 at b4
  change x 7 ≤ -63 ∨ 65 ≤ x 7 at b7
  change x 8 ≤ -12 ∨ 52 ≤ x 8 at b8
  change x 9 ≤ -12 ∨ 52 ≤ x 9 at b9
  have m2 := degree_mod hd 2
  have m3 := degree_mod hd 3
  have m4 := degree_mod hd 4
  have m8 := degree_mod hd 8
  have m9 := degree_mod hd 9
  change (x 2 - 51) % 64 = 0 at m2
  change (x 3 - 51) % 64 = 0 at m3
  change (x 4 - 90) % 64 = 0 at m4
  change (x 8 + 12) % 64 = 0 at m8
  change (x 9 + 12) % 64 = 0 at m9
  have h13 : x 2 = -13 ∨ x 3 = -13 := by
    by_contra hh
    have bb2 : x 2 ≤ -77 ∨ 51 ≤ x 2 := by omega
    have bb3 : x 3 ≤ -77 ∨ 51 ≤ x 3 := by omega
    have r2 : -(9:ℚ)/77 ≤ 9/(x 2:ℚ) :=
      reciprocal_lower (x 2) 77 51 9 (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast bb2)
    have r3 : -(9:ℚ)/77 ≤ 9/(x 3:ℚ) :=
      reciprocal_lower (x 3) 77 51 9 (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast bb3)
    have r7 : -(1:ℚ)/63 ≤ 1/(x 7:ℚ) :=
      reciprocal_lower (x 7) 63 65 1 (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast b7)
    have r8 : (16:ℚ)/(x 8) ≤ 16/52 :=
      reciprocal_upper (x 8) 12 52 16 (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast b8)
    have r9 : (16:ℚ)/(x 9) ≤ 16/52 :=
      reciprocal_upper (x 9) 12 52 16 (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast b9)
    linarith
  have hne : x 2 ≠ x 3 := by
    intro hh
    rcases h13 with h13 | h13 <;> omega
  have prime_bound : ∀ p : ℕ, p.Prime → p ∣ g → p ≤ 14 := by
    intro p hpp hpg
    rcases h13 with hh | hh
    · exact prime_bound_two hp hne hh p hpp hpg
    · exact prime_bound_three hp hne hh p hpp hpg
  have exclude141 (i : Fin 10) : x i ≠ -141 := by
    intro hh
    have hdvd := degree_dvd hp i
    rw [hh] at hdvd
    norm_num at hdvd
    have hh := prime_bound 47 (by decide) (dvd_trans (by norm_num : 47 ∣ 141) hdvd)
    omega
  have exclude116 (i : Fin 10) : x i ≠ 116 := by
    intro hh
    have hdvd := degree_dvd hp i
    rw [hh] at hdvd
    norm_num at hdvd
    have hh := prime_bound 29 (by decide) (dvd_trans (by norm_num : 29 ∣ 116) hdvd)
    omega
  have hpair : (x 2 = -13 ∧ x 3 = -77) ∨ (x 2 = -77 ∧ x 3 = -13) := by
    rcases h13 with hh | hh
    · have ss := third_degree_cases (x 2) (x 3) (x 4) b3 b4 m4 h3 hh h4
      rcases ss with ⟨_, hb⟩ | ⟨_, hb⟩
      · exact Or.inl ⟨hh, hb⟩
      · exact False.elim (exclude141 3 hb)
    · have ss := third_degree_cases (x 3) (x 2) (x 4) b2 b4 m4 (by omega) hh (by linarith)
      rcases ss with ⟨_, hb⟩ | ⟨_, hb⟩
      · exact Or.inr ⟨hb, hh⟩
      · exact False.elim (exclude141 2 hb)
  apply final_contradiction (x 7) (x 8) (x 9) b7 b8 b9 m8 m9 (exclude116 8) (exclude116 9)
  · rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rw [ha, hb] at h1 <;> norm_num at h1 ⊢ <;> linarith
  · rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega

end Stellmacher.Recognition.LyonsU3Four.EarlyL
