module
public import Stellmacher.Recognition.LyonsU3Four.TableIIsolatedMultiplicityAssembly
/-!
# Enumeration of isolated Table I multiplicities

Galois invariance reduces the 89 row counts to thirteen constant counts and
nineteen orbit counts. The adjacent-difference norm is eight, so a large
orbit of norm six leaves exactly one orbit of norm two. Two linear combinations
of the Gram equations, together with positivity of the principal count, force
the orbit pair to be (65, 17) or (73, 17). The remaining six Gram equations
then leave exactly the F and G constant counts.

All table reductions and integer arithmetic are checked by Lean's kernel;
no coverage or classification theorem is assumed.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 377–378, Case 3 and Table I.
-/

@[expose] public section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.TableIIsolatedRows
set_option maxHeartbeats 1000000 in
private theorem constant_counts (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : ℕ) (hp : 0 < a8)
    (h00 : (9) * (a0 : ℤ) + (9) * (a1 : ℤ) + (4) * (a2 : ℤ) + (4) * (a3 : ℤ) + (1) * (a4 : ℤ) + (1) * (a5
      : ℤ) + (1) * (a6 : ℤ) + (1) * (a8 : ℤ) + (1) * (a9 : ℤ) + (1) * (a10 : ℤ) + (4) * (a11 : ℤ) + (4) *
      (a12 : ℤ) = 8)
    (h01 : (-3) * (a0 : ℤ) + (-3) * (a1 : ℤ) + (-4) * (a2 : ℤ) + (-4) * (a3 : ℤ) + (1) * (a4 : ℤ) + (-3)
      * (a5 : ℤ) + (-3) * (a6 : ℤ) + (1) * (a8 : ℤ) + (1) * (a9 : ℤ) + (1) * (a10 : ℤ) + (4) * (a11 : ℤ)
      + (4) * (a12 : ℤ) = 0)
    (h02 : (-3) * (a1 : ℤ) + (-2) * (a2 : ℤ) + (-4) * (a3 : ℤ) + (-1) * (a4 : ℤ) + (-2) * (a5 : ℤ) + (-3)
      * (a6 : ℤ) + (1) * (a9 : ℤ) + (2) * (a10 : ℤ) + (2) * (a11 : ℤ) + (4) * (a12 : ℤ) = -2)
    (h11 : (1) * (a0 : ℤ) + (1) * (a1 : ℤ) + (4) * (a2 : ℤ) + (4) * (a3 : ℤ) + (1) * (a4 : ℤ) + (9) * (a5
      : ℤ) + (9) * (a6 : ℤ) + (1) * (a8 : ℤ) + (1) * (a9 : ℤ) + (1) * (a10 : ℤ) + (4) * (a11 : ℤ) + (4) *
      (a12 : ℤ) = 8)
    (h12 : (1) * (a1 : ℤ) + (2) * (a2 : ℤ) + (4) * (a3 : ℤ) + (-1) * (a4 : ℤ) + (6) * (a5 : ℤ) + (9) *
      (a6 : ℤ) + (1) * (a9 : ℤ) + (2) * (a10 : ℤ) + (2) * (a11 : ℤ) + (4) * (a12 : ℤ) = 6)
    (h22 : (1) * (a1 : ℤ) + (1) * (a2 : ℤ) + (4) * (a3 : ℤ) + (1) * (a4 : ℤ) + (4) * (a5 : ℤ) + (9) * (a6
      : ℤ) + (1) * (a7 : ℤ) + (1) * (a9 : ℤ) + (4) * (a10 : ℤ) + (1) * (a11 : ℤ) + (4) * (a12 : ℤ) = 8)
 :
    (a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 1 ∧ a4 = 0 ∧ a5 = 0 ∧ a6 = 0 ∧ a11 = 0 ∧ a12 = 0) ∧
    ((a7 = 2 ∧ a8 = 2 ∧ a9 = 2 ∧ a10 = 0) ∨ (a7 = 0 ∧ a8 = 3 ∧ a9 = 0 ∧ a10 = 1)) := by
  have hs : a1 + a3 + a6 = 1 := by
    zify
    linarith only [h00, h01, h02, h11, h12]
  have hb : 4*a4+a7+a8+a10+a11 = 4 := by
    zify
    linarith only [h01, h02, h11, h12, h22]
  have hz16 : a1 = 0 ∧ a6 = 0 := by
    clear h01 h02 h12 h22 hb
    omega
  have h3 : a3 = 1 := by
    clear h00 h01 h02 h11 h12 h22 hb
    omega
  have hz05 : a0 = 0 ∧ a5 = 0 := by
    clear h01 h02 h12 h22 hb
    omega
  have hz4 : a4 = 0 := by
    clear h00 h01 h02 h11 h12 h22
    omega
  have hz212 : a2 = 0 ∧ a11 = 0 ∧ a12 = 0 := by
    clear h01 h02 h11 h12 h22 hb
    omega
  have hc : a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 1 ∧ a4 = 0 ∧ a5 = 0 ∧ a6 = 0 ∧ a11 = 0 ∧ a12 = 0 := by
    clear h00 h01 h02 h11 h12 h22 hb
    omega
  have ht : a8 + a9 + a10 = 4 := by
    clear h01 h02 h11 h12 h22 hb
    omega
  have ht2 : a9 + 2*a10 = 2 := by
    clear h00 h01 h02 h11 h22 hb
    omega
  have hz : a7 + a9 + 4*a10 = 4 := by
    clear h00 h01 h02 h11 h12 hb
    omega
  clear h00 h01 h02 h11 h12 h22
  have hr : (a7 = 2 ∧ a8 = 2 ∧ a9 = 2 ∧ a10 = 0) ∨ (a7 = 0 ∧ a8 = 3 ∧ a9 = 0 ∧ a10 = 1) := by omega
  exact ⟨hc, hr⟩

set_option maxHeartbeats 1000000 in
private theorem numerical_counts (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a17 a21 a25 a29 a33 a37
  a41 a45 a49 a53 a57 a61 a65 a69 a73 a77 a81 a85 : ℕ) (hp : 0 < a8)
    (h00 : (9) * (a0 : ℤ) + (9) * (a1 : ℤ) + (4) * (a2 : ℤ) + (4) * (a3 : ℤ) + (1) * (a4 : ℤ) + (1) * (a5
      : ℤ) + (1) * (a6 : ℤ) + (1) * (a8 : ℤ) + (1) * (a9 : ℤ) + (1) * (a10 : ℤ) + (4) * (a11 : ℤ) + (4) *
      (a12 : ℤ) + (16) * (a13 : ℤ) + (4) * (a17 : ℤ) + (4) * (a21 : ℤ) + (4) * (a49 : ℤ) + (4) * (a53 :
      ℤ) + (4) * (a57 : ℤ) + (4) * (a61 : ℤ) + (4) * (a65 : ℤ) + (4) * (a69 : ℤ) + (4) * (a73 : ℤ) + (4)
      * (a77 : ℤ) + (16) * (a81 : ℤ) + (36) * (a85 : ℤ) = 16)
    (h01 : (-3) * (a0 : ℤ) + (-3) * (a1 : ℤ) + (-4) * (a2 : ℤ) + (-4) * (a3 : ℤ) + (1) * (a4 : ℤ) + (-3)
      * (a5 : ℤ) + (-3) * (a6 : ℤ) + (1) * (a8 : ℤ) + (1) * (a9 : ℤ) + (1) * (a10 : ℤ) + (4) * (a11 : ℤ)
      + (4) * (a12 : ℤ) + (-4) * (a17 : ℤ) + (-4) * (a21 : ℤ) + (-4) * (a49 : ℤ) + (4) * (a53 : ℤ) + (4)
      * (a57 : ℤ) + (4) * (a61 : ℤ) + (4) * (a65 : ℤ) + (4) * (a69 : ℤ) + (4) * (a73 : ℤ) + (12) * (a77 :
      ℤ) + (12) * (a85 : ℤ) = 0)
    (h02 : (-3) * (a1 : ℤ) + (-2) * (a2 : ℤ) + (-4) * (a3 : ℤ) + (-1) * (a4 : ℤ) + (-2) * (a5 : ℤ) + (-3)
      * (a6 : ℤ) + (1) * (a9 : ℤ) + (2) * (a10 : ℤ) + (2) * (a11 : ℤ) + (4) * (a12 : ℤ) + (-4) * (a13 :
      ℤ) + (-2) * (a17 : ℤ) + (-6) * (a21 : ℤ) + (2) * (a49 : ℤ) + (4) * (a65 : ℤ) + (4) * (a69 : ℤ) +
      (4) * (a73 : ℤ) + (10) * (a77 : ℤ) + (4) * (a81 : ℤ) + (6) * (a85 : ℤ) = 0)
    (h11 : (1) * (a0 : ℤ) + (1) * (a1 : ℤ) + (4) * (a2 : ℤ) + (4) * (a3 : ℤ) + (1) * (a4 : ℤ) + (9) * (a5
      : ℤ) + (9) * (a6 : ℤ) + (1) * (a8 : ℤ) + (1) * (a9 : ℤ) + (1) * (a10 : ℤ) + (4) * (a11 : ℤ) + (4) *
      (a12 : ℤ) + (4) * (a17 : ℤ) + (4) * (a21 : ℤ) + (16) * (a37 : ℤ) + (16) * (a41 : ℤ) + (16) * (a45 :
      ℤ) + (4) * (a49 : ℤ) + (4) * (a53 : ℤ) + (4) * (a57 : ℤ) + (4) * (a61 : ℤ) + (4) * (a65 : ℤ) + (4)
      * (a69 : ℤ) + (4) * (a73 : ℤ) + (36) * (a77 : ℤ) + (4) * (a85 : ℤ) = 16)
    (h12 : (1) * (a1 : ℤ) + (2) * (a2 : ℤ) + (4) * (a3 : ℤ) + (-1) * (a4 : ℤ) + (6) * (a5 : ℤ) + (9) *
      (a6 : ℤ) + (1) * (a9 : ℤ) + (2) * (a10 : ℤ) + (2) * (a11 : ℤ) + (4) * (a12 : ℤ) + (2) * (a17 : ℤ) +
      (6) * (a21 : ℤ) + (4) * (a37 : ℤ) + (12) * (a41 : ℤ) + (20) * (a45 : ℤ) + (-2) * (a49 : ℤ) + (4) *
      (a65 : ℤ) + (4) * (a69 : ℤ) + (4) * (a73 : ℤ) + (30) * (a77 : ℤ) + (2) * (a85 : ℤ) = 12)
    (h22 : (1) * (a1 : ℤ) + (1) * (a2 : ℤ) + (4) * (a3 : ℤ) + (1) * (a4 : ℤ) + (4) * (a5 : ℤ) + (9) * (a6
      : ℤ) + (1) * (a7 : ℤ) + (1) * (a9 : ℤ) + (4) * (a10 : ℤ) + (1) * (a11 : ℤ) + (4) * (a12 : ℤ) + (2)
      * (a13 : ℤ) + (2) * (a17 : ℤ) + (10) * (a21 : ℤ) + (6) * (a25 : ℤ) + (6) * (a29 : ℤ) + (6) * (a33 :
      ℤ) + (2) * (a37 : ℤ) + (10) * (a41 : ℤ) + (26) * (a45 : ℤ) + (2) * (a49 : ℤ) + (2) * (a53 : ℤ) +
      (2) * (a57 : ℤ) + (2) * (a61 : ℤ) + (6) * (a65 : ℤ) + (6) * (a69 : ℤ) + (6) * (a73 : ℤ) + (26) *
      (a77 : ℤ) + (2) * (a81 : ℤ) + (2) * (a85 : ℤ) = 16)
    (h23 : (1) * (a1 : ℤ) + (1) * (a2 : ℤ) + (4) * (a3 : ℤ) + (1) * (a4 : ℤ) + (4) * (a5 : ℤ) + (9) * (a6
      : ℤ) + (1) * (a7 : ℤ) + (1) * (a9 : ℤ) + (4) * (a10 : ℤ) + (1) * (a11 : ℤ) + (4) * (a12 : ℤ) + (1)
      * (a13 : ℤ) + (1) * (a17 : ℤ) + (9) * (a21 : ℤ) + (3) * (a25 : ℤ) + (4) * (a29 : ℤ) + (3) * (a33 :
      ℤ) + (1) * (a37 : ℤ) + (9) * (a41 : ℤ) + (25) * (a45 : ℤ) + (1) * (a49 : ℤ) + (-1) * (a53 : ℤ) +
      (-1) * (a61 : ℤ) + (3) * (a65 : ℤ) + (4) * (a69 : ℤ) + (3) * (a73 : ℤ) + (25) * (a77 : ℤ) + (1) *
      (a81 : ℤ) + (1) * (a85 : ℤ) = 12)
    (hl : 0 < a25 ∨ 0 < a33 ∨ 0 < a53 ∨ 0 < a61 ∨ 0 < a65 ∨ 0 < a73) :
    (a65 + a73 = 1 ∧ a17 = 1) ∧
    (a13 = 0 ∧ a21 = 0 ∧ a25 = 0 ∧ a29 = 0 ∧ a33 = 0 ∧ a37 = 0 ∧ a41 = 0 ∧ a45 = 0 ∧ a49 = 0 ∧ a53 = 0 ∧
      a57 = 0 ∧ a61 = 0 ∧ a69 = 0 ∧ a77 = 0 ∧ a81 = 0 ∧ a85 = 0) ∧
    (a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 1 ∧ a4 = 0 ∧ a5 = 0 ∧ a6 = 0 ∧ a11 = 0 ∧ a12 = 0) ∧
    ((a7 = 2 ∧ a8 = 2 ∧ a9 = 2 ∧ a10 = 0) ∨ (a7 = 0 ∧ a8 = 3 ∧ a9 = 0 ∧ a10 = 1)) := by
  have norm : 2 * a13 + 2 * a17 + 2 * a21 + 6 * a25 + 4 * a29 + 6 * a33 + 2 * a37 + 2 * a41 + 2 * a45 + 2
    * a49 + 6 * a53 + 4 * a57 + 6 * a61 + 6 * a65 + 4 * a69 + 6 * a73 + 2 * a77 + 2 * a81 + 2 * a85 = 8
    := by
    zify
    linarith only [h22, h23]
  have ho : a25 + a33 + a53 + a61 + a65 + a73 = 1 ∧
      a13 + a17 + a21 + a37 + a41 + a45 + a49 + a77 + a81 + a85 = 1 ∧
      a29 = 0 ∧ a57 = 0 ∧ a69 = 0 := by
    clear h00 h01 h02 h11 h12 h22 h23 hp
    omega
  have hz00 : a13 = 0 ∧ a81 = 0 ∧ a85 = 0 := by
    clear h01 h02 h11 h12 h22 h23 hl norm ho
    omega
  have hz11 : a37 = 0 ∧ a41 = 0 ∧ a45 = 0 ∧ a77 = 0 := by
    clear h00 h01 h02 h12 h22 h23 hl norm ho hz00
    omega
  have cert1 : 4*a4+a7+a8+a10+a11+3*a13+a17+3*a21+6*a25+6*a29+6*a33+
      7*a37+a41+3*a45+7*a49+6*a53+6*a57+6*a61+2*a65+2*a69+2*a73+a77+a81+3*a85 = 7 := by
    zify
    linarith only [h01, h02, h11, h12, h22]
  have cert2 : (a1:ℤ)+a3+a6+2*a13+2*a21-2*a37+2*a45-2*a49+2*a85 = 1 := by
    linarith only [h00, h01, h02, h11, h12]
  have hi : a65 + a73 = 1 := by
    clear h00 h01 h02 h11 h12 h22 h23
    omega
  have hj : a49 = 0 := by
    clear h00 h01 h02 h11 h12 h22 h23
    omega
  have hk : a21 = 0 := by
    clear h00 h01 h02 h11 h12 h22 h23
    omega
  have hj17 : a17 = 1 := by
    clear h00 h01 h02 h11 h12 h22 h23
    omega
  have he : a13 = 0 ∧ a21 = 0 ∧ a25 = 0 ∧ a29 = 0 ∧ a33 = 0 ∧ a37 = 0 ∧ a41 = 0 ∧ a45 = 0 ∧ a49 = 0 ∧ a53
    = 0 ∧ a57 = 0 ∧ a61 = 0 ∧ a69 = 0 ∧ a77 = 0 ∧ a81 = 0 ∧ a85 = 0 := by
    clear h00 h01 h02 h11 h12 h22 h23
    omega
  have hc := constant_counts a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hp
    (by
      rcases he with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      norm_num at h00
      have hiZ : (a65 : ℤ) + a73 = 1 := by exact_mod_cast hi
      have hjZ : (a17 : ℤ) = 1 := by exact_mod_cast hj17
      linarith only [h00, hiZ, hjZ])
    (by
      rcases he with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      norm_num at h01
      have hiZ : (a65 : ℤ) + a73 = 1 := by exact_mod_cast hi
      have hjZ : (a17 : ℤ) = 1 := by exact_mod_cast hj17
      linarith only [h01, hiZ, hjZ])
    (by
      rcases he with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      norm_num at h02
      have hiZ : (a65 : ℤ) + a73 = 1 := by exact_mod_cast hi
      have hjZ : (a17 : ℤ) = 1 := by exact_mod_cast hj17
      linarith only [h02, hiZ, hjZ])
    (by
      rcases he with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      norm_num at h11
      have hiZ : (a65 : ℤ) + a73 = 1 := by exact_mod_cast hi
      have hjZ : (a17 : ℤ) = 1 := by exact_mod_cast hj17
      linarith only [h11, hiZ, hjZ])
    (by
      rcases he with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      norm_num at h12
      have hiZ : (a65 : ℤ) + a73 = 1 := by exact_mod_cast hi
      have hjZ : (a17 : ℤ) = 1 := by exact_mod_cast hj17
      linarith only [h12, hiZ, hjZ])
    (by
      rcases he with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      norm_num at h22
      have hiZ : (a65 : ℤ) + a73 = 1 := by exact_mod_cast hi
      have hjZ : (a17 : ℤ) = 1 := by exact_mod_cast hj17
      linarith only [h22, hiZ, hjZ])
  exact ⟨⟨hi, hj17⟩, he, hc⟩

set_option maxRecDepth 10000 in
private theorem sum89 (f : Fin 89 → ℤ) :
    ∑ a, f a = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12
      + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 +
      (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f
      37 + (f 38 + (f 39 + (f 40 + (f 41 + (f 42 + (f 43 + (f 44 + (f 45 + (f 46 + (f 47 + (f 48 + (f 49
      + (f 50 + (f 51 + (f 52 + (f 53 + (f 54 + (f 55 + (f 56 + (f 57 + (f 58 + (f 59 + (f 60 + (f 61 +
      (f 62 + (f 63 + (f 64 + (f 65 + (f 66 + (f 67 + (f 68 + (f 69 + (f 70 + (f 71 + (f 72 + (f 73 + (f
      74 + (f 75 + (f 76 + (f 77 + (f 78 + (f 79 + (f 80 + (f 81 + (f 82 + (f 83 + (f 84 + (f 85 + (f 86
      + (f 87 + (f 88 +
      (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  rw [Fin.sum_univ_def]
  have he : List.finRange 89 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
    71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88] := by decide
  rw [he]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]


set_option maxRecDepth 10000 in
private theorem large_indices : ∀ a : Fin 89, difference (row a) 0 ^ 2 = 4 →
    a = 26 ∨ a = 33 ∨ a = 54 ∨ a = 61 ∨ a = 66 ∨ a = 73 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The Gram and Galois multiplicity conditions have exactly the four F/G
solutions, including the two column orientations. -/
theorem count_solutions (n : Fin 89 → ℕ) (h : MultiplicityConditions n) :
    ∃ c o : Bool, n = solution c o := by
  have hp : 0 < n 8 := h.principal_pos
  have r14 : n 14 = n 13 := by
    have hh := h.rotation_eq 13
    simpa [rotation] using hh
  have r15 : n 15 = n 13 := by
    have hh := h.rotation_eq 14
    simpa [rotation, r14] using hh
  have r16 : n 16 = n 13 := by
    have hh := h.rotation_eq 15
    simpa [rotation, r15] using hh
  have r18 : n 18 = n 17 := by
    have hh := h.rotation_eq 17
    simpa [rotation] using hh
  have r19 : n 19 = n 17 := by
    have hh := h.rotation_eq 18
    simpa [rotation, r18] using hh
  have r20 : n 20 = n 17 := by
    have hh := h.rotation_eq 19
    simpa [rotation, r19] using hh
  have r22 : n 22 = n 21 := by
    have hh := h.rotation_eq 21
    simpa [rotation] using hh
  have r23 : n 23 = n 21 := by
    have hh := h.rotation_eq 22
    simpa [rotation, r22] using hh
  have r24 : n 24 = n 21 := by
    have hh := h.rotation_eq 23
    simpa [rotation, r23] using hh
  have r26 : n 26 = n 25 := by
    have hh := h.rotation_eq 25
    simpa [rotation] using hh
  have r27 : n 27 = n 25 := by
    have hh := h.rotation_eq 26
    simpa [rotation, r26] using hh
  have r28 : n 28 = n 25 := by
    have hh := h.rotation_eq 27
    simpa [rotation, r27] using hh
  have r30 : n 30 = n 29 := by
    have hh := h.rotation_eq 29
    simpa [rotation] using hh
  have r31 : n 31 = n 29 := by
    have hh := h.rotation_eq 30
    simpa [rotation, r30] using hh
  have r32 : n 32 = n 29 := by
    have hh := h.rotation_eq 31
    simpa [rotation, r31] using hh
  have r34 : n 34 = n 33 := by
    have hh := h.rotation_eq 33
    simpa [rotation] using hh
  have r35 : n 35 = n 33 := by
    have hh := h.rotation_eq 34
    simpa [rotation, r34] using hh
  have r36 : n 36 = n 33 := by
    have hh := h.rotation_eq 35
    simpa [rotation, r35] using hh
  have r38 : n 38 = n 37 := by
    have hh := h.rotation_eq 37
    simpa [rotation] using hh
  have r39 : n 39 = n 37 := by
    have hh := h.rotation_eq 38
    simpa [rotation, r38] using hh
  have r40 : n 40 = n 37 := by
    have hh := h.rotation_eq 39
    simpa [rotation, r39] using hh
  have r42 : n 42 = n 41 := by
    have hh := h.rotation_eq 41
    simpa [rotation] using hh
  have r43 : n 43 = n 41 := by
    have hh := h.rotation_eq 42
    simpa [rotation, r42] using hh
  have r44 : n 44 = n 41 := by
    have hh := h.rotation_eq 43
    simpa [rotation, r43] using hh
  have r46 : n 46 = n 45 := by
    have hh := h.rotation_eq 45
    simpa [rotation] using hh
  have r47 : n 47 = n 45 := by
    have hh := h.rotation_eq 46
    simpa [rotation, r46] using hh
  have r48 : n 48 = n 45 := by
    have hh := h.rotation_eq 47
    simpa [rotation, r47] using hh
  have r50 : n 50 = n 49 := by
    have hh := h.rotation_eq 49
    simpa [rotation] using hh
  have r51 : n 51 = n 49 := by
    have hh := h.rotation_eq 50
    simpa [rotation, r50] using hh
  have r52 : n 52 = n 49 := by
    have hh := h.rotation_eq 51
    simpa [rotation, r51] using hh
  have r54 : n 54 = n 53 := by
    have hh := h.rotation_eq 53
    simpa [rotation] using hh
  have r55 : n 55 = n 53 := by
    have hh := h.rotation_eq 54
    simpa [rotation, r54] using hh
  have r56 : n 56 = n 53 := by
    have hh := h.rotation_eq 55
    simpa [rotation, r55] using hh
  have r58 : n 58 = n 57 := by
    have hh := h.rotation_eq 57
    simpa [rotation] using hh
  have r59 : n 59 = n 57 := by
    have hh := h.rotation_eq 58
    simpa [rotation, r58] using hh
  have r60 : n 60 = n 57 := by
    have hh := h.rotation_eq 59
    simpa [rotation, r59] using hh
  have r62 : n 62 = n 61 := by
    have hh := h.rotation_eq 61
    simpa [rotation] using hh
  have r63 : n 63 = n 61 := by
    have hh := h.rotation_eq 62
    simpa [rotation, r62] using hh
  have r64 : n 64 = n 61 := by
    have hh := h.rotation_eq 63
    simpa [rotation, r63] using hh
  have r66 : n 66 = n 65 := by
    have hh := h.rotation_eq 65
    simpa [rotation] using hh
  have r67 : n 67 = n 65 := by
    have hh := h.rotation_eq 66
    simpa [rotation, r66] using hh
  have r68 : n 68 = n 65 := by
    have hh := h.rotation_eq 67
    simpa [rotation, r67] using hh
  have r70 : n 70 = n 69 := by
    have hh := h.rotation_eq 69
    simpa [rotation] using hh
  have r71 : n 71 = n 69 := by
    have hh := h.rotation_eq 70
    simpa [rotation, r70] using hh
  have r72 : n 72 = n 69 := by
    have hh := h.rotation_eq 71
    simpa [rotation, r71] using hh
  have r74 : n 74 = n 73 := by
    have hh := h.rotation_eq 73
    simpa [rotation] using hh
  have r75 : n 75 = n 73 := by
    have hh := h.rotation_eq 74
    simpa [rotation, r74] using hh
  have r76 : n 76 = n 73 := by
    have hh := h.rotation_eq 75
    simpa [rotation, r75] using hh
  have r78 : n 78 = n 77 := by
    have hh := h.rotation_eq 77
    simpa [rotation] using hh
  have r79 : n 79 = n 77 := by
    have hh := h.rotation_eq 78
    simpa [rotation, r78] using hh
  have r80 : n 80 = n 77 := by
    have hh := h.rotation_eq 79
    simpa [rotation, r79] using hh
  have r82 : n 82 = n 81 := by
    have hh := h.rotation_eq 81
    simpa [rotation] using hh
  have r83 : n 83 = n 81 := by
    have hh := h.rotation_eq 82
    simpa [rotation, r82] using hh
  have r84 : n 84 = n 81 := by
    have hh := h.rotation_eq 83
    simpa [rotation, r83] using hh
  have r86 : n 86 = n 85 := by
    have hh := h.rotation_eq 85
    simpa [rotation] using hh
  have r87 : n 87 = n 85 := by
    have hh := h.rotation_eq 86
    simpa [rotation, r86] using hh
  have r88 : n 88 = n 85 := by
    have hh := h.rotation_eq 87
    simpa [rotation, r87] using hh
  have h00 := h.gram_eq 0 0
  have h01 := h.gram_eq 0 1
  have h02 := h.gram_eq 0 2
  have h11 := h.gram_eq 1 1
  have h12 := h.gram_eq 1 2
  have h22 := h.gram_eq 2 2
  have h23 := h.gram_eq 2 3
  rw [sum89] at h00
  simp [row, gram, TableIPairedRows.gram] at h00
  rw [sum89] at h01
  simp [row, gram, TableIPairedRows.gram] at h01
  rw [sum89] at h02
  simp [row, gram, TableIPairedRows.gram] at h02
  rw [sum89] at h11
  simp [row, gram, TableIPairedRows.gram] at h11
  rw [sum89] at h12
  simp [row, gram, TableIPairedRows.gram] at h12
  rw [sum89] at h22
  simp [row, gram, TableIPairedRows.gram] at h22
  rw [sum89] at h23
  simp [row, gram, TableIPairedRows.gram] at h23
  simp only [r14, r15, r16, r18, r19, r20, r22, r23, r24, r26, r27, r28, r30, r31, r32, r34, r35, r36,
    r38, r39, r40, r42, r43, r44, r46, r47, r48, r50, r51, r52, r54, r55, r56, r58, r59, r60, r62, r63,
    r64, r66, r67, r68, r70, r71, r72, r74, r75, r76, r78, r79, r80, r82, r83, r84, r86, r87, r88] at h00 h01 h02 h11 h12 h22 h23
  have hl : 0 < n 25 ∨ 0 < n 33 ∨ 0 < n 53 ∨ 0 < n 61 ∨ 0 < n 65 ∨ 0 < n 73 := by
    obtain ⟨a, ha, hd⟩ := h.large_pos
    rcases large_indices a hd with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hn := numerical_counts (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) (n 9) (n 10) (n 11)
    (n 12) (n 13) (n 17) (n 21) (n 25) (n 29) (n 33) (n 37) (n 41) (n 45) (n 49) (n 53) (n 57) (n 61) (n
    65) (n 69) (n 73) (n 77) (n 81) (n 85) hp
    (by linarith only [h00])
    (by linarith only [h01])
    (by linarith only [h02])
    (by linarith only [h11])
    (by linarith only [h12])
    (by linarith only [h22])
    (by linarith only [h23])
    hl
  rcases hn with ⟨hi, he, hc, hf⟩
  have ho : (n 65 = 1 ∧ n 73 = 0) ∨ (n 65 = 0 ∧ n 73 = 1) := by omega
  clear h hp hl h00 h01 h02 h11 h12 h22 h23
  rcases he with ⟨h13, h21, h25, h29, h33, h37, h41, h45, h49, h53, h57, h61,
    h69, h77, h81, h85⟩
  rcases hc with ⟨h0, h1, h2, h3, h4, h5, h6, h11, h12⟩
  have h17 := hi.2
  clear hi
  rcases hf with ⟨h7, h8, h9, h10⟩ | ⟨h7, h8, h9, h10⟩ <;>
    rcases ho with ⟨h65, h73⟩ | ⟨h65, h73⟩
  · simp only [h13, h17, h21, h25, h29, h33, h37, h41, h45, h49, h53, h57, h61, h65, h69, h73, h77, h81, h85] at r14 r15 r16 r18 r19 r20 r22 r23 r24 r26 r27 r28 r30 r31 r32 r34 r35 r36 r38 r39 r40 r42 r43 r44 r46 r47 r48 r50 r51 r52 r54 r55 r56 r58 r59 r60 r62 r63 r64 r66 r67 r68 r70 r71 r72 r74 r75 r76 r78 r79 r80 r82 r83 r84 r86 r87 r88
    refine ⟨false, false, ?_⟩
    funext a
    fin_cases a <;> assumption
  · simp only [h13, h17, h21, h25, h29, h33, h37, h41, h45, h49, h53, h57, h61, h65, h69, h73, h77, h81, h85] at r14 r15 r16 r18 r19 r20 r22 r23 r24 r26 r27 r28 r30 r31 r32 r34 r35 r36 r38 r39 r40 r42 r43 r44 r46 r47 r48 r50 r51 r52 r54 r55 r56 r58 r59 r60 r62 r63 r64 r66 r67 r68 r70 r71 r72 r74 r75 r76 r78 r79 r80 r82 r83 r84 r86 r87 r88
    refine ⟨false, true, ?_⟩
    funext a
    fin_cases a <;> assumption
  · simp only [h13, h17, h21, h25, h29, h33, h37, h41, h45, h49, h53, h57, h61, h65, h69, h73, h77, h81, h85] at r14 r15 r16 r18 r19 r20 r22 r23 r24 r26 r27 r28 r30 r31 r32 r34 r35 r36 r38 r39 r40 r42 r43 r44 r46 r47 r48 r50 r51 r52 r54 r55 r56 r58 r59 r60 r62 r63 r64 r66 r67 r68 r70 r71 r72 r74 r75 r76 r78 r79 r80 r82 r83 r84 r86 r87 r88
    refine ⟨true, false, ?_⟩
    funext a
    fin_cases a <;> assumption
  · simp only [h13, h17, h21, h25, h29, h33, h37, h41, h45, h49, h53, h57, h61, h65, h69, h73, h77, h81, h85] at r14 r15 r16 r18 r19 r20 r22 r23 r24 r26 r27 r28 r30 r31 r32 r34 r35 r36 r38 r39 r40 r42 r43 r44 r46 r47 r48 r50 r51 r52 r54 r55 r56 r58 r59 r60 r62 r63 r64 r66 r67 r68 r70 r71 r72 r74 r75 r76 r78 r79 r80 r82 r83 r84 r86 r87 r88
    refine ⟨true, true, ?_⟩
    funext a
    fin_cases a <;> assumption
end Stellmacher.Recognition.LyonsU3Four.TableIIsolatedRows
