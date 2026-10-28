module

public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.BinaryVectors

/-!
# Binary coefficient certificates for the change of tensor generators

A natural-number mask denotes the sum of its indicated tensor generators.
In characteristic two, XOR of masks denotes addition. Thus the finite inverse
coefficient calculation is verified by kernel reduction of explicit integers,
after each original orbit row has been proved to equal its mask evaluation.
Source: the concrete construction for GLS3 2.8.7 and 2.8.10(g).
-/

@[expose] public noncomputable section
namespace Atlas.G2.Restricted.Steinberg.OrbitClosure
open scoped BigOperators
variable (F : Type*) [Field F] [CharP F 2]
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

/-- Interpret a binary coefficient row in the tensor cube. -/
def maskVector (v : Fin 64 → Ambient F) (n : ℕ) : Ambient F :=
  ∑ i : Fin 64, if n.testBit i.val then v i else 0

/-- XOR is tensor addition because the coefficient field has characteristic two. -/
theorem maskVector_xor (v : Fin 64 → Ambient F) (m n : ℕ) :
    maskVector F v (m ^^^ n) = maskVector F v m + maskVector F v n := by
  simp only [maskVector, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.testBit_xor]
  have h : v i + v i = 0 := by
    rw [← two_smul F, cast2 F, zero_smul]
  cases hm : m.testBit i.val <;> cases hn : n.testBit i.val <;> simp [h]

omit [CharP F 2] in
theorem maskVector_single (v : Fin 64 → Ambient F) (j : Fin 64) :
    maskVector F v (2^j.val) = v j := by
  simp [maskVector, Nat.testBit_two_pow, ← Fin.ext_iff]

omit [CharP F 2] in
theorem mask_row_0 (v : Fin 64 → Ambient F) : maskVector F v 9223372036854775808 =
    v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_0 : binaryOrbitVector F (binaryIndex 0) =
    maskVector F (generators F) 9223372036854775808 := by
  rw [orbit_0]
  exact (mask_row_0 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_1 (v : Fin 64 → Ambient F) : maskVector F v 9223934986808197120 =
    v 49 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_1 : binaryOrbitVector F (binaryIndex 1) =
    maskVector F (generators F) 9223934986808197120 := by
  rw [orbit_1]
  exact (mask_row_1 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_2 (v : Fin 64 → Ambient F) : maskVector F v 13835058055282163712 =
    v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_2 : binaryOrbitVector F (binaryIndex 2) =
    maskVector F (generators F) 13835058055282163712 := by
  rw [orbit_2]
  exact (mask_row_2 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_3 (v : Fin 64 → Ambient F) : maskVector F v 13835902514572034048 =
    v 35 + v 48 + v 49 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_3 : binaryOrbitVector F (binaryIndex 3) =
    maskVector F (generators F) 13835902514572034048 := by
  rw [orbit_3]
  exact (mask_row_3 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_4 (v : Fin 64 → Ambient F) : maskVector F v 10682538326994452480 =
    v 27 + v 31 + v 33 + v 54 + v 58 + v 60 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_4 : binaryOrbitVector F (binaryIndex 4) =
    maskVector F (generators F) 10682538326994452480 := by
  rw [orbit_4]
  exact (mask_row_4 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_5 (v : Fin 64 → Ambient F) : maskVector F v 10683190337389725952 =
    v 8 + v 11 + v 27 + v 31 + v 33 + v 40 + v 44 + v 46 + v 49 + v 54 + v 58 + v 60 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_5 : binaryOrbitVector F (binaryIndex 5) =
    maskVector F (generators F) 10683190337389725952 := by
  rw [orbit_5]
  exact (mask_row_5 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_6 (v : Fin 64 → Ambient F) : maskVector F v 15294224379781578752 =
    v 27 + v 31 + v 33 + v 35 + v 54 + v 58 + v 60 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_6 : binaryOrbitVector F (binaryIndex 6) =
    maskVector F (generators F) 15294224379781578752 := by
  rw [orbit_6]
  exact (mask_row_6 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_7 (v : Fin 64 → Ambient F) : maskVector F v 15295157819922188544 =
    v 8 + v 11 + v 40 + v 44 + v 46 + v 48 + v 49 + v 54 + v 58 + v 60 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_7 : binaryOrbitVector F (binaryIndex 7) =
    maskVector F (generators F) 15295157819922188544 := by
  rw [orbit_7]
  exact (mask_row_7 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_8 (v : Fin 64 → Ambient F) : maskVector F v 11567495642901118986 =
    v 1 + v 3 + v 51 + v 55 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_8 : binaryOrbitVector F (binaryIndex 8) =
    maskVector F (generators F) 11567495642901118986 := by
  rw [orbit_8]
  exact (mask_row_8 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_9 (v : Fin 64 → Ambient F) : maskVector F v 11568201666809438218 =
    v 1 + v 3 + v 13 + v 17 + v 22 + v 37 + v 41 + v 47 + v 49 + v 51 + v 55 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_9 : binaryOrbitVector F (binaryIndex 9) =
    maskVector F (generators F) 11568201666809438218 := by
  rw [orbit_9]
  exact (mask_row_9 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_10 (v : Fin 64 → Ambient F) : maskVector F v 17342236265096937487 =
    v 0 + v 1 + v 2 + v 3 + v 50 + v 51 + v 53 + v 55 + v 60 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_10 : binaryOrbitVector F (binaryIndex 10) =
    maskVector F (generators F) 17342236265096937487 := by
  rw [orbit_10]
  exact (mask_row_10 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_11 (v : Fin 64 → Ambient F) : maskVector F v 17343294811693824703 =
    v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 7 + v 9 + v 11 + v 12 + v 13 + v 15 + v 17 + v 21 + v 22 + v 23 + v 24 + v 26 + v 28 + v 33 + v 34 + v 35 + v 36 + v 37 + v 39 + v 41 + v 46 + v 47 + v 48 + v 49 + v 50 + v 51 + v 53 + v 55 + v 60 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_11 : binaryOrbitVector F (binaryIndex 11) =
    maskVector F (generators F) 17343294811693824703 := by
  rw [orbit_11]
  exact (mask_row_11 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_12 (v : Fin 64 → Ambient F) : maskVector F v 13104349044656835451 =
    v 0 + v 1 + v 3 + v 4 + v 5 + v 6 + v 8 + v 9 + v 11 + v 23 + v 24 + v 25 + v 27 + v 28 + v 29 + v 31 + v 33 + v 34 + v 50 + v 51 + v 52 + v 54 + v 55 + v 56 + v 58 + v 60 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_12 : binaryOrbitVector F (binaryIndex 12) =
    maskVector F (generators F) 13104349044656835451 := by
  rw [orbit_12]
  exact (mask_row_12 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_13 (v : Fin 64 → Ambient F) : maskVector F v 13105148870653341707 =
    v 0 + v 1 + v 3 + v 12 + v 13 + v 14 + v 16 + v 17 + v 18 + v 21 + v 22 + v 23 + v 24 + v 25 + v 27 + v 28 + v 29 + v 31 + v 33 + v 34 + v 36 + v 37 + v 38 + v 40 + v 41 + v 42 + v 44 + v 46 + v 47 + v 49 + v 50 + v 51 + v 52 + v 54 + v 55 + v 56 + v 58 + v 60 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_13 : binaryOrbitVector F (binaryIndex 13) =
    maskVector F (generators F) 13105148870653341707 := by
  rw [orbit_13]
  exact (mask_row_13 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_14 (v : Fin 64 → Ambient F) : maskVector F v 16570994883653796846 =
    v 1 + v 2 + v 3 + v 5 + v 6 + v 7 + v 8 + v 9 + v 24 + v 25 + v 26 + v 27 + v 28 + v 29 + v 31 + v 34 + v 35 + v 51 + v 52 + v 53 + v 54 + v 55 + v 56 + v 58 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_14 : binaryOrbitVector F (binaryIndex 14) =
    maskVector F (generators F) 16570994883653796846 := by
  rw [orbit_14]
  exact (mask_row_14 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_15 (v : Fin 64 → Ambient F) : maskVector F v 16572006242173051886 =
    v 1 + v 2 + v 3 + v 5 + v 6 + v 7 + v 8 + v 9 + v 13 + v 14 + v 15 + v 16 + v 17 + v 18 + v 22 + v 37 + v 38 + v 39 + v 40 + v 41 + v 42 + v 44 + v 47 + v 48 + v 49 + v 51 + v 52 + v 53 + v 54 + v 55 + v 56 + v 58 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_15 : binaryOrbitVector F (binaryIndex 15) =
    maskVector F (generators F) 16572006242173051886 := by
  rw [orbit_15]
  exact (mask_row_15 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_16 (v : Fin 64 → Ambient F) : maskVector F v 9367487224931155968 =
    v 19 + v 57 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_16 : binaryOrbitVector F (binaryIndex 16) =
    maskVector F (generators F) 9367487224931155968 := by
  rw [orbit_16]
  exact (mask_row_16 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_17 (v : Fin 64 → Ambient F) : maskVector F v 9368058970977599488 =
    v 19 + v 43 + v 49 + v 57 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_17 : binaryOrbitVector F (binaryIndex 17) =
    maskVector F (generators F) 9368058970977599488 := by
  rw [orbit_17]
  exact (mask_row_17 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_18 (v : Fin 64 → Ambient F) : maskVector F v 14557885795476709376 =
    v 13 + v 19 + v 20 + v 51 + v 57 + v 59 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_18 : binaryOrbitVector F (binaryIndex 18) =
    maskVector F (generators F) 14557885795476709376 := by
  rw [orbit_18]
  exact (mask_row_18 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_19 (v : Fin 64 → Ambient F) : maskVector F v 14558774378056130562 =
    v 1 + v 13 + v 19 + v 20 + v 24 + v 30 + v 32 + v 35 + v 37 + v 43 + v 45 + v 48 + v 49 + v 51 + v 57 + v 59 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_19 : binaryOrbitVector F (binaryIndex 19) =
    maskVector F (generators F) 14558774378056130562 := by
  rw [orbit_19]
  exact (mask_row_19 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_20 (v : Fin 64 → Ambient F) : maskVector F v 10868311813010444297 =
    v 0 + v 3 + v 12 + v 14 + v 16 + v 17 + v 19 + v 21 + v 23 + v 25 + v 27 + v 28 + v 30 + v 31 + v 33 + v 50 + v 52 + v 54 + v 55 + v 57 + v 58 + v 60 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_20 : binaryOrbitVector F (binaryIndex 20) =
    maskVector F (generators F) 10868311813010444297 := by
  rw [orbit_20]
  exact (mask_row_20 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_21 (v : Fin 64 → Ambient F) : maskVector F v 10868975162119379801 =
    v 0 + v 3 + v 4 + v 6 + v 8 + v 9 + v 11 + v 12 + v 14 + v 16 + v 17 + v 19 + v 21 + v 23 + v 25 + v 27 + v 28 + v 30 + v 31 + v 33 + v 36 + v 38 + v 40 + v 41 + v 43 + v 44 + v 46 + v 49 + v 50 + v 52 + v 54 + v 55 + v 57 + v 58 + v 60 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_21 : binaryOrbitVector F (binaryIndex 21) =
    maskVector F (generators F) 10868975162119379801 := by
  rw [orbit_21]
  exact (mask_row_21 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_22 (v : Fin 64 → Ambient F) : maskVector F v 16058710422227480587 =
    v 0 + v 1 + v 3 + v 12 + v 13 + v 14 + v 16 + v 17 + v 19 + v 20 + v 21 + v 23 + v 24 + v 25 + v 27 + v 28 + v 30 + v 31 + v 32 + v 33 + v 35 + v 50 + v 51 + v 52 + v 54 + v 55 + v 57 + v 58 + v 59 + v 60 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_22 : binaryOrbitVector F (binaryIndex 22) =
    maskVector F (generators F) 16058710422227480587 := by
  rw [orbit_22]
  exact (mask_row_22 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_23 (v : Fin 64 → Ambient F) : maskVector F v 16059690517196930928 =
    v 4 + v 5 + v 6 + v 8 + v 9 + v 10 + v 11 + v 12 + v 13 + v 14 + v 16 + v 17 + v 19 + v 20 + v 21 + v 36 + v 37 + v 38 + v 40 + v 41 + v 43 + v 44 + v 45 + v 46 + v 48 + v 49 + v 50 + v 51 + v 52 + v 54 + v 55 + v 57 + v 58 + v 59 + v 60 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_23 : binaryOrbitVector F (binaryIndex 23) =
    maskVector F (generators F) 16059690517196930928 := by
  rw [orbit_23]
  exact (mask_row_23 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_24 (v : Fin 64 → Ambient F) : maskVector F v 11711610830981832714 =
    v 1 + v 3 + v 13 + v 17 + v 19 + v 22 + v 51 + v 55 + v 57 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_24 : binaryOrbitVector F (binaryIndex 24) =
    maskVector F (generators F) 11711610830981832714 := by
  rw [orbit_24]
  exact (mask_row_24 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_25 (v : Fin 64 → Ambient F) : maskVector F v 11712325650973982730 =
    v 1 + v 3 + v 37 + v 41 + v 43 + v 47 + v 49 + v 51 + v 55 + v 57 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_25 : binaryOrbitVector F (binaryIndex 25) =
    maskVector F (generators F) 11712325650973982730 := by
  rw [orbit_25]
  exact (mask_row_25 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_26 (v : Fin 64 → Ambient F) : maskVector F v 18065064005297950733 =
    v 0 + v 2 + v 3 + v 12 + v 14 + v 15 + v 17 + v 19 + v 20 + v 21 + v 22 + v 50 + v 52 + v 53 + v 55 + v 57 + v 59 + v 60 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_26 : binaryOrbitVector F (binaryIndex 26) =
    maskVector F (generators F) 18065064005297950733 := by
  rw [orbit_26]
  exact (mask_row_26 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_27 (v : Fin 64 → Ambient F) : maskVector F v 18066166675169873616 =
    v 4 + v 6 + v 7 + v 9 + v 10 + v 11 + v 23 + v 25 + v 26 + v 28 + v 30 + v 32 + v 33 + v 34 + v 35 + v 36 + v 38 + v 39 + v 41 + v 43 + v 45 + v 46 + v 47 + v 48 + v 49 + v 50 + v 52 + v 53 + v 55 + v 57 + v 59 + v 60 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_27 : binaryOrbitVector F (binaryIndex 27) =
    maskVector F (generators F) 18066166675169873616 := by
  rw [orbit_27]
  exact (mask_row_27 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_28 (v : Fin 64 → Ambient F) : maskVector F v 13204554137119557888 =
    v 8 + v 11 + v 16 + v 18 + v 19 + v 21 + v 22 + v 27 + v 29 + v 30 + v 31 + v 33 + v 34 + v 54 + v 56 + v 57 + v 58 + v 60 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_28 : binaryOrbitVector F (binaryIndex 28) =
    maskVector F (generators F) 13204554137119557888 := by
  rw [orbit_28]
  exact (mask_row_28 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_29 (v : Fin 64 → Ambient F) : maskVector F v 13205360079135571968 =
    v 27 + v 29 + v 30 + v 31 + v 33 + v 34 + v 40 + v 42 + v 43 + v 44 + v 46 + v 47 + v 49 + v 54 + v 56 + v 57 + v 58 + v 60 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_29 : binaryOrbitVector F (binaryIndex 29) =
    maskVector F (generators F) 13205360079135571968 := by
  rw [orbit_29]
  exact (mask_row_29 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_30 (v : Fin 64 → Ambient F) : maskVector F v 17256667932035773936 =
    v 4 + v 5 + v 6 + v 7 + v 8 + v 10 + v 12 + v 13 + v 14 + v 15 + v 16 + v 18 + v 19 + v 20 + v 22 + v 23 + v 24 + v 25 + v 26 + v 27 + v 29 + v 30 + v 31 + v 32 + v 34 + v 35 + v 50 + v 51 + v 52 + v 53 + v 54 + v 56 + v 57 + v 58 + v 59 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_30 : binaryOrbitVector F (binaryIndex 30) =
    maskVector F (generators F) 17256667932035773936 := by
  rw [orbit_30]
  exact (mask_row_30 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_31 (v : Fin 64 → Ambient F) : maskVector F v 17257721135596832247 =
    v 0 + v 1 + v 2 + v 4 + v 5 + v 6 + v 7 + v 8 + v 10 + v 36 + v 37 + v 38 + v 39 + v 40 + v 42 + v 43 + v 44 + v 45 + v 47 + v 48 + v 49 + v 50 + v 51 + v 52 + v 53 + v 54 + v 56 + v 57 + v 58 + v 59 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_31 : binaryOrbitVector F (binaryIndex 31) =
    maskVector F (generators F) 17257721135596832247 := by
  rw [orbit_31]
  exact (mask_row_31 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_32 (v : Fin 64 → Ambient F) : maskVector F v 9873016283102970896 =
    v 4 + v 10 + v 50 + v 56 + v 59 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_32 : binaryOrbitVector F (binaryIndex 32) =
    maskVector F (generators F) 9873016283102970896 := by
  rw [orbit_32]
  exact (mask_row_32 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_33 (v : Fin 64 → Ambient F) : maskVector F v 9873618884194468881 =
    v 0 + v 4 + v 10 + v 36 + v 42 + v 45 + v 49 + v 50 + v 56 + v 59 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_33 : binaryOrbitVector F (binaryIndex 33) =
    maskVector F (generators F) 9873618884194468881 := by
  rw [orbit_33]
  exact (mask_row_33 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_34 (v : Fin 64 → Ambient F) : maskVector F v 14502716700039841040 =
    v 4 + v 8 + v 10 + v 50 + v 54 + v 56 + v 59 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_34 : binaryOrbitVector F (binaryIndex 34) =
    maskVector F (generators F) 14502716700039841040 := by
  rw [orbit_34]
  exact (mask_row_34 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_35 (v : Fin 64 → Ambient F) : maskVector F v 14503601914953860369 =
    v 0 + v 4 + v 8 + v 10 + v 23 + v 27 + v 29 + v 32 + v 35 + v 36 + v 40 + v 42 + v 45 + v 48 + v 49 + v 50 + v 54 + v 56 + v 59 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_35 : binaryOrbitVector F (binaryIndex 35) =
    maskVector F (generators F) 14503601914953860369 := by
  rw [orbit_35]
  exact (mask_row_35 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_36 (v : Fin 64 → Ambient F) : maskVector F v 11341189777404726672 =
    v 4 + v 7 + v 8 + v 10 + v 11 + v 23 + v 26 + v 27 + v 29 + v 31 + v 32 + v 33 + v 50 + v 53 + v 54 + v 56 + v 58 + v 59 + v 60 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_36 : binaryOrbitVector F (binaryIndex 36) =
    maskVector F (generators F) 11341189777404726672 := by
  rw [orbit_36]
  exact (mask_row_36 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_37 (v : Fin 64 → Ambient F) : maskVector F v 11341881988693884933 =
    v 0 + v 2 + v 23 + v 26 + v 27 + v 29 + v 31 + v 32 + v 33 + v 36 + v 39 + v 40 + v 42 + v 44 + v 45 + v 46 + v 49 + v 50 + v 53 + v 54 + v 56 + v 58 + v 59 + v 60 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_37 : binaryOrbitVector F (binaryIndex 37) =
    maskVector F (generators F) 11341881988693884933 := by
  rw [orbit_37]
  exact (mask_row_37 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_38 (v : Fin 64 → Ambient F) : maskVector F v 15934861431548152976 =
    v 4 + v 7 + v 10 + v 11 + v 23 + v 26 + v 29 + v 31 + v 32 + v 33 + v 35 + v 50 + v 53 + v 56 + v 58 + v 59 + v 60 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_38 : binaryOrbitVector F (binaryIndex 38) =
    maskVector F (generators F) 15934861431548152976 := by
  rw [orbit_38]
  exact (mask_row_38 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_39 (v : Fin 64 → Ambient F) : maskVector F v 15935833968297902085 =
    v 0 + v 2 + v 36 + v 39 + v 42 + v 44 + v 45 + v 46 + v 48 + v 49 + v 50 + v 53 + v 56 + v 58 + v 59 + v 60 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_39 : binaryOrbitVector F (binaryIndex 39) =
    maskVector F (generators F) 15935833968297902085 := by
  rw [orbit_39]
  exact (mask_row_39 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_40 (v : Fin 64 → Ambient F) : maskVector F v 12221643488776685179 =
    v 0 + v 1 + v 3 + v 4 + v 5 + v 6 + v 9 + v 10 + v 50 + v 51 + v 52 + v 55 + v 56 + v 59 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_40 : binaryOrbitVector F (binaryIndex 40) =
    maskVector F (generators F) 12221643488776685179 := by
  rw [orbit_40]
  exact (mask_row_40 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_41 (v : Fin 64 → Ambient F) : maskVector F v 12222389438702319216 =
    v 4 + v 5 + v 6 + v 9 + v 10 + v 12 + v 13 + v 14 + v 17 + v 18 + v 20 + v 22 + v 36 + v 37 + v 38 + v 41 + v 42 + v 45 + v 47 + v 49 + v 50 + v 51 + v 52 + v 55 + v 56 + v 59 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_41 : binaryOrbitVector F (binaryIndex 41) =
    maskVector F (generators F) 12222389438702319216 := by
  rw [orbit_41]
  exact (mask_row_41 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_42 (v : Fin 64 → Ambient F) : maskVector F v 18012146709668302830 =
    v 1 + v 2 + v 3 + v 5 + v 6 + v 7 + v 8 + v 9 + v 10 + v 11 + v 51 + v 52 + v 53 + v 54 + v 55 + v 56 + v 59 + v 60 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_42 : binaryOrbitVector F (binaryIndex 42) =
    maskVector F (generators F) 18012146709668302830 := by
  rw [orbit_42]
  exact (mask_row_42 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_43 (v : Fin 64 → Ambient F) : maskVector F v 18013246149346451456 =
    v 13 + v 14 + v 15 + v 16 + v 17 + v 18 + v 20 + v 21 + v 22 + v 24 + v 25 + v 26 + v 27 + v 28 + v 29 + v 32 + v 33 + v 34 + v 35 + v 37 + v 38 + v 39 + v 40 + v 41 + v 42 + v 45 + v 46 + v 47 + v 48 + v 49 + v 51 + v 52 + v 53 + v 54 + v 55 + v 56 + v 59 + v 60 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_43 : binaryOrbitVector F (binaryIndex 43) =
    maskVector F (generators F) 18013246149346451456 := by
  rw [orbit_43]
  exact (mask_row_43 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_44 (v : Fin 64 → Ambient F) : maskVector F v 13613255806341349391 =
    v 0 + v 1 + v 2 + v 3 + v 23 + v 24 + v 26 + v 27 + v 28 + v 31 + v 32 + v 33 + v 34 + v 50 + v 51 + v 53 + v 54 + v 55 + v 58 + v 59 + v 60 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_44 : binaryOrbitVector F (binaryIndex 44) =
    maskVector F (generators F) 13613255806341349391 := by
  rw [orbit_44]
  exact (mask_row_44 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_45 (v : Fin 64 → Ambient F) : maskVector F v 13614086693542150064 =
    v 4 + v 5 + v 7 + v 8 + v 9 + v 10 + v 11 + v 12 + v 13 + v 15 + v 16 + v 17 + v 20 + v 21 + v 22 + v 23 + v 24 + v 26 + v 27 + v 28 + v 31 + v 32 + v 33 + v 34 + v 36 + v 37 + v 39 + v 40 + v 41 + v 44 + v 45 + v 46 + v 47 + v 49 + v 50 + v 51 + v 53 + v 54 + v 55 + v 58 + v 59 + v 60 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_45 : binaryOrbitVector F (binaryIndex 45) =
    maskVector F (generators F) 13614086693542150064 := by
  rw [orbit_45]
  exact (mask_row_45 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_46 (v : Fin 64 → Ambient F) : maskVector F v 17043872848050913290 =
    v 1 + v 3 + v 24 + v 28 + v 31 + v 32 + v 34 + v 35 + v 51 + v 55 + v 58 + v 59 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_46 : binaryOrbitVector F (binaryIndex 46) =
    maskVector F (generators F) 17043872848050913290 := by
  rw [orbit_46]
  exact (mask_row_46 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_47 (v : Fin 64 → Ambient F) : maskVector F v 17044913065227853824 =
    v 13 + v 17 + v 20 + v 22 + v 37 + v 41 + v 44 + v 45 + v 47 + v 48 + v 49 + v 51 + v 55 + v 58 + v 59 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_47 : binaryOrbitVector F (binaryIndex 47) =
    maskVector F (generators F) 17044913065227853824 := by
  rw [orbit_47]
  exact (mask_row_47 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_48 (v : Fin 64 → Ambient F) : maskVector F v 10019383270994359344 =
    v 4 + v 5 + v 10 + v 12 + v 13 + v 18 + v 19 + v 20 + v 50 + v 51 + v 56 + v 57 + v 59 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_48 : binaryOrbitVector F (binaryIndex 48) =
    maskVector F (generators F) 10019383270994359344 := by
  rw [orbit_48]
  exact (mask_row_48 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_49 (v : Fin 64 → Ambient F) : maskVector F v 10019994805617833011 =
    v 0 + v 1 + v 4 + v 5 + v 10 + v 12 + v 13 + v 18 + v 19 + v 20 + v 36 + v 37 + v 42 + v 43 + v 45 + v 49 + v 50 + v 51 + v 56 + v 57 + v 59 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_49 : binaryOrbitVector F (binaryIndex 49) =
    maskVector F (generators F) 10019994805617833011 := by
  rw [orbit_49]
  exact (mask_row_49 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_50 (v : Fin 64 → Ambient F) : maskVector F v 14069245235906281728 =
    v 8 + v 16 + v 18 + v 19 + v 54 + v 56 + v 57 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_50 : binaryOrbitVector F (binaryIndex 50) =
    maskVector F (generators F) 14069245235906281728 := by
  rw [orbit_50]
  exact (mask_row_50 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_51 (v : Fin 64 → Ambient F) : maskVector F v 14070103990592143616 =
    v 8 + v 16 + v 18 + v 19 + v 27 + v 29 + v 30 + v 35 + v 40 + v 42 + v 43 + v 48 + v 49 + v 54 + v 56 + v 57 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_51 : binaryOrbitVector F (binaryIndex 51) =
    maskVector F (generators F) 14070103990592143616 := by
  rw [orbit_51]
  exact (mask_row_51 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_52 (v : Fin 64 → Ambient F) : maskVector F v 11526963263422066670 =
    v 1 + v 2 + v 3 + v 5 + v 6 + v 7 + v 8 + v 9 + v 10 + v 11 + v 13 + v 14 + v 15 + v 16 + v 17 + v 18 + v 19 + v 20 + v 21 + v 24 + v 25 + v 26 + v 27 + v 28 + v 29 + v 30 + v 31 + v 32 + v 33 + v 51 + v 52 + v 53 + v 54 + v 55 + v 56 + v 57 + v 58 + v 59 + v 60 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_52 : binaryOrbitVector F (binaryIndex 52) =
    maskVector F (generators F) 11526963263422066670 := by
  rw [orbit_52]
  exact (mask_row_52 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_53 (v : Fin 64 → Ambient F) : maskVector F v 11527666813424885760 =
    v 13 + v 14 + v 15 + v 16 + v 17 + v 18 + v 19 + v 20 + v 21 + v 24 + v 25 + v 26 + v 27 + v 28 + v 29 + v 30 + v 31 + v 32 + v 33 + v 37 + v 38 + v 39 + v 40 + v 41 + v 42 + v 43 + v 44 + v 45 + v 46 + v 49 + v 51 + v 52 + v 53 + v 54 + v 55 + v 56 + v 57 + v 58 + v 59 + v 60 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_53 : binaryOrbitVector F (binaryIndex 53) =
    maskVector F (generators F) 11527666813424885760 := by
  rw [orbit_53]
  exact (mask_row_53 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_54 (v : Fin 64 → Ambient F) : maskVector F v 15543048261050751709 =
    v 0 + v 2 + v 3 + v 4 + v 6 + v 7 + v 9 + v 11 + v 12 + v 14 + v 15 + v 17 + v 18 + v 19 + v 21 + v 23 + v 25 + v 26 + v 28 + v 29 + v 30 + v 31 + v 33 + v 35 + v 50 + v 52 + v 53 + v 55 + v 56 + v 57 + v 58 + v 60 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_54 : binaryOrbitVector F (binaryIndex 54) =
    maskVector F (generators F) 15543048261050751709 := by
  rw [orbit_54]
  exact (mask_row_54 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_55 (v : Fin 64 → Ambient F) : maskVector F v 15543996886341832717 =
    v 0 + v 2 + v 3 + v 12 + v 14 + v 15 + v 17 + v 18 + v 19 + v 21 + v 36 + v 38 + v 39 + v 41 + v 42 + v 43 + v 44 + v 46 + v 48 + v 49 + v 50 + v 52 + v 53 + v 55 + v 56 + v 57 + v 58 + v 60 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_55 : binaryOrbitVector F (binaryIndex 55) =
    maskVector F (generators F) 15543996886341832717 := by
  rw [orbit_55]
  exact (mask_row_55 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_56 (v : Fin 64 → Ambient F) : maskVector F v 12363506877045036633 =
    v 0 + v 3 + v 4 + v 6 + v 9 + v 10 + v 12 + v 14 + v 17 + v 18 + v 19 + v 20 + v 22 + v 50 + v 52 + v 55 + v 56 + v 57 + v 59 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_56 : binaryOrbitVector F (binaryIndex 56) =
    maskVector F (generators F) 12363506877045036633 := by
  rw [orbit_56]
  exact (mask_row_56 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_57 (v : Fin 64 → Ambient F) : maskVector F v 12364261485612893776 =
    v 4 + v 6 + v 9 + v 10 + v 36 + v 38 + v 41 + v 42 + v 43 + v 45 + v 47 + v 49 + v 50 + v 52 + v 55 + v 56 + v 57 + v 59 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_57 : binaryOrbitVector F (binaryIndex 57) =
    maskVector F (generators F) 12364261485612893776 := by
  rw [orbit_57]
  exact (mask_row_57 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_58 (v : Fin 64 → Ambient F) : maskVector F v 17576423445727525823 =
    v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 7 + v 8 + v 9 + v 11 + v 12 + v 13 + v 15 + v 16 + v 17 + v 18 + v 19 + v 21 + v 22 + v 50 + v 51 + v 53 + v 54 + v 55 + v 56 + v 57 + v 60 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_58 : binaryOrbitVector F (binaryIndex 58) =
    maskVector F (generators F) 17576423445727525823 := by
  rw [orbit_58]
  exact (mask_row_58 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_59 (v : Fin 64 → Ambient F) : maskVector F v 17577496287706611727 =
    v 0 + v 1 + v 2 + v 3 + v 23 + v 24 + v 26 + v 27 + v 28 + v 29 + v 30 + v 33 + v 34 + v 35 + v 36 + v 37 + v 39 + v 40 + v 41 + v 42 + v 43 + v 46 + v 47 + v 48 + v 49 + v 50 + v 51 + v 53 + v 54 + v 55 + v 56 + v 57 + v 60 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_59 : binaryOrbitVector F (binaryIndex 59) =
    maskVector F (generators F) 17577496287706611727 := by
  rw [orbit_59]
  exact (mask_row_59 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_60 (v : Fin 64 → Ambient F) : maskVector F v 13724719897957228544 =
    v 13 + v 14 + v 15 + v 16 + v 19 + v 20 + v 21 + v 22 + v 24 + v 25 + v 26 + v 27 + v 30 + v 31 + v 32 + v 33 + v 34 + v 51 + v 52 + v 53 + v 54 + v 57 + v 58 + v 59 + v 60 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_60 : binaryOrbitVector F (binaryIndex 60) =
    maskVector F (generators F) 13724719897957228544 := by
  rw [orbit_60]
  exact (mask_row_60 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_61 (v : Fin 64 → Ambient F) : maskVector F v 13725557588370656742 =
    v 1 + v 2 + v 5 + v 6 + v 7 + v 8 + v 10 + v 11 + v 24 + v 25 + v 26 + v 27 + v 30 + v 31 + v 32 + v 33 + v 34 + v 37 + v 38 + v 39 + v 40 + v 43 + v 44 + v 45 + v 46 + v 47 + v 49 + v 51 + v 52 + v 53 + v 54 + v 57 + v 58 + v 59 + v 60 + v 61 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_61 : binaryOrbitVector F (binaryIndex 61) =
    maskVector F (generators F) 13725557588370656742 := by
  rw [orbit_61]
  exact (mask_row_61 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_62 (v : Fin 64 → Ambient F) : maskVector F v 16573246683488976896 =
    v 19 + v 22 + v 30 + v 31 + v 34 + v 35 + v 57 + v 58 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_62 : binaryOrbitVector F (binaryIndex 62) =
    maskVector F (generators F) 16573246683488976896 := by
  rw [orbit_62]
  exact (mask_row_62 F (generators F)).symm

omit [CharP F 2] in
theorem mask_row_63 (v : Fin 64 → Ambient F) : maskVector F v 16574258179420979200 =
    v 43 + v 44 + v 47 + v 48 + v 49 + v 57 + v 58 + v 61 + v 62 + v 63 := by
  norm_num [maskVector, Fin.sum_univ_succ, Nat.testBit, Nat.shiftRight_eq_div_pow, add_assoc] <;> rfl

theorem orbit_mask_63 : binaryOrbitVector F (binaryIndex 63) =
    maskVector F (generators F) 16574258179420979200 := by
  rw [orbit_63]
  exact (mask_row_63 F (generators F)).symm

end Atlas.G2.Restricted.Steinberg.OrbitClosure
