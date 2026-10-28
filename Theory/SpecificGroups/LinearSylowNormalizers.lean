module

public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular

/-!
# Solvable Sylow normalizers on the concrete linear component carriers

The upper triangular Borel calculation specializes to PSL₂(2ᵉ), SL₃(2ᵉ),
and PSL₄(2), PSL₅(2). The finite-field cardinality hypothesis supplies
characteristic two; the projective groups are the actual central quotients.
No quasisimplicity or solvability premise is needed.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, combined manuscript of
1 March 2004, B.4.2(1),(2),(9), printed p.86; B.5.5(1)(iv)–B.5.6,
pp.104–105; and the Borel in the proof of 15.3.49(k), p.1144.
-/

public section

namespace Theory.SpecificGroups.LinearSylowNormalizers

open Matrix Subgroup

variable {F : Type*} [Field F] [Finite F]

private theorem ringChar_eq_two_of_card {e : ℕ} (he : 0 < e)
    (hF : Nat.card F = 2 ^ e) : ringChar F = 2 := by
  let _ := Fintype.ofFinite F
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hF]
  simp [Nat.pow_mod, Nat.ne_of_gt he]

/-- Every Sylow two-normalizer on the actual PSL₂(2ᵉ) carrier is solvable. -/
theorem isSolvable_psl_two_normalizer {e : ℕ} (he : 2 ≤ e)
    (hF : Nat.card F = 2 ^ e)
    (S : Sylow 2 (ProjectiveSpecialLinearGroup (Fin 2) F)) :
    Group.IsSolvable
      (normalizer (S : Set (ProjectiveSpecialLinearGroup (Fin 2) F))) := by
  let _ : CharP F 2 := ringChar.of_eq (ringChar_eq_two_of_card (by omega) hF)
  exact isSolvable_projective_sylow_normalizer 2 F (by decide) S

/-- Every Sylow two-normalizer on the actual SL₃(2ᵉ) carrier is solvable. -/
theorem isSolvable_sl_three_normalizer {e : ℕ} (he : 1 ≤ e)
    (hF : Nat.card F = 2 ^ e)
    (S : Sylow 2 (SpecialLinearGroup (Fin 3) F)) :
    Group.IsSolvable (normalizer (S : Set (SpecialLinearGroup (Fin 3) F))) := by
  let _ : CharP F 2 := ringChar.of_eq (ringChar_eq_two_of_card (by omega) hF)
  exact isSolvable_sylow_normalizer 3 F (by decide) S

/-- Every Sylow two-normalizer on the actual PSL₄(2) or PSL₅(2) carrier is solvable. -/
theorem isSolvable_binary_psl_normalizer {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    Group.IsSolvable
      (normalizer (S : Set (ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))) := by
  exact isSolvable_projective_sylow_normalizer n (ZMod 2) (by omega) S

end Theory.SpecificGroups.LinearSylowNormalizers
