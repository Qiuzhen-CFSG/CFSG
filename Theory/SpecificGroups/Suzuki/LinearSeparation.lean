module

public import BenderSuzuki.Converse.PSL2
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Separating Suzuki groups from binary projective linear groups

The matrix `!![0,1;1,1]` has order three in SL₂ in characteristic two.
The central quotient is injective in this characteristic, so three divides
the order of PSL₂. Positive-parameter Suzuki groups have order prime to
three, excluding an isomorphism for any pair of field parameters.

This supplies the actual-model distinction used in GLS4, Chapter 2,
Lemmas 12.4 and 12.10. The Suzuki order formula is Huppert--Blackburn III,
XI.3.3. The order-three matrix argument also occurs in
`Theory/SpecificGroups/PSL3Even/ResidualComparison.lean` for the derived
subgroup; here only the full group and narrow model imports are needed.
-/

namespace BenderSuzuki.MatrixGroups

/-- PSL₂ in characteristic two contains an element of order three. -/
public theorem three_dvd_card_psl2_char_two
    (F : Type*) [Field F] [Finite F] [CharP F 2] :
    3 ∣ Nat.card (PSL2MatrixGroup F) := by
  let c : Converse.SL2 F :=
    ⟨!![0,1;1,1], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩
  have hpow : c ^ 3 = 1 := by
    apply Subtype.ext
    change ((!![0,1;1,1] : Matrix (Fin 2) (Fin 2) F) ^ 3) = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hne : c ≠ 1 := by
    intro h
    have he := congrArg (fun a : Converse.SL2 F => a.val 0 0) h
    simp [c] at he
  have horder : orderOf (Converse.pi F c) = 3 :=
    (orderOf_injective (Converse.pi F) Converse.pi_injective c).trans
      (orderOf_eq_prime hpow hne)
  exact horder ▸ orderOf_dvd_natCard (Converse.pi F c)

/-- No positive-parameter Suzuki group is isomorphic to a PSL₂ group in
characteristic two, independently of the two field orders. -/
public theorem not_nonempty_psl2_char_two_equiv_suzuki
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) :
    ¬ Nonempty (PSL2MatrixGroup F ≃* SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  apply suzukiMatrixGroup_three_free m hm
  rw [← Nat.card_congr e.toEquiv]
  exact three_dvd_card_psl2_char_two F

end BenderSuzuki.MatrixGroups
