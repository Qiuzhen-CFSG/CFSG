module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Special and projective linear groups in odd binary degree

The scalar center of SL₃(q) has order gcd(3,q−1). For q = 2ⁿ with n odd,
this is one, so the canonical map SL₃(q) → PSL₃(q) is an isomorphism.
The explicit quotient-map identity allows transport to the natural module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the model
restriction in the proof of 13.8.20(a), printed p.954 (PDF p.971).
-/

public section

open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.OddDegreeProjectiveComparison
variable {F : Type*} [Field F] [Finite F]

theorem center_eq_bot {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Odd n) :
    center SL(3,F) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin, hF]
  exact (Nat.BinaryTorusParity.coprime_three_sub_one hn).gcd_eq_one

noncomputable def specialProjectiveEquiv {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Odd n) : SL(3,F) ≃* PSL(3,F) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (center SL(3,F)))
    ⟨(QuotientGroup.mk' (center SL(3,F))).ker_eq_bot_iff.mp (by
      rw [QuotientGroup.ker_mk', center_eq_bot hF hn]),
      QuotientGroup.mk'_surjective _⟩

@[simp] theorem specialProjectiveEquiv_apply {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Odd n) (g : SL(3,F)) :
    specialProjectiveEquiv hF hn g = QuotientGroup.mk g := by
  rfl

end Matrix.PSL3.OddDegreeProjectiveComparison

end
