module
public import Theory.GroupTheory.TwoFixedLinesIrreducible

/-!
# Fixed cubic lines in normal nine-groups

A three-group acting nontrivially on a normal subgroup of order nine has
exactly three fixed points. The p-group fixed-point theorem makes the fixed
subgroup nontrivial, and nontrivial action makes it proper. Its order is
therefore the sole intermediate three-power.

This is the fixed-line step in the elementary-nine enlargement of
Aschbacher–Smith, 14.5.20, printed p.1019, refs/quasithin.pdf. The actual
local application is SourceConstruction.LocalReduction.SolvableNinePoint.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]

/-- A nontrivial three-group action on a normal nine-group has a cubic fixed subgroup. -/
theorem normal_nine_fixed_line_card (P X : Subgroup D) [X.Normal]
    (hP : IsPGroup 3 P) (hX : IsPGroup 3 X) (h9 : Nat.card X = 9)
    (hmove : ¬ P ≤ centralizer (X : Set D)) :
    Nat.card (X ⊓ centralizer (P : Set D) : Subgroup D) = 3 := by
  let C := X ⊓ centralizer (P : Set D)
  have hXne : X ≠ ⊥ := by
    intro he
    rw [he,card_bot] at h9
    omega
  have hne : C ≠ ⊥ :=
    inf_centralizer_ne_bot_of_pGroups P X hP hX le_normalizer_of_normal hXne
  have hlt : C < X := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hmove (le_centralizer_iff.mp (he ▸ (inf_le_right : C ≤ centralizer (P : Set D)))))
  have hc : Nat.card C < 9 := by
    rw [←h9]
    exact lt_of_not_ge (fun hh => hlt.ne (eq_of_le_of_card_ge hlt.le hh))
  obtain ⟨n,hn⟩ := (hX.to_le (inf_le_left : C ≤ X)).exists_card_eq
  change Nat.card C = 3 ^ n at hn
  have hnlt : n < 2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp
    (show 3^n < 3^2 by simpa only [hn] using hc)
  have hn0 : n ≠ 0 := by
    intro hz
    exact hne (card_eq_one.mp (by simpa only [hz,pow_zero] using hn))
  have hn1 : n = 1 := by omega
  simpa only [hn1,pow_one] using hn

end Subgroup
