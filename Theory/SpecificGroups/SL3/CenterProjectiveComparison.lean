module

public import Theory.SpecificGroups.PSL3.ProjectionKernel

/-!+# The center of SL₃ and its actual projective quotient

The scalar-center formula gives `|Z(SL₃(F))| = gcd(3, |F| - 1)`. Thus the
center has odd order, and is trivial precisely when `|F|` is not `1 mod 3`.
When the center is trivial, the actual projection to `PSL₃(F)` is a
multiplicative equivalence; its displayed equation identifies the quotient
map, rather than merely asserting an abstract model comparison.

These facts separate the odd-center and projective cases of the degree-three
linear alternatives in Aschbacher–Smith, *The Classification of Quasithin
Groups*, F.6.18(10)–(11), printed pp.309–310, used in 15.4.18, pp.1162–1163.
The scalar-center count is reused from the attributed ATLAS port imported
by `Theory.SpecificGroups.PSL3.ProjectionKernel`.
-/

open scoped MatrixGroups
open Subgroup

namespace Matrix.SL3
variable (F : Type*) [Field F]

/-- When its center is trivial, the natural SL₃-to-PSL₃ projection is an
isomorphism of the actual carriers. -/
public noncomputable def equivProjectiveOfCenterEqBot
    (hZ : center SL(3, F) = ⊥) : SL(3, F) ≃* PSL(3, F) :=
  MulEquiv.ofBijective (PSL3.projection F) ⟨by
    apply (PSL3.projection F).ker_eq_bot_iff.mp
    rw [PSL3.projection_ker, hZ], PSL3.projection_surjective F⟩

/-- The comparison is induced by the canonical quotient projection. -/
@[simp] public theorem equivProjectiveOfCenterEqBot_apply
    (hZ : center SL(3, F) = ⊥) (x : SL(3, F)) :
    equivProjectiveOfCenterEqBot F hZ x = PSL3.projection F x := (rfl)

variable [Finite F]

/-- The scalar center in degree three has order dividing three. -/
public theorem card_center_dvd_three : Nat.card (center SL(3, F)) ∣ 3 := by
  rw [Atlas.ExceptionalSupport.card_sl_center]
  exact Nat.gcd_dvd_left 3 _

/-- The degree-three scalar center always has odd order. -/
public theorem odd_card_center : Odd (Nat.card (center SL(3, F))) :=
  Odd.of_dvd_nat (by decide : Odd 3) (card_center_dvd_three F)

/-- The exact trivial-center criterion for a finite coefficient field. -/
public theorem center_eq_bot_iff_card_mod_three :
    center SL(3, F) = ⊥ ↔ Nat.card F % 3 ≠ 1 := by
  rw [← Subgroup.card_eq_one, Atlas.ExceptionalSupport.card_sl_center]
  change Nat.gcd 3 (Nat.card F - 1) = 1 ↔ Nat.card F % 3 ≠ 1
  have hpos : 0 < Nat.card F := Nat.card_pos
  constructor
  · intro hg hm
    have hd : 3 ∣ Nat.card F - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hh := Nat.dvd_gcd (dvd_refl 3) hd
    rw [hg] at hh
    norm_num at hh
  · intro hm
    apply Nat.Coprime.gcd_eq_one
    apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
    intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega

/-- Every nontrivial degree-three scalar center has order exactly three. -/
public theorem card_center_eq_three_of_ne_bot (hZ : center SL(3, F) ≠ ⊥) :
    Nat.card (center SL(3, F)) = 3 := by
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (card_center_dvd_three F) with h | h
  · exact (hZ (Subgroup.card_eq_one.mp h)).elim
  · exact h

end Matrix.SL3
