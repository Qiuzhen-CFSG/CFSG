module

public import Theory.GroupAction.C4SquareAutomorphismOrder
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic

/-!
# Self-centralizing C₄-square extensions

Conjugation embeds the quotient by a normal self-centralizing abelian subgroup
in its automorphism group. For a C₄-square, the quotient order divides 96;
in a two-group with index greater than four it is therefore 8, 16, or 32.
The total group order is respectively 128, 256, or 512.

These intrinsic bounds reduce the recognition problem in Janko–Thompson,
Math. Z. 113 (1970), 1.4(c), printed p.386, to three finite extension orders.
They do not select the exotic extension or use an ambient classification.
-/

namespace Subgroup

/-- Conjugation on a normal self-centralizing abelian subgroup has that subgroup as kernel. -/
public theorem conjNormal_ker_eq_of_selfCentralizing_abelian
    {P : Type*} [Group P] (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) :
    (MulAut.conjNormal : P →* MulAut D).ker = D := by
  apply le_antisymm
  · intro x hx
    apply hDC
    intro d hd
    have hh := congrArg (fun f : MulAut D => (f ⟨d, hd⟩ : P))
      (MonoidHom.mem_ker.mp hx)
    change x * d * x⁻¹ = d at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro x hx
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    change x * (d : P) * x⁻¹ = d
    rw [(D.le_centralizer hx d d.property).symm, mul_inv_cancel_right]

/-- A self-centralizing normal C₄-square has index dividing 96. -/
public theorem index_dvd_ninety_six_of_selfCentralizing_c4_square
    {P : Type*} [Group P] (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (model : Nonempty (D ≃* C4SquareExtension.Model)) : D.index ∣ 96 := by
  have hh := C4SquareExtension.aut_subgroup_card_dvd model
    (MulAut.conjNormal : P →* MulAut D).range
  rwa [← index_ker, conjNormal_ker_eq_of_selfCentralizing_abelian D hDC] at hh

/-- In a finite two-group, index greater than four leaves just 8, 16, or 32. -/
public theorem index_cases_of_selfCentralizing_c4_square
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (model : Nonempty (D ≃* C4SquareExtension.Model)) (hlt : 4 < D.index) :
    D.index = 8 ∨ D.index = 16 ∨ D.index = 32 := by
  have hdiv := index_dvd_ninety_six_of_selfCentralizing_c4_square D hDC model
  obtain ⟨n, hn⟩ := (hP.to_quotient D).exists_card_eq
  change D.index = 2 ^ n at hn
  have hnle : n ≤ 5 := by
    by_contra hnot
    have hbad : 64 ∣ 96 := (Nat.pow_dvd_pow 2 (show 6 ≤ n by omega)).trans (hn ▸ hdiv)
    norm_num at hbad
  rw [hn] at hlt ⊢
  interval_cases n <;> norm_num at *

/-- The corresponding extension orders are 128, 256, and 512. -/
public theorem card_cases_of_selfCentralizing_c4_square
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (model : Nonempty (D ≃* C4SquareExtension.Model)) (hlt : 4 < D.index) :
    Nat.card P = 128 ∨ Nat.card P = 256 ∨ Nat.card P = 512 := by
  have hc : Nat.card D = 16 := by
    obtain ⟨e⟩ := model
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hh := D.card_mul_index
  rw [hc] at hh
  rcases index_cases_of_selfCentralizing_c4_square hP D hDC model hlt with h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))
end Subgroup
